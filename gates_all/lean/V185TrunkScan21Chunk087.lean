import V185TrunkScan21Chunk086

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1056417 : List Nat := [1, 2, 3, 3, 2, 3, 1, 2, 4]
def baseStart_1056417 : Nat := 118140960795 + 1056417 * 2 ^ 59
def prefixEnd_1056417 : Nat := 4983230072969 + 3 ^ 40 * 1056417 * 2
def baseEnd_1056417 : Nat := 241088752258177109924059

theorem tailTrace_1056417 : CollatzResearch.WordTrace tailWord_1056417 prefixEnd_1056417 241088752258177109924059 := by
  unfold tailWord_1056417
  simp only [CollatzResearch.WordTrace]
  refine ⟨38530693413789105504607505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25687128942526070336405003 38530693413789105504607505)
  ·
    refine ⟨28898020060341829128455629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38530693413789105504607505 28898020060341829128455629)
    ·
      refine ⟨10836757522628185923170861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28898020060341829128455629 10836757522628185923170861)
      ·
        refine ⟨4063784070985569721189073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10836757522628185923170861 4063784070985569721189073)
        ·
          refine ⟨3047838053239177290891805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4063784070985569721189073 3047838053239177290891805)
          ·
            refine ⟨1142939269964691484084427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3047838053239177290891805 1142939269964691484084427)
            ·
              refine ⟨1714408904947037226126641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142939269964691484084427 1714408904947037226126641)
              ·
                refine ⟨1285806678710277919594981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1714408904947037226126641 1285806678710277919594981)
                ·
                  refine ⟨241088752258177109924059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285806678710277919594981 241088752258177109924059)
                  ·
                    rfl

theorem cell21_1056417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_1056417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056417 prefixEnd_1056417 := by exact prefixLift 1056417
  have htrace : WordTrace (prefixWord ++ tailWord_1056417) baseStart_1056417 baseEnd_1056417 := by
    simpa [prefixWord, tailWord_1056417, baseEnd_1056417] using wordTrace_append hprefix tailTrace_1056417
  have hstable : (prefixWord ++ tailWord_1056417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056417).length < 2 ^ (prefixWord ++ tailWord_1056417).sum := by decide
  have hdescent : baseEnd_1056417 < baseStart_1056417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056473 : List Nat := [1, 2, 1, 2, 3, 3, 9]
def baseStart_1056473 : Nat := 118140960795 + 1056473 * 2 ^ 59
def prefixEnd_1056473 : Nat := 4983230072969 + 3 ^ 40 * 1056473 * 2
def baseEnd_1056473 : Nat := 26789059135681495221179

theorem tailTrace_1056473 : CollatzResearch.WordTrace tailWord_1056473 prefixEnd_1056473 26789059135681495221179 := by
  unfold tailWord_1056473
  simp only [CollatzResearch.WordTrace]
  refine ⟨38532735901586227068646073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25688490601057484712430715 38532735901586227068646073)
  ·
    refine ⟨28899551926189670301484555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38532735901586227068646073 28899551926189670301484555)
    ·
      refine ⟨43349327889284505452226833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28899551926189670301484555 43349327889284505452226833)
      ·
        refine ⟨32511995916963379089170125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43349327889284505452226833 32511995916963379089170125)
        ·
          refine ⟨12191998468861267158438797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32511995916963379089170125 12191998468861267158438797)
          ·
            refine ⟨4571999425822975184414549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12191998468861267158438797 4571999425822975184414549)
            ·
              refine ⟨26789059135681495221179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4571999425822975184414549 26789059135681495221179)
              ·
                rfl

theorem cell21_1056473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 9].length) (baseStart_1056473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056473 prefixEnd_1056473 := by exact prefixLift 1056473
  have htrace : WordTrace (prefixWord ++ tailWord_1056473) baseStart_1056473 baseEnd_1056473 := by
    simpa [prefixWord, tailWord_1056473, baseEnd_1056473] using wordTrace_append hprefix tailTrace_1056473
  have hstable : (prefixWord ++ tailWord_1056473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056473).length < 2 ^ (prefixWord ++ tailWord_1056473).sum := by decide
  have hdescent : baseEnd_1056473 < baseStart_1056473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056493 : List Nat := [1, 5, 1, 2, 1, 2, 4, 1, 4]
def baseStart_1056493 : Nat := 118140960795 + 1056493 * 2 ^ 59
def prefixEnd_1056493 : Nat := 4983230072969 + 3 ^ 40 * 1056493 * 2
def baseEnd_1056493 : Nat := 241106096493617866657237

theorem tailTrace_1056493 : CollatzResearch.WordTrace tailWord_1056493 prefixEnd_1056493 241106096493617866657237 := by
  unfold tailWord_1056493
  simp only [CollatzResearch.WordTrace]
  refine ⟨38533465361513770484374133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25688976907675846989582755 38533465361513770484374133)
  ·
    refine ⟨3612512377641915982910075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38533465361513770484374133 3612512377641915982910075)
    ·
      refine ⟨5418768566462873974365113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3612512377641915982910075 5418768566462873974365113)
      ·
        refine ⟨4064076424847155480773835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5418768566462873974365113 4064076424847155480773835)
        ·
          refine ⟨6096114637270733221160753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4064076424847155480773835 6096114637270733221160753)
          ·
            refine ⟨4572085977953049915870565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6096114637270733221160753 4572085977953049915870565)
            ·
              refine ⟨857266120866196859225731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4572085977953049915870565 857266120866196859225731)
              ·
                refine ⟨1285899181299295288838597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857266120866196859225731 1285899181299295288838597)
                ·
                  refine ⟨241106096493617866657237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285899181299295288838597 241106096493617866657237)
                  ·
                    rfl

theorem cell21_1056493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_1056493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056493 prefixEnd_1056493 := by exact prefixLift 1056493
  have htrace : WordTrace (prefixWord ++ tailWord_1056493) baseStart_1056493 baseEnd_1056493 := by
    simpa [prefixWord, tailWord_1056493, baseEnd_1056493] using wordTrace_append hprefix tailTrace_1056493
  have hstable : (prefixWord ++ tailWord_1056493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056493).length < 2 ^ (prefixWord ++ tailWord_1056493).sum := by decide
  have hdescent : baseEnd_1056493 < baseStart_1056493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056521 : List Nat := [1, 2, 1, 1, 3, 2, 1, 7, 3]
def baseStart_1056521 : Nat := 118140960795 + 1056521 * 2 ^ 59
def prefixEnd_1056521 : Nat := 4983230072969 + 3 ^ 40 * 1056521 * 2
def baseEnd_1056521 : Nat := 241112486475096040190513

theorem tailTrace_1056521 : CollatzResearch.WordTrace tailWord_1056521 prefixEnd_1056521 241112486475096040190513 := by
  unfold tailWord_1056521
  simp only [CollatzResearch.WordTrace]
  refine ⟨38534486605412331266393417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25689657736941554177595611 38534486605412331266393417)
  ·
    refine ⟨28900864954059248449795063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38534486605412331266393417 28900864954059248449795063)
    ·
      refine ⟨43351297431088872674692595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28900864954059248449795063 43351297431088872674692595)
      ·
        refine ⟨65026946146633309012038893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43351297431088872674692595 65026946146633309012038893)
        ·
          refine ⟨24385104804987490879514585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65026946146633309012038893 24385104804987490879514585)
          ·
            refine ⟨18288828603740618159635939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24385104804987490879514585 18288828603740618159635939)
            ·
              refine ⟨27433242905610927239453909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18288828603740618159635939 27433242905610927239453909)
              ·
                refine ⟨642966630600256107174701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27433242905610927239453909 642966630600256107174701)
                ·
                  refine ⟨241112486475096040190513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642966630600256107174701 241112486475096040190513)
                  ·
                    rfl

theorem cell21_1056521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 3].length) (baseStart_1056521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056521 prefixEnd_1056521 := by exact prefixLift 1056521
  have htrace : WordTrace (prefixWord ++ tailWord_1056521) baseStart_1056521 baseEnd_1056521 := by
    simpa [prefixWord, tailWord_1056521, baseEnd_1056521] using wordTrace_append hprefix tailTrace_1056521
  have hstable : (prefixWord ++ tailWord_1056521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056521).length < 2 ^ (prefixWord ++ tailWord_1056521).sum := by decide
  have hdescent : baseEnd_1056521 < baseStart_1056521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056538 : List Nat := [3, 1, 1, 3, 2, 3, 1, 4, 3]
def baseStart_1056538 : Nat := 118140960795 + 1056538 * 2 ^ 59
def prefixEnd_1056538 : Nat := 4983230072969 + 3 ^ 40 * 1056538 * 2
def baseEnd_1056538 : Nat := 241116366106707788407145

theorem tailTrace_1056538 : CollatzResearch.WordTrace tailWord_1056538 prefixEnd_1056538 241116366106707788407145 := by
  unfold tailWord_1056538
  simp only [CollatzResearch.WordTrace]
  refine ⟨9633776661587685792440567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25690071097567162113174845 9633776661587685792440567)
  ·
    refine ⟨14450664992381528688660851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9633776661587685792440567 14450664992381528688660851)
    ·
      refine ⟨21675997488572293032991277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14450664992381528688660851 21675997488572293032991277)
      ·
        refine ⟨8128499058214609887371729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21675997488572293032991277 8128499058214609887371729)
        ·
          refine ⟨6096374293660957415528797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8128499058214609887371729 6096374293660957415528797)
          ·
            refine ⟨2286140360122859030823299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6096374293660957415528797 2286140360122859030823299)
            ·
              refine ⟨3429210540184288546234949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2286140360122859030823299 3429210540184288546234949)
              ·
                refine ⟨642976976284554102419053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3429210540184288546234949 642976976284554102419053)
                ·
                  refine ⟨241116366106707788407145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642976976284554102419053 241116366106707788407145)
                  ·
                    rfl

theorem cell21_1056538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_1056538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056538 prefixEnd_1056538 := by exact prefixLift 1056538
  have htrace : WordTrace (prefixWord ++ tailWord_1056538) baseStart_1056538 baseEnd_1056538 := by
    simpa [prefixWord, tailWord_1056538, baseEnd_1056538] using wordTrace_append hprefix tailTrace_1056538
  have hstable : (prefixWord ++ tailWord_1056538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056538).length < 2 ^ (prefixWord ++ tailWord_1056538).sum := by decide
  have hdescent : baseEnd_1056538 < baseStart_1056538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056552 : List Nat := [2, 1, 5, 1, 1, 2, 2, 3, 4]
def baseStart_1056552 : Nat := 118140960795 + 1056552 * 2 ^ 59
def prefixEnd_1056552 : Nat := 4983230072969 + 3 ^ 40 * 1056552 * 2
def baseEnd_1056552 : Nat := 241119561097446875173783

theorem tailTrace_1056552 : CollatzResearch.WordTrace tailWord_1056552 prefixEnd_1056552 241119561097446875173783 := by
  unfold tailWord_1056552
  simp only [CollatzResearch.WordTrace]
  refine ⟨19267808634150011780385955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25690411512200015707181273 19267808634150011780385955)
  ·
    refine ⟨28901712951225017670578933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19267808634150011780385955 28901712951225017670578933)
    ·
      refine ⟨2709535589177345406616775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28901712951225017670578933 2709535589177345406616775)
      ·
        refine ⟨4064303383766018109925163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2709535589177345406616775 4064303383766018109925163)
        ·
          refine ⟨6096455075649027164887745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4064303383766018109925163 6096455075649027164887745)
          ·
            refine ⟨4572341306736770373665809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6096455075649027164887745 4572341306736770373665809)
            ·
              refine ⟨3429255980052577780249357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4572341306736770373665809 3429255980052577780249357)
              ·
                refine ⟨1285970992519716667593509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3429255980052577780249357 1285970992519716667593509)
                ·
                  refine ⟨241119561097446875173783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285970992519716667593509 241119561097446875173783)
                  ·
                    rfl

theorem cell21_1056552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_1056552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056552 prefixEnd_1056552 := by exact prefixLift 1056552
  have htrace : WordTrace (prefixWord ++ tailWord_1056552) baseStart_1056552 baseEnd_1056552 := by
    simpa [prefixWord, tailWord_1056552, baseEnd_1056552] using wordTrace_append hprefix tailTrace_1056552
  have hstable : (prefixWord ++ tailWord_1056552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056552).length < 2 ^ (prefixWord ++ tailWord_1056552).sum := by decide
  have hdescent : baseEnd_1056552 < baseStart_1056552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056597 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 5]
def baseStart_1056597 : Nat := 118140960795 + 1056597 * 2 ^ 59
def prefixEnd_1056597 : Nat := 4983230072969 + 3 ^ 40 * 1056597 * 2
def baseEnd_1056597 : Nat := 241129830710536796923691

theorem tailTrace_1056597 : CollatzResearch.WordTrace tailWord_1056597 prefixEnd_1056597 241129830710536796923691 := by
  unfold tailWord_1056597
  simp only [CollatzResearch.WordTrace]
  refine ⟨38537258553136996246160045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25691505702091330830773363 38537258553136996246160045)
  ·
    refine ⟨14451471957426373592310017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38537258553136996246160045 14451471957426373592310017)
    ·
      refine ⟨10838603968069780194232513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14451471957426373592310017 10838603968069780194232513)
      ·
        refine ⟨8128952976052335145674385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10838603968069780194232513 8128952976052335145674385)
        ·
          refine ⟨6096714732039251359255789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8128952976052335145674385 6096714732039251359255789)
          ·
            refine ⟨2286268024514719259720921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6096714732039251359255789 2286268024514719259720921)
            ·
              refine ⟨1714701018386039444790691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2286268024514719259720921 1714701018386039444790691)
              ·
                refine ⟨2572051527579059167186037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1714701018386039444790691 2572051527579059167186037)
                ·
                  refine ⟨241129830710536796923691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2572051527579059167186037 241129830710536796923691)
                  ·
                    rfl

theorem cell21_1056597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_1056597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056597 prefixEnd_1056597 := by exact prefixLift 1056597
  have htrace : WordTrace (prefixWord ++ tailWord_1056597) baseStart_1056597 baseEnd_1056597 := by
    simpa [prefixWord, tailWord_1056597, baseEnd_1056597] using wordTrace_append hprefix tailTrace_1056597
  have hstable : (prefixWord ++ tailWord_1056597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056597).length < 2 ^ (prefixWord ++ tailWord_1056597).sum := by decide
  have hdescent : baseEnd_1056597 < baseStart_1056597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056625 : List Nat := [1, 2, 2, 2, 1, 3, 3, 7]
def baseStart_1056625 : Nat := 118140960795 + 1056625 * 2 ^ 59
def prefixEnd_1056625 : Nat := 4983230072969 + 3 ^ 40 * 1056625 * 2
def baseEnd_1056625 : Nat := 80378740230671656818989

theorem tailTrace_1056625 : CollatzResearch.WordTrace tailWord_1056625 prefixEnd_1056625 80378740230671656818989 := by
  unfold tailWord_1056625
  simp only [CollatzResearch.WordTrace]
  refine ⟨38538279797035557028179329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25692186531357038018786219 38538279797035557028179329)
  ·
    refine ⟨28903709847776667771134497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38538279797035557028179329 28903709847776667771134497)
    ·
      refine ⟨21677782385832500828350873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28903709847776667771134497 21677782385832500828350873)
      ·
        refine ⟨16258336789374375621263155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21677782385832500828350873 16258336789374375621263155)
        ·
          refine ⟨24387505184061563431894733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16258336789374375621263155 24387505184061563431894733)
          ·
            refine ⟨9145314444023086286960525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24387505184061563431894733 9145314444023086286960525)
            ·
              refine ⟨3429492916508657357610197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9145314444023086286960525 3429492916508657357610197)
              ·
                refine ⟨80378740230671656818989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3429492916508657357610197 80378740230671656818989)
                ·
                  rfl

theorem cell21_1056625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 7].length) (baseStart_1056625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056625 prefixEnd_1056625 := by exact prefixLift 1056625
  have htrace : WordTrace (prefixWord ++ tailWord_1056625) baseStart_1056625 baseEnd_1056625 := by
    simpa [prefixWord, tailWord_1056625, baseEnd_1056625] using wordTrace_append hprefix tailTrace_1056625
  have hstable : (prefixWord ++ tailWord_1056625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056625).length < 2 ^ (prefixWord ++ tailWord_1056625).sum := by decide
  have hdescent : baseEnd_1056625 < baseStart_1056625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056701 : List Nat := [1, 4, 1, 2, 3, 10]
def baseStart_1056701 : Nat := 118140960795 + 1056701 * 2 ^ 59
def prefixEnd_1056701 : Nat := 4983230072969 + 3 ^ 40 * 1056701 * 2
def baseEnd_1056701 : Nat := 8931613515831693599635

theorem tailTrace_1056701 : CollatzResearch.WordTrace tailWord_1056701 prefixEnd_1056701 8931613515831693599635 := by
  unfold tailWord_1056701
  simp only [CollatzResearch.WordTrace]
  refine ⟨38541051744760222007945957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25694034496506814671963971 38541051744760222007945957)
  ·
    refine ⟨7226447202142541626489867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38541051744760222007945957 7226447202142541626489867)
    ·
      refine ⟨10839670803213812439734801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7226447202142541626489867 10839670803213812439734801)
      ·
        refine ⟨8129753102410359329801101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10839670803213812439734801 8129753102410359329801101)
        ·
          refine ⟨3048657413403884748675413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8129753102410359329801101 3048657413403884748675413)
          ·
            refine ⟨8931613515831693599635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3048657413403884748675413 8931613515831693599635)
            ·
              rfl

theorem cell21_1056701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 10].length) (baseStart_1056701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056701 prefixEnd_1056701 := by exact prefixLift 1056701
  have htrace : WordTrace (prefixWord ++ tailWord_1056701) baseStart_1056701 baseEnd_1056701 := by
    simpa [prefixWord, tailWord_1056701, baseEnd_1056701] using wordTrace_append hprefix tailTrace_1056701
  have hstable : (prefixWord ++ tailWord_1056701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056701).length < 2 ^ (prefixWord ++ tailWord_1056701).sum := by decide
  have hdescent : baseEnd_1056701 < baseStart_1056701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056763 : List Nat := [1, 1, 1, 1, 1, 3, 7, 2, 4]
def baseStart_1056763 : Nat := 118140960795 + 1056763 * 2 ^ 59
def prefixEnd_1056763 : Nat := 4983230072969 + 3 ^ 40 * 1056763 * 2
def baseEnd_1056763 : Nat := 241167714172157397156685

theorem tailTrace_1056763 : CollatzResearch.WordTrace tailWord_1056763 prefixEnd_1056763 241167714172157397156685 := by
  unfold tailWord_1056763
  simp only [CollatzResearch.WordTrace]
  refine ⟨38543313070535606596702943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25695542047023737731135295 38543313070535606596702943)
  ·
    refine ⟨57814969605803409895054415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38543313070535606596702943 57814969605803409895054415)
    ·
      refine ⟨86722454408705114842581623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57814969605803409895054415 86722454408705114842581623)
      ·
        refine ⟨130083681613057672263872435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86722454408705114842581623 130083681613057672263872435)
        ·
          refine ⟨195125522419586508395808653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130083681613057672263872435 195125522419586508395808653)
          ·
            refine ⟨73172070907344940648428245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195125522419586508395808653 73172070907344940648428245)
            ·
              refine ⟨1714970411890897046447537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 73172070907344940648428245 1714970411890897046447537)
              ·
                refine ⟨1286227808918172784835653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1714970411890897046447537 1286227808918172784835653)
                ·
                  refine ⟨241167714172157397156685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1286227808918172784835653 241167714172157397156685)
                  ·
                    rfl

theorem cell21_1056763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 4].length) (baseStart_1056763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056763 prefixEnd_1056763 := by exact prefixLift 1056763
  have htrace : WordTrace (prefixWord ++ tailWord_1056763) baseStart_1056763 baseEnd_1056763 := by
    simpa [prefixWord, tailWord_1056763, baseEnd_1056763] using wordTrace_append hprefix tailTrace_1056763
  have hstable : (prefixWord ++ tailWord_1056763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056763).length < 2 ^ (prefixWord ++ tailWord_1056763).sum := by decide
  have hdescent : baseEnd_1056763 < baseStart_1056763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056766 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_1056766 : Nat := 118140960795 + 1056766 * 2 ^ 59
def prefixEnd_1056766 : Nat := 4983230072969 + 3 ^ 40 * 1056766 * 2
def baseEnd_1056766 : Nat := 241168398813030058606679

theorem tailTrace_1056766 : CollatzResearch.WordTrace tailWord_1056766 prefixEnd_1056766 241168398813030058606679 := by
  unfold tailWord_1056766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4817927811190592263632769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25695614993016492072708101 4817927811190592263632769)
  ·
    refine ⟨3613445858392944197724577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4817927811190592263632769 3613445858392944197724577)
    ·
      refine ⟨2710084393794708148293433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3613445858392944197724577 2710084393794708148293433)
      ·
        refine ⟨2032563295346031111220075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2710084393794708148293433 2032563295346031111220075)
        ·
          refine ⟨3048844943019046666830113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2032563295346031111220075 3048844943019046666830113)
          ·
            refine ⟨2286633707264285000122585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3048844943019046666830113 2286633707264285000122585)
            ·
              refine ⟨1714975280448213750091939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2286633707264285000122585 1714975280448213750091939)
              ·
                refine ⟨2572462920672320625137909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1714975280448213750091939 2572462920672320625137909)
                ·
                  refine ⟨241168398813030058606679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2572462920672320625137909 241168398813030058606679)
                  ·
                    rfl

theorem cell21_1056766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_1056766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056766 prefixEnd_1056766 := by exact prefixLift 1056766
  have htrace : WordTrace (prefixWord ++ tailWord_1056766) baseStart_1056766 baseEnd_1056766 := by
    simpa [prefixWord, tailWord_1056766, baseEnd_1056766] using wordTrace_append hprefix tailTrace_1056766
  have hstable : (prefixWord ++ tailWord_1056766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056766).length < 2 ^ (prefixWord ++ tailWord_1056766).sum := by decide
  have hdescent : baseEnd_1056766 < baseStart_1056766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056780 : List Nat := [2, 2, 1, 2, 3, 1, 5, 1, 4]
def baseStart_1056780 : Nat := 118140960795 + 1056780 * 2 ^ 59
def prefixEnd_1056780 : Nat := 4983230072969 + 3 ^ 40 * 1056780 * 2
def baseEnd_1056780 : Nat := 241171593803769145373317

theorem tailTrace_1056780 : CollatzResearch.WordTrace tailWord_1056780 prefixEnd_1056780 241171593803769145373317 := by
  unfold tailWord_1056780
  simp only [CollatzResearch.WordTrace]
  refine ⟨19271966555737009250035897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25695955407649345666714529 19271966555737009250035897)
  ·
    refine ⟨14453974916802756937526923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19271966555737009250035897 14453974916802756937526923)
    ·
      refine ⟨21680962375204135406290385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14453974916802756937526923 21680962375204135406290385)
      ·
        refine ⟨16260721781403101554717789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21680962375204135406290385 16260721781403101554717789)
        ·
          refine ⟨6097770668026163083019171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16260721781403101554717789 6097770668026163083019171)
          ·
            refine ⟨9146656002039244624528757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6097770668026163083019171 9146656002039244624528757)
            ·
              refine ⟨857499000191179183549571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9146656002039244624528757 857499000191179183549571)
              ·
                refine ⟨1286248500286768775324357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857499000191179183549571 1286248500286768775324357)
                ·
                  refine ⟨241171593803769145373317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1286248500286768775324357 241171593803769145373317)
                  ·
                    rfl

theorem cell21_1056780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_1056780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056780 prefixEnd_1056780 := by exact prefixLift 1056780
  have htrace : WordTrace (prefixWord ++ tailWord_1056780) baseStart_1056780 baseEnd_1056780 := by
    simpa [prefixWord, tailWord_1056780, baseEnd_1056780] using wordTrace_append hprefix tailTrace_1056780
  have hstable : (prefixWord ++ tailWord_1056780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056780).length < 2 ^ (prefixWord ++ tailWord_1056780).sum := by decide
  have hdescent : baseEnd_1056780 < baseStart_1056780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056794 : List Nat := [3, 1, 1, 3, 1, 3, 4, 5]
def baseStart_1056794 : Nat := 118140960795 + 1056794 * 2 ^ 59
def prefixEnd_1056794 : Nat := 4983230072969 + 3 ^ 40 * 1056794 * 2
def baseEnd_1056794 : Nat := 80391596264836077379985

theorem tailTrace_1056794 : CollatzResearch.WordTrace tailWord_1056794 prefixEnd_1056794 80391596264836077379985 := by
  unfold tailWord_1056794
  simp only [CollatzResearch.WordTrace]
  refine ⟨9636110933355824722770359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25696295822282199260720957 9636110933355824722770359)
  ·
    refine ⟨14454166400033737084155539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9636110933355824722770359 14454166400033737084155539)
    ·
      refine ⟨21681249600050605626233309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14454166400033737084155539 21681249600050605626233309)
      ·
        refine ⟨8130468600018977109837491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21681249600050605626233309 8130468600018977109837491)
        ·
          refine ⟨12195702900028465664756237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8130468600018977109837491 12195702900028465664756237)
          ·
            refine ⟨4573388587510674624283589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12195702900028465664756237 4573388587510674624283589)
            ·
              refine ⟨857510360158251492053173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4573388587510674624283589 857510360158251492053173)
              ·
                refine ⟨80391596264836077379985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 857510360158251492053173 80391596264836077379985)
                ·
                  rfl

theorem cell21_1056794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_1056794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056794 prefixEnd_1056794 := by exact prefixLift 1056794
  have htrace : WordTrace (prefixWord ++ tailWord_1056794) baseStart_1056794 baseEnd_1056794 := by
    simpa [prefixWord, tailWord_1056794, baseEnd_1056794] using wordTrace_append hprefix tailTrace_1056794
  have hstable : (prefixWord ++ tailWord_1056794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056794).length < 2 ^ (prefixWord ++ tailWord_1056794).sum := by decide
  have hdescent : baseEnd_1056794 < baseStart_1056794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056839 : List Nat := [1, 1, 4, 1, 3, 1, 3, 3, 4]
def baseStart_1056839 : Nat := 118140960795 + 1056839 * 2 ^ 59
def prefixEnd_1056839 : Nat := 4983230072969 + 3 ^ 40 * 1056839 * 2
def baseEnd_1056839 : Nat := 241185058407598153889863

theorem tailTrace_1056839 : CollatzResearch.WordTrace tailWord_1056839 prefixEnd_1056839 241185058407598153889863 := by
  unfold tailWord_1056839
  simp only [CollatzResearch.WordTrace]
  refine ⟨38546085018260271576469571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25697390012173514384313047 38546085018260271576469571)
  ·
    refine ⟨57819127527390407364704357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38546085018260271576469571 57819127527390407364704357)
    ·
      refine ⟨10841086411385701380882067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57819127527390407364704357 10841086411385701380882067)
      ·
        refine ⟨16261629617078552071323101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10841086411385701380882067 16261629617078552071323101)
        ·
          refine ⟨6098111106404457026746163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16261629617078552071323101 6098111106404457026746163)
          ·
            refine ⟨9147166659606685540119245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6098111106404457026746163 9147166659606685540119245)
            ·
              refine ⟨3430187497352507077544717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9147166659606685540119245 3430187497352507077544717)
              ·
                refine ⟨1286320311507190154079269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3430187497352507077544717 1286320311507190154079269)
                ·
                  refine ⟨241185058407598153889863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1286320311507190154079269 241185058407598153889863)
                  ·
                    rfl

theorem cell21_1056839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 4].length) (baseStart_1056839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056839 prefixEnd_1056839 := by exact prefixLift 1056839
  have htrace : WordTrace (prefixWord ++ tailWord_1056839) baseStart_1056839 baseEnd_1056839 := by
    simpa [prefixWord, tailWord_1056839, baseEnd_1056839] using wordTrace_append hprefix tailTrace_1056839
  have hstable : (prefixWord ++ tailWord_1056839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056839).length < 2 ^ (prefixWord ++ tailWord_1056839).sum := by decide
  have hdescent : baseEnd_1056839 < baseStart_1056839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056853 : List Nat := [1, 3, 2, 2, 1, 3, 2, 7]
def baseStart_1056853 : Nat := 118140960795 + 1056853 * 2 ^ 59
def prefixEnd_1056853 : Nat := 4983230072969 + 3 ^ 40 * 1056853 * 2
def baseEnd_1056853 : Nat := 80396084466112413552167

theorem tailTrace_1056853 : CollatzResearch.WordTrace tailWord_1056853 prefixEnd_1056853 80396084466112413552167 := by
  unfold tailWord_1056853
  simp only [CollatzResearch.WordTrace]
  refine ⟨38546595640209551967479213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25697730426806367978319475 38546595640209551967479213)
  ·
    refine ⟨14454973365078581987804705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38546595640209551967479213 14454973365078581987804705)
    ·
      refine ⟨10841230023808936490853529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14454973365078581987804705 10841230023808936490853529)
      ·
        refine ⟨8130922517856702368140147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10841230023808936490853529 8130922517856702368140147)
        ·
          refine ⟨12196383776785053552210221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8130922517856702368140147 12196383776785053552210221)
          ·
            refine ⟨4573643916294395082078833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12196383776785053552210221 4573643916294395082078833)
            ·
              refine ⟨3430232937220796311559125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4573643916294395082078833 3430232937220796311559125)
              ·
                refine ⟨80396084466112413552167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3430232937220796311559125 80396084466112413552167)
                ·
                  rfl

theorem cell21_1056853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 7].length) (baseStart_1056853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056853 prefixEnd_1056853 := by exact prefixLift 1056853
  have htrace : WordTrace (prefixWord ++ tailWord_1056853) baseStart_1056853 baseEnd_1056853 := by
    simpa [prefixWord, tailWord_1056853, baseEnd_1056853] using wordTrace_append hprefix tailTrace_1056853
  have hstable : (prefixWord ++ tailWord_1056853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056853).length < 2 ^ (prefixWord ++ tailWord_1056853).sum := by decide
  have hdescent : baseEnd_1056853 < baseStart_1056853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056929 : List Nat := [1, 2, 3, 3, 1, 3, 8]
def baseStart_1056929 : Nat := 118140960795 + 1056929 * 2 ^ 59
def prefixEnd_1056929 : Nat := 4983230072969 + 3 ^ 40 * 1056929 * 2
def baseEnd_1056929 : Nat := 26800621959308666376631

theorem tailTrace_1056929 : CollatzResearch.WordTrace tailWord_1056929 prefixEnd_1056929 26800621959308666376631 := by
  unfold tailWord_1056929
  simp only [CollatzResearch.WordTrace]
  refine ⟨38549367587934216947245841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25699578391956144631497227 38549367587934216947245841)
  ·
    refine ⟨28912025690950662710434381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38549367587934216947245841 28912025690950662710434381)
    ·
      refine ⟨10842009634106498516412893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28912025690950662710434381 10842009634106498516412893)
      ·
        refine ⟨4065753612789936943654835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10842009634106498516412893 4065753612789936943654835)
        ·
          refine ⟨6098630419184905415482253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4065753612789936943654835 6098630419184905415482253)
          ·
            refine ⟨2286986407194339530805845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6098630419184905415482253 2286986407194339530805845)
            ·
              refine ⟨26800621959308666376631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2286986407194339530805845 26800621959308666376631)
              ·
                rfl

theorem cell21_1056929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 8].length) (baseStart_1056929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056929 prefixEnd_1056929 := by exact prefixLift 1056929
  have htrace : WordTrace (prefixWord ++ tailWord_1056929) baseStart_1056929 baseEnd_1056929 := by
    simpa [prefixWord, tailWord_1056929, baseEnd_1056929] using wordTrace_append hprefix tailTrace_1056929
  have hstable : (prefixWord ++ tailWord_1056929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056929).length < 2 ^ (prefixWord ++ tailWord_1056929).sum := by decide
  have hdescent : baseEnd_1056929 < baseStart_1056929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056960 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 5]
def baseStart_1056960 : Nat := 118140960795 + 1056960 * 2 ^ 59
def prefixEnd_1056960 : Nat := 4983230072969 + 3 ^ 40 * 1056960 * 2
def baseEnd_1056960 : Nat := 241212672256128832372949

theorem tailTrace_1056960 : CollatzResearch.WordTrace tailWord_1056960 prefixEnd_1056960 241212672256128832372949 := by
  unfold tailWord_1056960
  simp only [CollatzResearch.WordTrace]
  refine ⟨19275249125410954620812167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25700332167214606161082889 19275249125410954620812167)
  ·
    refine ⟨28912873688116431931218251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19275249125410954620812167 28912873688116431931218251)
    ·
      refine ⟨43369310532174647896827377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28912873688116431931218251 43369310532174647896827377)
      ·
        refine ⟨32526982899130985922620533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43369310532174647896827377 32526982899130985922620533)
        ·
          refine ⟨3049404646793529930245675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32526982899130985922620533 3049404646793529930245675)
          ·
            refine ⟨4574106970190294895368513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3049404646793529930245675 4574106970190294895368513)
            ·
              refine ⟨3430580227642721171526385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4574106970190294895368513 3430580227642721171526385)
              ·
                refine ⟨2572935170732040878644789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3430580227642721171526385 2572935170732040878644789)
                ·
                  refine ⟨241212672256128832372949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2572935170732040878644789 241212672256128832372949)
                  ·
                    rfl

theorem cell21_1056960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_1056960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056960 prefixEnd_1056960 := by exact prefixLift 1056960
  have htrace : WordTrace (prefixWord ++ tailWord_1056960) baseStart_1056960 baseEnd_1056960 := by
    simpa [prefixWord, tailWord_1056960, baseEnd_1056960] using wordTrace_append hprefix tailTrace_1056960
  have hstable : (prefixWord ++ tailWord_1056960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056960).length < 2 ^ (prefixWord ++ tailWord_1056960).sum := by decide
  have hdescent : baseEnd_1056960 < baseStart_1056960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056977 : List Nat := [1, 2, 2, 1, 2, 2, 5, 3, 3]
def baseStart_1056977 : Nat := 118140960795 + 1056977 * 2 ^ 59
def prefixEnd_1056977 : Nat := 4983230072969 + 3 ^ 40 * 1056977 * 2
def baseEnd_1056977 : Nat := 241216551887740580589581

theorem tailTrace_1056977 : CollatzResearch.WordTrace tailWord_1056977 prefixEnd_1056977 241216551887740580589581 := by
  unfold tailWord_1056977
  simp only [CollatzResearch.WordTrace]
  refine ⟨38551118291760321144993185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25700745527840214096662123 38551118291760321144993185)
  ·
    refine ⟨28913338718820240858744889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38551118291760321144993185 28913338718820240858744889)
    ·
      refine ⟨21685004039115180644058667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28913338718820240858744889 21685004039115180644058667)
      ·
        refine ⟨32527506058672770966088001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21685004039115180644058667 32527506058672770966088001)
        ·
          refine ⟨24395629544004578224566001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32527506058672770966088001 24395629544004578224566001)
          ·
            refine ⟨18296722158003433668424501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24395629544004578224566001 18296722158003433668424501)
            ·
              refine ⟨1715317702312821906414797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18296722158003433668424501 1715317702312821906414797)
              ·
                refine ⟨643244138367308214905549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1715317702312821906414797 643244138367308214905549)
                ·
                  refine ⟨241216551887740580589581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 643244138367308214905549 241216551887740580589581)
                  ·
                    rfl

theorem cell21_1056977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 3].length) (baseStart_1056977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056977 prefixEnd_1056977 := by exact prefixLift 1056977
  have htrace : WordTrace (prefixWord ++ tailWord_1056977) baseStart_1056977 baseEnd_1056977 := by
    simpa [prefixWord, tailWord_1056977, baseEnd_1056977] using wordTrace_append hprefix tailTrace_1056977
  have hstable : (prefixWord ++ tailWord_1056977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056977).length < 2 ^ (prefixWord ++ tailWord_1056977).sum := by decide
  have hdescent : baseEnd_1056977 < baseStart_1056977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057070 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_1057070 : Nat := 118140960795 + 1057070 * 2 ^ 59
def prefixEnd_1057070 : Nat := 4983230072969 + 3 ^ 40 * 1057070 * 2
def baseEnd_1057070 : Nat := 241237775754793085539391

theorem tailTrace_1057070 : CollatzResearch.WordTrace tailWord_1057070 prefixEnd_1057070 241237775754793085539391 := by
  unfold tailWord_1057070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4819313785052924753516083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25703006853615598685419109 4819313785052924753516083)
  ·
    refine ⟨7228970677579387130274125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4819313785052924753516083 7228970677579387130274125)
    ·
      refine ⟨2710864004092270173852797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7228970677579387130274125 2710864004092270173852797)
      ·
        refine ⟨1016574001534601315194799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2710864004092270173852797 1016574001534601315194799)
        ·
          refine ⟨1524861002301901972792199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016574001534601315194799 1524861002301901972792199)
          ·
            refine ⟨2287291503452852959188299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524861002301901972792199 2287291503452852959188299)
            ·
              refine ⟨3430937255179279438782449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287291503452852959188299 3430937255179279438782449)
              ·
                refine ⟨2573202941384459579086837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3430937255179279438782449 2573202941384459579086837)
                ·
                  refine ⟨241237775754793085539391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2573202941384459579086837 241237775754793085539391)
                  ·
                    rfl

theorem cell21_1057070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_1057070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057070 prefixEnd_1057070 := by exact prefixLift 1057070
  have htrace : WordTrace (prefixWord ++ tailWord_1057070) baseStart_1057070 baseEnd_1057070 := by
    simpa [prefixWord, tailWord_1057070, baseEnd_1057070] using wordTrace_append hprefix tailTrace_1057070
  have hstable : (prefixWord ++ tailWord_1057070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057070).length < 2 ^ (prefixWord ++ tailWord_1057070).sum := by decide
  have hdescent : baseEnd_1057070 < baseStart_1057070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057095 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 7]
def baseStart_1057095 : Nat := 118140960795 + 1057095 * 2 ^ 59
def prefixEnd_1057095 : Nat := 4983230072969 + 3 ^ 40 * 1057095 * 2
def baseEnd_1057095 : Nat := 241243481095398597622673

theorem tailTrace_1057095 : CollatzResearch.WordTrace tailWord_1057095 prefixEnd_1057095 241243481095398597622673 := by
  unfold tailWord_1057095
  simp only [CollatzResearch.WordTrace]
  refine ⟨38555422105332827297788739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25703614736888551531859159 38555422105332827297788739)
  ·
    refine ⟨57833133157999240946683109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38555422105332827297788739 57833133157999240946683109)
    ·
      refine ⟨10843712467124857677503083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57833133157999240946683109 10843712467124857677503083)
      ·
        refine ⟨16265568700687286516254625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10843712467124857677503083 16265568700687286516254625)
        ·
          refine ⟨12199176525515464887190969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16265568700687286516254625 12199176525515464887190969)
          ·
            refine ⟨9149382394136598665393227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12199176525515464887190969 9149382394136598665393227)
            ·
              refine ⟨13724073591204897998089841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9149382394136598665393227 13724073591204897998089841)
              ·
                refine ⟨10293055193403673498567381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13724073591204897998089841 10293055193403673498567381)
                ·
                  refine ⟨241243481095398597622673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10293055193403673498567381 241243481095398597622673)
                  ·
                    rfl

theorem cell21_1057095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_1057095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057095 prefixEnd_1057095 := by exact prefixLift 1057095
  have htrace : WordTrace (prefixWord ++ tailWord_1057095) baseStart_1057095 baseEnd_1057095 := by
    simpa [prefixWord, tailWord_1057095, baseEnd_1057095] using wordTrace_append hprefix tailTrace_1057095
  have hstable : (prefixWord ++ tailWord_1057095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057095).length < 2 ^ (prefixWord ++ tailWord_1057095).sum := by decide
  have hdescent : baseEnd_1057095 < baseStart_1057095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057247 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 7]
def baseStart_1057247 : Nat := 118140960795 + 1057247 * 2 ^ 59
def prefixEnd_1057247 : Nat := 4983230072969 + 3 ^ 40 * 1057247 * 2
def baseEnd_1057247 : Nat := 241278169566280111089029

theorem tailTrace_1057247 : CollatzResearch.WordTrace tailWord_1057247 prefixEnd_1057247 241278169566280111089029 := by
  unfold tailWord_1057247
  simp only [CollatzResearch.WordTrace]
  refine ⟨38560966000782157257321995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25707310667188104838214663 38560966000782157257321995)
  ·
    refine ⟨57841449001173235885982993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38560966000782157257321995 57841449001173235885982993)
    ·
      refine ⟨43381086750879926914487245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57841449001173235885982993 43381086750879926914487245)
      ·
        refine ⟨16267907531579972592932717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43381086750879926914487245 16267907531579972592932717)
        ·
          refine ⟨6100465324342489722349769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16267907531579972592932717 6100465324342489722349769)
          ·
            refine ⟨4575348993256867291762327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6100465324342489722349769 4575348993256867291762327)
            ·
              refine ⟨6863023489885300937643491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4575348993256867291762327 6863023489885300937643491)
              ·
                refine ⟨10294535234827951406465237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6863023489885300937643491 10294535234827951406465237)
                ·
                  refine ⟨241278169566280111089029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10294535234827951406465237 241278169566280111089029)
                  ·
                    rfl

theorem cell21_1057247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_1057247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057247 prefixEnd_1057247 := by exact prefixLift 1057247
  have htrace : WordTrace (prefixWord ++ tailWord_1057247) baseStart_1057247 baseEnd_1057247 := by
    simpa [prefixWord, tailWord_1057247, baseEnd_1057247] using wordTrace_append hprefix tailTrace_1057247
  have hstable : (prefixWord ++ tailWord_1057247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057247).length < 2 ^ (prefixWord ++ tailWord_1057247).sum := by decide
  have hdescent : baseEnd_1057247 < baseStart_1057247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057281 : List Nat := [1, 2, 4, 1, 3, 1, 2, 4, 3]
def baseStart_1057281 : Nat := 118140960795 + 1057281 * 2 ^ 59
def prefixEnd_1057281 : Nat := 4983230072969 + 3 ^ 40 * 1057281 * 2
def baseEnd_1057281 : Nat := 241285928829503607522293

theorem tailTrace_1057281 : CollatzResearch.WordTrace tailWord_1057281 prefixEnd_1057281 241285928829503607522293 := by
  unfold tailWord_1057281
  simp only [CollatzResearch.WordTrace]
  refine ⟨38562206082658981064059697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25708137388439320709373131 38562206082658981064059697)
  ·
    refine ⟨28921654561994235798044773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38562206082658981064059697 28921654561994235798044773)
    ·
      refine ⟨5422810230373919212133395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28921654561994235798044773 5422810230373919212133395)
      ·
        refine ⟨8134215345560878818200093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5422810230373919212133395 8134215345560878818200093)
        ·
          refine ⟨3050330754585329556825035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8134215345560878818200093 3050330754585329556825035)
          ·
            refine ⟨4575496131877994335237553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3050330754585329556825035 4575496131877994335237553)
            ·
              refine ⟨3431622098908495751428165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4575496131877994335237553 3431622098908495751428165)
              ·
                refine ⟨643429143545342953392781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3431622098908495751428165 643429143545342953392781)
                ·
                  refine ⟨241285928829503607522293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 643429143545342953392781 241285928829503607522293)
                  ·
                    rfl

theorem cell21_1057281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 3].length) (baseStart_1057281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057281 prefixEnd_1057281 := by exact prefixLift 1057281
  have htrace : WordTrace (prefixWord ++ tailWord_1057281) baseStart_1057281 baseEnd_1057281 := by
    simpa [prefixWord, tailWord_1057281, baseEnd_1057281] using wordTrace_append hprefix tailTrace_1057281
  have hstable : (prefixWord ++ tailWord_1057281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057281).length < 2 ^ (prefixWord ++ tailWord_1057281).sum := by decide
  have hdescent : baseEnd_1057281 < baseStart_1057281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057309 : List Nat := [1, 4, 2, 2, 1, 3, 1, 7]
def baseStart_1057309 : Nat := 118140960795 + 1057309 * 2 ^ 59
def prefixEnd_1057309 : Nat := 4983230072969 + 3 ^ 40 * 1057309 * 2
def baseEnd_1057309 : Nat := 80430772936993927018523

theorem tailTrace_1057309 : CollatzResearch.WordTrace tailWord_1057309 prefixEnd_1057309 80430772936993927018523 := by
  unfold tailWord_1057309
  simp only [CollatzResearch.WordTrace]
  refine ⟨38563227326557541846078981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25708818217705027897385987 38563227326557541846078981)
  ·
    refine ⟨7230605123729539096139809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38563227326557541846078981 7230605123729539096139809)
    ·
      refine ⟨5422953842797154322104857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7230605123729539096139809 5422953842797154322104857)
      ·
        refine ⟨4067215382097865741578643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5422953842797154322104857 4067215382097865741578643)
        ·
          refine ⟨6100823073146798612367965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4067215382097865741578643 6100823073146798612367965)
          ·
            refine ⟨2287808652430049479637987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6100823073146798612367965 2287808652430049479637987)
            ·
              refine ⟨3431712978645074219456981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287808652430049479637987 3431712978645074219456981)
              ·
                refine ⟨80430772936993927018523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3431712978645074219456981 80430772936993927018523)
                ·
                  rfl

theorem cell21_1057309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 7].length) (baseStart_1057309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057309 prefixEnd_1057309 := by exact prefixLift 1057309
  have htrace : WordTrace (prefixWord ++ tailWord_1057309) baseStart_1057309 baseEnd_1057309 := by
    simpa [prefixWord, tailWord_1057309, baseEnd_1057309] using wordTrace_append hprefix tailTrace_1057309
  have hstable : (prefixWord ++ tailWord_1057309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057309).length < 2 ^ (prefixWord ++ tailWord_1057309).sum := by decide
  have hdescent : baseEnd_1057309 < baseStart_1057309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057326 : List Nat := [4, 1, 3, 1, 3, 2, 7]
def baseStart_1057326 : Nat := 118140960795 + 1057326 * 2 ^ 59
def prefixEnd_1057326 : Nat := 4983230072969 + 3 ^ 40 * 1057326 * 2
def baseEnd_1057326 : Nat := 26810688715843725474689

theorem tailTrace_1057326 : CollatzResearch.WordTrace tailWord_1057326 prefixEnd_1057326 26810688715843725474689 := by
  unfold tailWord_1057326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4820480920936994218680979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25709231578330635832965221 4820480920936994218680979)
  ·
    refine ⟨7230721381405491328021469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4820480920936994218680979 7230721381405491328021469)
    ·
      refine ⟨2711520518027059248008051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7230721381405491328021469 2711520518027059248008051)
      ·
        refine ⟨4067280777040588872012077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2711520518027059248008051 4067280777040588872012077)
        ·
          refine ⟨1525230291390220827004529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4067280777040588872012077 1525230291390220827004529)
          ·
            refine ⟨1143922718542665620253397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1525230291390220827004529 1143922718542665620253397)
            ·
              refine ⟨26810688715843725474689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1143922718542665620253397 26810688715843725474689)
              ·
                rfl

theorem cell21_1057326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 7].length) (baseStart_1057326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057326 prefixEnd_1057326 := by exact prefixLift 1057326
  have htrace : WordTrace (prefixWord ++ tailWord_1057326) baseStart_1057326 baseEnd_1057326 := by
    simpa [prefixWord, tailWord_1057326, baseEnd_1057326] using wordTrace_append hprefix tailTrace_1057326
  have hstable : (prefixWord ++ tailWord_1057326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057326).length < 2 ^ (prefixWord ++ tailWord_1057326).sum := by decide
  have hdescent : baseEnd_1057326 < baseStart_1057326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057332 : List Nat := [2, 5, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1057332 : Nat := 118140960795 + 1057332 * 2 ^ 59
def prefixEnd_1057332 : Nat := 4983230072969 + 3 ^ 40 * 1057332 * 2
def baseEnd_1057332 : Nat := 241297567724338852172189

theorem tailTrace_1057332 : CollatzResearch.WordTrace tailWord_1057332 prefixEnd_1057332 241297567724338852172189 := by
  unfold tailWord_1057332
  simp only [CollatzResearch.WordTrace]
  refine ⟨19282033102737108387083125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25709377470316144516110833 19282033102737108387083125)
  ·
    refine ⟨1807690603381603911289043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19282033102737108387083125 1807690603381603911289043)
    ·
      refine ⟨2711535905072405866933565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1807690603381603911289043 2711535905072405866933565)
      ·
        refine ⟨1016825964402152200100087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2711535905072405866933565 1016825964402152200100087)
        ·
          refine ⟨1525238946603228300150131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016825964402152200100087 1525238946603228300150131)
          ·
            refine ⟨2287858419904842450225197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525238946603228300150131 2287858419904842450225197)
            ·
              refine ⟨857946907464315918834449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2287858419904842450225197 857946907464315918834449)
              ·
                refine ⟨643460180598236939125837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 857946907464315918834449 643460180598236939125837)
                ·
                  refine ⟨241297567724338852172189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 643460180598236939125837 241297567724338852172189)
                  ·
                    rfl

theorem cell21_1057332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1057332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057332 prefixEnd_1057332 := by exact prefixLift 1057332
  have htrace : WordTrace (prefixWord ++ tailWord_1057332) baseStart_1057332 baseEnd_1057332 := by
    simpa [prefixWord, tailWord_1057332, baseEnd_1057332] using wordTrace_append hprefix tailTrace_1057332
  have hstable : (prefixWord ++ tailWord_1057332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057332).length < 2 ^ (prefixWord ++ tailWord_1057332).sum := by decide
  have hdescent : baseEnd_1057332 < baseStart_1057332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057340 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 5]
def baseStart_1057340 : Nat := 118140960795 + 1057340 * 2 ^ 59
def prefixEnd_1057340 : Nat := 4983230072969 + 3 ^ 40 * 1057340 * 2
def baseEnd_1057340 : Nat := 241299393433332616038839

theorem tailTrace_1057340 : CollatzResearch.WordTrace tailWord_1057340 prefixEnd_1057340 241299393433332616038839 := by
  unfold tailWord_1057340
  simp only [CollatzResearch.WordTrace]
  refine ⟨19282178994722617070228737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25709571992963489426971649 19282178994722617070228737)
  ·
    refine ⟨14461634246041962802671553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19282178994722617070228737 14461634246041962802671553)
    ·
      refine ⟨10846225684531472102003665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14461634246041962802671553 10846225684531472102003665)
      ·
        refine ⟨8134669263398604076502749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10846225684531472102003665 8134669263398604076502749)
        ·
          refine ⟨3050500973774476528688531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8134669263398604076502749 3050500973774476528688531)
          ·
            refine ⟨4575751460661714793032797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3050500973774476528688531 4575751460661714793032797)
            ·
              refine ⟨1715906797748143047387299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4575751460661714793032797 1715906797748143047387299)
              ·
                refine ⟨2573860196622214571080949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1715906797748143047387299 2573860196622214571080949)
                ·
                  refine ⟨241299393433332616038839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2573860196622214571080949 241299393433332616038839)
                  ·
                    rfl

theorem cell21_1057340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_1057340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057340 prefixEnd_1057340 := by exact prefixLift 1057340
  have htrace : WordTrace (prefixWord ++ tailWord_1057340) baseStart_1057340 baseEnd_1057340 := by
    simpa [prefixWord, tailWord_1057340, baseEnd_1057340] using wordTrace_append hprefix tailTrace_1057340
  have hstable : (prefixWord ++ tailWord_1057340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057340).length < 2 ^ (prefixWord ++ tailWord_1057340).sum := by decide
  have hdescent : baseEnd_1057340 < baseStart_1057340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057368 : List Nat := [2, 1, 2, 2, 1, 2, 4, 7]
def baseStart_1057368 : Nat := 118140960795 + 1057368 * 2 ^ 59
def prefixEnd_1057368 : Nat := 4983230072969 + 3 ^ 40 * 1057368 * 2
def baseEnd_1057368 : Nat := 80435261138270263190705

theorem tailTrace_1057368 : CollatzResearch.WordTrace tailWord_1057368 prefixEnd_1057368 80435261138270263190705 := by
  unfold tailWord_1057368
  simp only [CollatzResearch.WordTrace]
  refine ⟨19282689616671897461238379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25710252822229196614984505 19282689616671897461238379)
  ·
    refine ⟨28924034425007846191857569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19282689616671897461238379 28924034425007846191857569)
    ·
      refine ⟨21693025818755884643893177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28924034425007846191857569 21693025818755884643893177)
      ·
        refine ⟨16269769364066913482919883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21693025818755884643893177 16269769364066913482919883)
        ·
          refine ⟨24404654046100370224379825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16269769364066913482919883 24404654046100370224379825)
          ·
            refine ⟨18303490534575277668284869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24404654046100370224379825 18303490534575277668284869)
            ·
              refine ⟨3431904475232864562803413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18303490534575277668284869 3431904475232864562803413)
              ·
                refine ⟨80435261138270263190705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3431904475232864562803413 80435261138270263190705)
                ·
                  rfl

theorem cell21_1057368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_1057368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057368 prefixEnd_1057368 := by exact prefixLift 1057368
  have htrace : WordTrace (prefixWord ++ tailWord_1057368) baseStart_1057368 baseEnd_1057368 := by
    simpa [prefixWord, tailWord_1057368, baseEnd_1057368] using wordTrace_append hprefix tailTrace_1057368
  have hstable : (prefixWord ++ tailWord_1057368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057368).length < 2 ^ (prefixWord ++ tailWord_1057368).sum := by decide
  have hdescent : baseEnd_1057368 < baseStart_1057368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057444 : List Nat := [2, 3, 1, 2, 2, 1, 10]
def baseStart_1057444 : Nat := 118140960795 + 1057444 * 2 ^ 59
def prefixEnd_1057444 : Nat := 4983230072969 + 3 ^ 40 * 1057444 * 2
def baseEnd_1057444 : Nat := 26813680850027949589477

theorem tailTrace_1057444 : CollatzResearch.WordTrace tailWord_1057444 prefixEnd_1057444 26813680850027949589477 := by
  unfold tailWord_1057444
  simp only [CollatzResearch.WordTrace]
  refine ⟨19284075590534229951121693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25712100787378973268162257 19284075590534229951121693)
  ·
    refine ⟨7231528346450336231670635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19284075590534229951121693 7231528346450336231670635)
    ·
      refine ⟨10847292519675504347505953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7231528346450336231670635 10847292519675504347505953)
      ·
        refine ⟨8135469389756628260629465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10847292519675504347505953 8135469389756628260629465)
        ·
          refine ⟨6101602042317471195472099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8135469389756628260629465 6101602042317471195472099)
          ·
            refine ⟨9152403063476206793208149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6101602042317471195472099 9152403063476206793208149)
            ·
              refine ⟨26813680850027949589477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9152403063476206793208149 26813680850027949589477)
              ·
                rfl

theorem cell21_1057444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 10].length) (baseStart_1057444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057444 prefixEnd_1057444 := by exact prefixLift 1057444
  have htrace : WordTrace (prefixWord ++ tailWord_1057444) baseStart_1057444 baseEnd_1057444 := by
    simpa [prefixWord, tailWord_1057444, baseEnd_1057444] using wordTrace_append hprefix tailTrace_1057444
  have hstable : (prefixWord ++ tailWord_1057444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057444).length < 2 ^ (prefixWord ++ tailWord_1057444).sum := by decide
  have hdescent : baseEnd_1057444 < baseStart_1057444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057450 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_1057450 : Nat := 118140960795 + 1057450 * 2 ^ 59
def prefixEnd_1057450 : Nat := 4983230072969 + 3 ^ 40 * 1057450 * 2
def baseEnd_1057450 : Nat := 241324496931996869205281

theorem tailTrace_1057450 : CollatzResearch.WordTrace tailWord_1057450 prefixEnd_1057450 241324496931996869205281 := by
  unfold tailWord_1057450
  simp only [CollatzResearch.WordTrace]
  refine ⟨9642092504761680731740451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25712246679364481951307869 9642092504761680731740451)
  ·
    refine ⟨14463138757142521097610677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9642092504761680731740451 14463138757142521097610677)
    ·
      refine ⟨1355919258482111352901001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14463138757142521097610677 1355919258482111352901001)
      ·
        refine ⟨1016939443861583514675751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1355919258482111352901001 1016939443861583514675751)
        ·
          refine ⟨1525409165792375272013627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016939443861583514675751 1525409165792375272013627)
          ·
            refine ⟨2288113748688562908020441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525409165792375272013627 2288113748688562908020441)
            ·
              refine ⟨1716085311516422181015331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2288113748688562908020441 1716085311516422181015331)
              ·
                refine ⟨2574127967274633271522997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1716085311516422181015331 2574127967274633271522997)
                ·
                  refine ⟨241324496931996869205281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2574127967274633271522997 241324496931996869205281)
                  ·
                    rfl

theorem cell21_1057450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_1057450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057450 prefixEnd_1057450 := by exact prefixLift 1057450
  have htrace : WordTrace (prefixWord ++ tailWord_1057450) baseStart_1057450 baseEnd_1057450 := by
    simpa [prefixWord, tailWord_1057450, baseEnd_1057450] using wordTrace_append hprefix tailTrace_1057450
  have hstable : (prefixWord ++ tailWord_1057450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057450).length < 2 ^ (prefixWord ++ tailWord_1057450).sum := by decide
  have hdescent : baseEnd_1057450 < baseStart_1057450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057489 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 8]
def baseStart_1057489 : Nat := 118140960795 + 1057489 * 2 ^ 59
def prefixEnd_1057489 : Nat := 4983230072969 + 3 ^ 40 * 1057489 * 2
def baseEnd_1057489 : Nat := 241333397263341468055201

theorem tailTrace_1057489 : CollatzResearch.WordTrace tailWord_1057489 prefixEnd_1057489 241333397263341468055201 := by
  unfold tailWord_1057489
  simp only [CollatzResearch.WordTrace]
  refine ⟨38569792465905432587631521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25713194977270288391754347 38569792465905432587631521)
  ·
    refine ⟨28927344349429074440723641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38569792465905432587631521 28927344349429074440723641)
    ·
      refine ⟨21695508262071805830542731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28927344349429074440723641 21695508262071805830542731)
      ·
        refine ⟨32543262393107708745814097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21695508262071805830542731 32543262393107708745814097)
        ·
          refine ⟨24407446794830781559360573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32543262393107708745814097 24407446794830781559360573)
          ·
            refine ⟨9152792548061543084760215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24407446794830781559360573 9152792548061543084760215)
            ·
              refine ⟨13729188822092314627140323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9152792548061543084760215 13729188822092314627140323)
              ·
                refine ⟨20593783233138471940710485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13729188822092314627140323 20593783233138471940710485)
                ·
                  refine ⟨241333397263341468055201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20593783233138471940710485 241333397263341468055201)
                  ·
                    rfl

theorem cell21_1057489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_1057489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057489 prefixEnd_1057489 := by exact prefixLift 1057489
  have htrace : WordTrace (prefixWord ++ tailWord_1057489) baseStart_1057489 baseEnd_1057489 := by
    simpa [prefixWord, tailWord_1057489, baseEnd_1057489] using wordTrace_append hprefix tailTrace_1057489
  have hstable : (prefixWord ++ tailWord_1057489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057489).length < 2 ^ (prefixWord ++ tailWord_1057489).sum := by decide
  have hdescent : baseEnd_1057489 < baseStart_1057489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057520 : List Nat := [2, 1, 1, 1, 3, 1, 6, 6]
def baseStart_1057520 : Nat := 118140960795 + 1057520 * 2 ^ 59
def prefixEnd_1057520 : Nat := 4983230072969 + 3 ^ 40 * 1057520 * 2
def baseEnd_1057520 : Nat := 80446823961897434346157

theorem tailTrace_1057520 : CollatzResearch.WordTrace tailWord_1057520 prefixEnd_1057520 80446823961897434346157 := by
  unfold tailWord_1057520
  simp only [CollatzResearch.WordTrace]
  refine ⟨19285461564396562441005007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25713948752528749921340009 19285461564396562441005007)
  ·
    refine ⟨28928192346594843661507511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19285461564396562441005007 28928192346594843661507511)
    ·
      refine ⟨43392288519892265492261267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28928192346594843661507511 43392288519892265492261267)
      ·
        refine ⟨65088432779838398238391901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43392288519892265492261267 65088432779838398238391901)
        ·
          refine ⟨24408162292439399339396963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65088432779838398238391901 24408162292439399339396963)
          ·
            refine ⟨36612243438659099009095445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24408162292439399339396963 36612243438659099009095445)
            ·
              refine ⟨1716198911187145266051349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36612243438659099009095445 1716198911187145266051349)
              ·
                refine ⟨80446823961897434346157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1716198911187145266051349 80446823961897434346157)
                ·
                  rfl

theorem cell21_1057520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_1057520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057520 prefixEnd_1057520 := by exact prefixLift 1057520
  have htrace : WordTrace (prefixWord ++ tailWord_1057520) baseStart_1057520 baseEnd_1057520 := by
    simpa [prefixWord, tailWord_1057520, baseEnd_1057520] using wordTrace_append hprefix tailTrace_1057520
  have hstable : (prefixWord ++ tailWord_1057520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057520).length < 2 ^ (prefixWord ++ tailWord_1057520).sum := by decide
  have hdescent : baseEnd_1057520 < baseStart_1057520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057554 : List Nat := [3, 2, 4, 1, 3, 8]
def baseStart_1057554 : Nat := 118140960795 + 1057554 * 2 ^ 59
def prefixEnd_1057554 : Nat := 4983230072969 + 3 ^ 40 * 1057554 * 2
def baseEnd_1057554 : Nat := 8938823375885770350805

theorem tailTrace_1057554 : CollatzResearch.WordTrace tailWord_1057554 prefixEnd_1057554 8938823375885770350805 := by
  unfold tailWord_1057554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9643040802667487172186929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25714775473779965792498477 9643040802667487172186929)
  ·
    refine ⟨7232280602000615379140197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9643040802667487172186929 7232280602000615379140197)
    ·
      refine ⟨1356052612875115383588787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7232280602000615379140197 1356052612875115383588787)
      ·
        refine ⟨2034078919312673075383181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1356052612875115383588787 2034078919312673075383181)
        ·
          refine ⟨762779594742252403268693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2034078919312673075383181 762779594742252403268693)
          ·
            refine ⟨8938823375885770350805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 762779594742252403268693 8938823375885770350805)
            ·
              rfl

theorem cell21_1057554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 8].length) (baseStart_1057554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057554 prefixEnd_1057554 := by exact prefixLift 1057554
  have htrace : WordTrace (prefixWord ++ tailWord_1057554) baseStart_1057554 baseEnd_1057554 := by
    simpa [prefixWord, tailWord_1057554, baseEnd_1057554] using wordTrace_append hprefix tailTrace_1057554
  have hstable : (prefixWord ++ tailWord_1057554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057554).length < 2 ^ (prefixWord ++ tailWord_1057554).sum := by decide
  have hdescent : baseEnd_1057554 < baseStart_1057554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057672 : List Nat := [2, 1, 3, 3, 2, 1, 9]
def baseStart_1057672 : Nat := 118140960795 + 1057672 * 2 ^ 59
def prefixEnd_1057672 : Nat := 4983230072969 + 3 ^ 40 * 1057672 * 2
def baseEnd_1057672 : Nat := 26819462261841535167203

theorem tailTrace_1057672 : CollatzResearch.WordTrace tailWord_1057672 prefixEnd_1057672 26819462261841535167203 := by
  unfold tailWord_1057672
  simp only [CollatzResearch.WordTrace]
  refine ⟨19288233512121227420771635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25717644682828303227695513 19288233512121227420771635)
  ·
    refine ⟨28932350268181841131157453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19288233512121227420771635 28932350268181841131157453)
    ·
      refine ⟨10849631350568190424184045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28932350268181841131157453 10849631350568190424184045)
      ·
        refine ⟨4068611756463071409069017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10849631350568190424184045 4068611756463071409069017)
        ·
          refine ⟨3051458817347303556801763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4068611756463071409069017 3051458817347303556801763)
          ·
            refine ⟨4577188226020955335202645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051458817347303556801763 4577188226020955335202645)
            ·
              refine ⟨26819462261841535167203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4577188226020955335202645 26819462261841535167203)
              ·
                rfl

theorem cell21_1057672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 9].length) (baseStart_1057672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057672 prefixEnd_1057672 := by exact prefixLift 1057672
  have htrace : WordTrace (prefixWord ++ tailWord_1057672) baseStart_1057672 baseEnd_1057672 := by
    simpa [prefixWord, tailWord_1057672, baseEnd_1057672] using wordTrace_append hprefix tailTrace_1057672
  have hstable : (prefixWord ++ tailWord_1057672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057672).length < 2 ^ (prefixWord ++ tailWord_1057672).sum := by decide
  have hdescent : baseEnd_1057672 < baseStart_1057672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057948 : List Nat := [2, 2, 3, 2, 1, 2, 1, 5, 3]
def baseStart_1057948 : Nat := 118140960795 + 1057948 * 2 ^ 59
def prefixEnd_1057948 : Nat := 4983230072969 + 3 ^ 40 * 1057948 * 2
def baseEnd_1057948 : Nat := 241438147316858669904263

theorem tailTrace_1057948 : CollatzResearch.WordTrace tailWord_1057948 prefixEnd_1057948 241438147316858669904263 := by
  unfold tailWord_1057948
  simp only [CollatzResearch.WordTrace]
  refine ⟨19293266785621276989295249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25724355714161702652393665 19293266785621276989295249)
  ·
    refine ⟨14469950089215957741971437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19293266785621276989295249 14469950089215957741971437)
    ·
      refine ⟨5426231283455984153239289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14469950089215957741971437 5426231283455984153239289)
      ·
        refine ⟨4069673462591988114929467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5426231283455984153239289 4069673462591988114929467)
        ·
          refine ⟨6104510193887982172394201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4069673462591988114929467 6104510193887982172394201)
          ·
            refine ⟨4578382645415986629295651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6104510193887982172394201 4578382645415986629295651)
            ·
              refine ⟨6867573968123979943943477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4578382645415986629295651 6867573968123979943943477)
              ·
                refine ⟨643835059511623119744701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6867573968123979943943477 643835059511623119744701)
                ·
                  refine ⟨241438147316858669904263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 643835059511623119744701 241438147316858669904263)
                  ·
                    rfl

theorem cell21_1057948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_1057948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1057948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1057948 prefixEnd_1057948 := by exact prefixLift 1057948
  have htrace : WordTrace (prefixWord ++ tailWord_1057948) baseStart_1057948 baseEnd_1057948 := by
    simpa [prefixWord, tailWord_1057948, baseEnd_1057948] using wordTrace_append hprefix tailTrace_1057948
  have hstable : (prefixWord ++ tailWord_1057948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057948).length < 2 ^ (prefixWord ++ tailWord_1057948).sum := by decide
  have hdescent : baseEnd_1057948 < baseStart_1057948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058035 : List Nat := [1, 1, 1, 2, 2, 5, 1, 8]
def baseStart_1058035 : Nat := 118140960795 + 1058035 * 2 ^ 59
def prefixEnd_1058035 : Nat := 4983230072969 + 3 ^ 40 * 1058035 * 2
def baseEnd_1058035 : Nat := 80486000634055283984695

theorem tailTrace_1058035 : CollatzResearch.WordTrace tailWord_1058035 prefixEnd_1058035 80486000634055283984695 := by
  unfold tailWord_1058035
  simp only [CollatzResearch.WordTrace]
  refine ⟨38589706721927367837007559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25726471147951578558005039 38589706721927367837007559)
  ·
    refine ⟨57884560082891051755511339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38589706721927367837007559 57884560082891051755511339)
    ·
      refine ⟨86826840124336577633267009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57884560082891051755511339 86826840124336577633267009)
      ·
        refine ⟨65120130093252433224950257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86826840124336577633267009 65120130093252433224950257)
        ·
          refine ⟨48840097569939324918712693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65120130093252433224950257 48840097569939324918712693)
          ·
            refine ⟨4578759147181811711129315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48840097569939324918712693 4578759147181811711129315)
            ·
              refine ⟨6868138720772717566693973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4578759147181811711129315 6868138720772717566693973)
              ·
                refine ⟨80486000634055283984695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6868138720772717566693973 80486000634055283984695)
                ·
                  rfl

theorem cell21_1058035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 8].length) (baseStart_1058035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058035 prefixEnd_1058035 := by exact prefixLift 1058035
  have htrace : WordTrace (prefixWord ++ tailWord_1058035) baseStart_1058035 baseEnd_1058035 := by
    simpa [prefixWord, tailWord_1058035, baseEnd_1058035] using wordTrace_append hprefix tailTrace_1058035
  have hstable : (prefixWord ++ tailWord_1058035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058035).length < 2 ^ (prefixWord ++ tailWord_1058035).sum := by decide
  have hdescent : baseEnd_1058035 < baseStart_1058035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058052 : List Nat := [2, 3, 2, 2, 2, 1, 2, 7]
def baseStart_1058052 : Nat := 118140960795 + 1058052 * 2 ^ 59
def prefixEnd_1058052 : Nat := 4983230072969 + 3 ^ 40 * 1058052 * 2
def baseEnd_1058052 : Nat := 80487293844592533390239

theorem tailTrace_1058052 : CollatzResearch.WordTrace tailWord_1058052 prefixEnd_1058052 80487293844592533390239 := by
  unfold tailWord_1058052
  simp only [CollatzResearch.WordTrace]
  refine ⟨19295163381432889870188205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25726884508577186493584273 19295163381432889870188205)
  ·
    refine ⟨7235686268037333701320577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19295163381432889870188205 7235686268037333701320577)
    ·
      refine ⟨5426764701028000275990433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7235686268037333701320577 5426764701028000275990433)
      ·
        refine ⟨4070073525771000206992825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5426764701028000275990433 4070073525771000206992825)
        ·
          refine ⟨3052555144328250155244619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4070073525771000206992825 3052555144328250155244619)
          ·
            refine ⟨4578832716492375232866929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3052555144328250155244619 4578832716492375232866929)
            ·
              refine ⟨3434124537369281424650197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4578832716492375232866929 3434124537369281424650197)
              ·
                refine ⟨80487293844592533390239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3434124537369281424650197 80487293844592533390239)
                ·
                  rfl

theorem cell21_1058052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_1058052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058052 prefixEnd_1058052 := by exact prefixLift 1058052
  have htrace : WordTrace (prefixWord ++ tailWord_1058052) baseStart_1058052 baseEnd_1058052 := by
    simpa [prefixWord, tailWord_1058052, baseEnd_1058052] using wordTrace_append hprefix tailTrace_1058052
  have hstable : (prefixWord ++ tailWord_1058052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058052).length < 2 ^ (prefixWord ++ tailWord_1058052).sum := by decide
  have hdescent : baseEnd_1058052 < baseStart_1058052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058207 : List Nat := [1, 1, 2, 5, 1, 4, 2, 1, 4]
def baseStart_1058207 : Nat := 118140960795 + 1058207 * 2 ^ 59
def prefixEnd_1058207 : Nat := 4983230072969 + 3 ^ 40 * 1058207 * 2
def baseEnd_1058207 : Nat := 241497254645531775087067

theorem tailTrace_1058207 : CollatzResearch.WordTrace tailWord_1058207 prefixEnd_1058207 241497254645531775087067 := by
  unfold tailWord_1058207
  simp only [CollatzResearch.WordTrace]
  refine ⟨38595980077304241212268875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25730653384869494141512583 38595980077304241212268875)
  ·
    refine ⟨57893970115956361818403313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38595980077304241212268875 57893970115956361818403313)
    ·
      refine ⟨43420477586967271363802485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57893970115956361818403313 43420477586967271363802485)
      ·
        refine ⟨4070669773778181690356483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43420477586967271363802485 4070669773778181690356483)
        ·
          refine ⟨6106004660667272535534725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4070669773778181690356483 6106004660667272535534725)
          ·
            refine ⟨1144875873875113600412761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6106004660667272535534725 1144875873875113600412761)
            ·
              refine ⟨858656905406335200309571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1144875873875113600412761 858656905406335200309571)
              ·
                refine ⟨1287985358109502800464357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858656905406335200309571 1287985358109502800464357)
                ·
                  refine ⟨241497254645531775087067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1287985358109502800464357 241497254645531775087067)
                  ·
                    rfl

theorem cell21_1058207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 4].length) (baseStart_1058207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058207 prefixEnd_1058207 := by exact prefixLift 1058207
  have htrace : WordTrace (prefixWord ++ tailWord_1058207) baseStart_1058207 baseEnd_1058207 := by
    simpa [prefixWord, tailWord_1058207, baseEnd_1058207] using wordTrace_append hprefix tailTrace_1058207
  have hstable : (prefixWord ++ tailWord_1058207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058207).length < 2 ^ (prefixWord ++ tailWord_1058207).sum := by decide
  have hdescent : baseEnd_1058207 < baseStart_1058207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058232 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 8]
def baseStart_1058232 : Nat := 118140960795 + 1058232 * 2 ^ 59
def prefixEnd_1058232 : Nat := 4983230072969 + 3 ^ 40 * 1058232 * 2
def baseEnd_1058232 : Nat := 241502959986137287170349

theorem tailTrace_1058232 : CollatzResearch.WordTrace tailWord_1058232 prefixEnd_1058232 241502959986137287170349 := by
  unfold tailWord_1058232
  simp only [CollatzResearch.WordTrace]
  refine ⟨19298445951106835240964475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25731261268142446987952633 19298445951106835240964475)
  ·
    refine ⟨28947668926660252861446713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19298445951106835240964475 28947668926660252861446713)
    ·
      refine ⟨21710751694995189646085035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28947668926660252861446713 21710751694995189646085035)
      ·
        refine ⟨32566127542492784469127553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21710751694995189646085035 32566127542492784469127553)
        ·
          refine ⟨24424595656869588351845665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32566127542492784469127553 24424595656869588351845665)
          ·
            refine ⟨18318446742652191263884249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24424595656869588351845665 18318446742652191263884249)
            ·
              refine ⟨13738835056989143447913187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18318446742652191263884249 13738835056989143447913187)
              ·
                refine ⟨20608252585483715171869781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13738835056989143447913187 20608252585483715171869781)
                ·
                  refine ⟨241502959986137287170349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20608252585483715171869781 241502959986137287170349)
                  ·
                    rfl

theorem cell21_1058232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_1058232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058232 prefixEnd_1058232 := by exact prefixLift 1058232
  have htrace : WordTrace (prefixWord ++ tailWord_1058232) baseStart_1058232 baseEnd_1058232 := by
    simpa [prefixWord, tailWord_1058232, baseEnd_1058232] using wordTrace_append hprefix tailTrace_1058232
  have hstable : (prefixWord ++ tailWord_1058232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058232).length < 2 ^ (prefixWord ++ tailWord_1058232).sum := by decide
  have hdescent : baseEnd_1058232 < baseStart_1058232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058252 : List Nat := [2, 2, 1, 4, 2, 2, 1, 4, 3]
def baseStart_1058252 : Nat := 118140960795 + 1058252 * 2 ^ 59
def prefixEnd_1058252 : Nat := 4983230072969 + 3 ^ 40 * 1058252 * 2
def baseEnd_1058252 : Nat := 241507524258621696836975

theorem tailTrace_1058252 : CollatzResearch.WordTrace tailWord_1058252 prefixEnd_1058252 241507524258621696836975 := by
  unfold tailWord_1058252
  simp only [CollatzResearch.WordTrace]
  refine ⟨19298810681070606948828505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25731747574760809265104673 19298810681070606948828505)
  ·
    refine ⟨14474108010802955211621379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19298810681070606948828505 14474108010802955211621379)
    ·
      refine ⟨21711162016204432817432069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14474108010802955211621379 21711162016204432817432069)
      ·
        refine ⟨4070842878038331153268513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21711162016204432817432069 4070842878038331153268513)
        ·
          refine ⟨3053132158528748364951385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4070842878038331153268513 3053132158528748364951385)
          ·
            refine ⟨2289849118896561273713539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3053132158528748364951385 2289849118896561273713539)
            ·
              refine ⟨3434773678344841910570309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289849118896561273713539 3434773678344841910570309)
              ·
                refine ⟨644020064689657858231933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3434773678344841910570309 644020064689657858231933)
                ·
                  refine ⟨241507524258621696836975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644020064689657858231933 241507524258621696836975)
                  ·
                    rfl

theorem cell21_1058252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_1058252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058252 prefixEnd_1058252 := by exact prefixLift 1058252
  have htrace : WordTrace (prefixWord ++ tailWord_1058252) baseStart_1058252 baseEnd_1058252 := by
    simpa [prefixWord, tailWord_1058252, baseEnd_1058252] using wordTrace_append hprefix tailTrace_1058252
  have hstable : (prefixWord ++ tailWord_1058252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058252).length < 2 ^ (prefixWord ++ tailWord_1058252).sum := by decide
  have hdescent : baseEnd_1058252 < baseStart_1058252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058280 : List Nat := [2, 1, 4, 1, 1, 2, 5, 5]
def baseStart_1058280 : Nat := 118140960795 + 1058280 * 2 ^ 59
def prefixEnd_1058280 : Nat := 4983230072969 + 3 ^ 40 * 1058280 * 2
def baseEnd_1058280 : Nat := 80504638080033290123417

theorem tailTrace_1058280 : CollatzResearch.WordTrace tailWord_1058280 prefixEnd_1058280 80504638080033290123417 := by
  unfold tailWord_1058280
  simp only [CollatzResearch.WordTrace]
  refine ⟨19299321303019887339838147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25732428404026516453117529 19299321303019887339838147)
  ·
    refine ⟨28948981954529831009757221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19299321303019887339838147 28948981954529831009757221)
    ·
      refine ⟨5427934116474343314329479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28948981954529831009757221 5427934116474343314329479)
      ·
        refine ⟨8141901174711514971494219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5427934116474343314329479 8141901174711514971494219)
        ·
          refine ⟨12212851762067272457241329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8141901174711514971494219 12212851762067272457241329)
          ·
            refine ⟨9159638821550454342930997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12212851762067272457241329 9159638821550454342930997)
            ·
              refine ⟨858716139520355094649781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9159638821550454342930997 858716139520355094649781)
              ·
                refine ⟨80504638080033290123417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 858716139520355094649781 80504638080033290123417)
                ·
                  rfl

theorem cell21_1058280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 5].length) (baseStart_1058280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058280 prefixEnd_1058280 := by exact prefixLift 1058280
  have htrace : WordTrace (prefixWord ++ tailWord_1058280) baseStart_1058280 baseEnd_1058280 := by
    simpa [prefixWord, tailWord_1058280, baseEnd_1058280] using wordTrace_append hprefix tailTrace_1058280
  have hstable : (prefixWord ++ tailWord_1058280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058280).length < 2 ^ (prefixWord ++ tailWord_1058280).sum := by decide
  have hdescent : baseEnd_1058280 < baseStart_1058280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058311 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 5]
def baseStart_1058311 : Nat := 118140960795 + 1058311 * 2 ^ 59
def prefixEnd_1058311 : Nat := 4983230072969 + 3 ^ 40 * 1058311 * 2
def baseEnd_1058311 : Nat := 241520988862450705353521

theorem tailTrace_1058311 : CollatzResearch.WordTrace tailWord_1058311 prefixEnd_1058311 241520988862450705353521 := by
  unfold tailWord_1058311
  simp only [CollatzResearch.WordTrace]
  refine ⟨38599773268927466974054787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25733182179284977982703191 38599773268927466974054787)
  ·
    refine ⟨57899659903391200461082181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38599773268927466974054787 57899659903391200461082181)
    ·
      refine ⟨10856186231885850086452909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57899659903391200461082181 10856186231885850086452909)
      ·
        refine ⟨4071069836957193782419841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10856186231885850086452909 4071069836957193782419841)
        ·
          refine ⟨3053302377717895336814881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4071069836957193782419841 3053302377717895336814881)
          ·
            refine ⟨2289976783288421502611161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3053302377717895336814881 2289976783288421502611161)
            ·
              refine ⟨1717482587466316126958371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2289976783288421502611161 1717482587466316126958371)
              ·
                refine ⟨2576223881199474190437557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1717482587466316126958371 2576223881199474190437557)
                ·
                  refine ⟨241520988862450705353521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2576223881199474190437557 241520988862450705353521)
                  ·
                    rfl

theorem cell21_1058311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 5].length) (baseStart_1058311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058311 prefixEnd_1058311 := by exact prefixLift 1058311
  have htrace : WordTrace (prefixWord ++ tailWord_1058311) baseStart_1058311 baseEnd_1058311 := by
    simpa [prefixWord, tailWord_1058311, baseEnd_1058311] using wordTrace_append hprefix tailTrace_1058311
  have hstable : (prefixWord ++ tailWord_1058311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058311).length < 2 ^ (prefixWord ++ tailWord_1058311).sum := by decide
  have hdescent : baseEnd_1058311 < baseStart_1058311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058317 : List Nat := [1, 7, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1058317 : Nat := 118140960795 + 1058317 * 2 ^ 59
def prefixEnd_1058317 : Nat := 4983230072969 + 3 ^ 40 * 1058317 * 2
def baseEnd_1058317 : Nat := 241522358144196028253509

theorem tailTrace_1058317 : CollatzResearch.WordTrace tailWord_1058317 prefixEnd_1058317 241522358144196028253509 := by
  unfold tailWord_1058317
  simp only [CollatzResearch.WordTrace]
  refine ⟨38599992106905729998773205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25733328071270486665848803 38599992106905729998773205)
  ·
    refine ⟨904687315005603046846247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 38599992106905729998773205 904687315005603046846247)
    ·
      refine ⟨1357030972508404570269371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 904687315005603046846247 1357030972508404570269371)
      ·
        refine ⟨2035546458762606855404057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1357030972508404570269371 2035546458762606855404057)
        ·
          refine ⟨1526659844071955141553043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2035546458762606855404057 1526659844071955141553043)
          ·
            refine ⟨2289989766107932712329565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526659844071955141553043 2289989766107932712329565)
            ·
              refine ⟨858746162290474767123587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2289989766107932712329565 858746162290474767123587)
              ·
                refine ⟨1288119243435712150685381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858746162290474767123587 1288119243435712150685381)
                ·
                  refine ⟨241522358144196028253509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1288119243435712150685381 241522358144196028253509)
                  ·
                    rfl

theorem cell21_1058317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1058317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058317 prefixEnd_1058317 := by exact prefixLift 1058317
  have htrace : WordTrace (prefixWord ++ tailWord_1058317) baseStart_1058317 baseEnd_1058317 := by
    simpa [prefixWord, tailWord_1058317, baseEnd_1058317] using wordTrace_append hprefix tailTrace_1058317
  have hstable : (prefixWord ++ tailWord_1058317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058317).length < 2 ^ (prefixWord ++ tailWord_1058317).sum := by decide
  have hdescent : baseEnd_1058317 < baseStart_1058317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058418 : List Nat := [3, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_1058418 : Nat := 118140960795 + 1058418 * 2 ^ 59
def prefixEnd_1058418 : Nat := 4983230072969 + 3 ^ 40 * 1058418 * 2
def baseEnd_1058418 : Nat := 241545407720242297069969

theorem tailTrace_1058418 : CollatzResearch.WordTrace tailWord_1058418 prefixEnd_1058418 241545407720242297069969 := by
  unfold tailWord_1058418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9650918969884956062049977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25735783919693216165466605 9650918969884956062049977)
  ·
    refine ⟨7238189227413717046537483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9650918969884956062049977 7238189227413717046537483)
    ·
      refine ⟨10857283841120575569806225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7238189227413717046537483 10857283841120575569806225)
      ·
        refine ⟨8142962880840431677354669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10857283841120575569806225 8142962880840431677354669)
        ·
          refine ⟨3053611080315161879008001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8142962880840431677354669 3053611080315161879008001)
          ·
            refine ⟨2290208310236371409256001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3053611080315161879008001 2290208310236371409256001)
            ·
              refine ⟨1717656232677278556942001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290208310236371409256001 1717656232677278556942001)
              ·
                refine ⟨1288242174507958917706501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1717656232677278556942001 1288242174507958917706501)
                ·
                  refine ⟨241545407720242297069969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1288242174507958917706501 241545407720242297069969)
                  ·
                    rfl

theorem cell21_1058418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_1058418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058418 prefixEnd_1058418 := by exact prefixLift 1058418
  have htrace : WordTrace (prefixWord ++ tailWord_1058418) baseStart_1058418 baseEnd_1058418 := by
    simpa [prefixWord, tailWord_1058418, baseEnd_1058418] using wordTrace_append hprefix tailTrace_1058418
  have hstable : (prefixWord ++ tailWord_1058418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058418).length < 2 ^ (prefixWord ++ tailWord_1058418).sum := by decide
  have hdescent : baseEnd_1058418 < baseStart_1058418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058421 : List Nat := [1, 3, 4, 2, 1, 1, 4, 2, 3]
def baseStart_1058421 : Nat := 118140960795 + 1058421 * 2 ^ 59
def prefixEnd_1058421 : Nat := 4983230072969 + 3 ^ 40 * 1058421 * 2
def baseEnd_1058421 : Nat := 241546092361114958519963

theorem tailTrace_1058421 : CollatzResearch.WordTrace tailWord_1058421 prefixEnd_1058421 241546092361114958519963 := by
  unfold tailWord_1058421
  simp only [CollatzResearch.WordTrace]
  refine ⟨38603785298528955760559117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25735856865685970507039411 38603785298528955760559117)
  ·
    refine ⟨14476419486948358410209669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38603785298528955760559117 14476419486948358410209669)
    ·
      refine ⟨2714328653802817201914313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14476419486948358410209669 2714328653802817201914313)
      ·
        refine ⟨2035746490352112901435735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2714328653802817201914313 2035746490352112901435735)
        ·
          refine ⟨3053619735528169352153603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2035746490352112901435735 3053619735528169352153603)
          ·
            refine ⟨4580429603292254028230405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3053619735528169352153603 4580429603292254028230405)
            ·
              refine ⟨858830550617297630293201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4580429603292254028230405 858830550617297630293201)
              ·
                refine ⟨644122912962973222719901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858830550617297630293201 644122912962973222719901)
                ·
                  refine ⟨241546092361114958519963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644122912962973222719901 241546092361114958519963)
                  ·
                    rfl

theorem cell21_1058421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_1058421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058421 prefixEnd_1058421 := by exact prefixLift 1058421
  have htrace : WordTrace (prefixWord ++ tailWord_1058421) baseStart_1058421 baseEnd_1058421 := by
    simpa [prefixWord, tailWord_1058421, baseEnd_1058421] using wordTrace_append hprefix tailTrace_1058421
  have hstable : (prefixWord ++ tailWord_1058421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058421).length < 2 ^ (prefixWord ++ tailWord_1058421).sum := by decide
  have hdescent : baseEnd_1058421 < baseStart_1058421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058446 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_1058446 : Nat := 118140960795 + 1058446 * 2 ^ 59
def prefixEnd_1058446 : Nat := 4983230072969 + 3 ^ 40 * 1058446 * 2
def baseEnd_1058446 : Nat := 241551797701720470603245

theorem tailTrace_1058446 : CollatzResearch.WordTrace tailWord_1058446 prefixEnd_1058446 241551797701720470603245 := by
  unfold tailWord_1058446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4825587140429798128777399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25736464748958923353479461 4825587140429798128777399)
  ·
    refine ⟨7238380710644697193166099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4825587140429798128777399 7238380710644697193166099)
    ·
      refine ⟨10857571065967045789749149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7238380710644697193166099 10857571065967045789749149)
      ·
        refine ⟨4071589149737642171155931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10857571065967045789749149 4071589149737642171155931)
        ·
          refine ⟨6107383724606463256733897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4071589149737642171155931 6107383724606463256733897)
          ·
            refine ⟨4580537793454847442550423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6107383724606463256733897 4580537793454847442550423)
            ·
              refine ⟨6870806690182271163825635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4580537793454847442550423 6870806690182271163825635)
              ·
                refine ⟨10306210035273406745738453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6870806690182271163825635 10306210035273406745738453)
                ·
                  refine ⟨241551797701720470603245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10306210035273406745738453 241551797701720470603245)
                  ·
                    rfl

theorem cell21_1058446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_1058446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058446 prefixEnd_1058446 := by exact prefixLift 1058446
  have htrace : WordTrace (prefixWord ++ tailWord_1058446) baseStart_1058446 baseEnd_1058446 := by
    simpa [prefixWord, tailWord_1058446, baseEnd_1058446] using wordTrace_append hprefix tailTrace_1058446
  have hstable : (prefixWord ++ tailWord_1058446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058446).length < 2 ^ (prefixWord ++ tailWord_1058446).sum := by decide
  have hdescent : baseEnd_1058446 < baseStart_1058446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058477 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1058477 : Nat := 118140960795 + 1058477 * 2 ^ 59
def prefixEnd_1058477 : Nat := 4983230072969 + 3 ^ 40 * 1058477 * 2
def baseEnd_1058477 : Nat := 241558872324071305586515

theorem tailTrace_1058477 : CollatzResearch.WordTrace tailWord_1058477 prefixEnd_1058477 241558872324071305586515 := by
  unfold tailWord_1058477
  simp only [CollatzResearch.WordTrace]
  refine ⟨38605827786326077324597685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25737218524217384883065123 38605827786326077324597685)
  ·
    refine ⟨3619296354968069749181033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38605827786326077324597685 3619296354968069749181033)
    ·
      refine ⟨2714472266226052311885775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3619296354968069749181033 2714472266226052311885775)
      ·
        refine ⟨4071708399339078467828663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2714472266226052311885775 4071708399339078467828663)
        ·
          refine ⟨6107562599008617701742995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4071708399339078467828663 6107562599008617701742995)
          ·
            refine ⟨9161343898512926552614493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6107562599008617701742995 9161343898512926552614493)
            ·
              refine ⟨3435503961942347457230435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9161343898512926552614493 3435503961942347457230435)
              ·
                refine ⟨5153255942913521185845653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3435503961942347457230435 5153255942913521185845653)
                ·
                  refine ⟨241558872324071305586515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5153255942913521185845653 241558872324071305586515)
                  ·
                    rfl

theorem cell21_1058477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1058477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058477 prefixEnd_1058477 := by exact prefixLift 1058477
  have htrace : WordTrace (prefixWord ++ tailWord_1058477) baseStart_1058477 baseEnd_1058477 := by
    simpa [prefixWord, tailWord_1058477, baseEnd_1058477] using wordTrace_append hprefix tailTrace_1058477
  have hstable : (prefixWord ++ tailWord_1058477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058477).length < 2 ^ (prefixWord ++ tailWord_1058477).sum := by decide
  have hdescent : baseEnd_1058477 < baseStart_1058477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058508 : List Nat := [2, 2, 1, 5, 2, 1, 1, 7]
def baseStart_1058508 : Nat := 118140960795 + 1058508 * 2 ^ 59
def prefixEnd_1058508 : Nat := 4983230072969 + 3 ^ 40 * 1058508 * 2
def baseEnd_1058508 : Nat := 80521982315474046856595

theorem tailTrace_1058508 : CollatzResearch.WordTrace tailWord_1058508 prefixEnd_1058508 80521982315474046856595 := by
  unfold tailWord_1058508
  simp only [CollatzResearch.WordTrace]
  refine ⟨19303479224606884809488089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25737972299475846412650785 19303479224606884809488089)
  ·
    refine ⟨14477609418455163607116067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19303479224606884809488089 14477609418455163607116067)
    ·
      refine ⟨21716414127682745410674101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14477609418455163607116067 21716414127682745410674101)
      ·
        refine ⟨2035913824470257382250697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21716414127682745410674101 2035913824470257382250697)
        ·
          refine ⟨1526935368352693036688023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2035913824470257382250697 1526935368352693036688023)
          ·
            refine ⟨2290403052529039555032035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526935368352693036688023 2290403052529039555032035)
            ·
              refine ⟨3435604578793559332548053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2290403052529039555032035 3435604578793559332548053)
              ·
                refine ⟨80521982315474046856595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3435604578793559332548053 80521982315474046856595)
                ·
                  rfl

theorem cell21_1058508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_1058508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058508 prefixEnd_1058508 := by exact prefixLift 1058508
  have htrace : WordTrace (prefixWord ++ tailWord_1058508) baseStart_1058508 baseEnd_1058508 := by
    simpa [prefixWord, tailWord_1058508, baseEnd_1058508] using wordTrace_append hprefix tailTrace_1058508
  have hstable : (prefixWord ++ tailWord_1058508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058508).length < 2 ^ (prefixWord ++ tailWord_1058508).sum := by decide
  have hdescent : baseEnd_1058508 < baseStart_1058508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058525 : List Nat := [1, 4, 3, 3, 1, 2, 7]
def baseStart_1058525 : Nat := 118140960795 + 1058525 * 2 ^ 59
def prefixEnd_1058525 : Nat := 4983230072969 + 3 ^ 40 * 1058525 * 2
def baseEnd_1058525 : Nat := 26841091842003765420713

theorem tailTrace_1058525 : CollatzResearch.WordTrace tailWord_1058525 prefixEnd_1058525 26841091842003765420713 := by
  unfold tailWord_1058525
  simp only [CollatzResearch.WordTrace]
  refine ⟨38607578490152181522345029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25738385660101454348230019 38607578490152181522345029)
  ·
    refine ⟨7238920966903534035439693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38607578490152181522345029 7238920966903534035439693)
    ·
      refine ⟨2714595362588825263289885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7238920966903534035439693 2714595362588825263289885)
      ·
        refine ⟨1017973260970809473733707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2714595362588825263289885 1017973260970809473733707)
        ·
          refine ⟨1526959891456214210600561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017973260970809473733707 1526959891456214210600561)
          ·
            refine ⟨1145219918592160657950421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1526959891456214210600561 1145219918592160657950421)
            ·
              refine ⟨26841091842003765420713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1145219918592160657950421 26841091842003765420713)
              ·
                rfl

theorem cell21_1058525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 7].length) (baseStart_1058525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058525 prefixEnd_1058525 := by exact prefixLift 1058525
  have htrace : WordTrace (prefixWord ++ tailWord_1058525) baseStart_1058525 baseEnd_1058525 := by
    simpa [prefixWord, tailWord_1058525, baseEnd_1058525] using wordTrace_append hprefix tailTrace_1058525
  have hstable : (prefixWord ++ tailWord_1058525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058525).length < 2 ^ (prefixWord ++ tailWord_1058525).sum := by decide
  have hdescent : baseEnd_1058525 < baseStart_1058525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058590 : List Nat := [4, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_1058590 : Nat := 118140960795 + 1058590 * 2 ^ 59
def prefixEnd_1058590 : Nat := 4983230072969 + 3 ^ 40 * 1058590 * 2
def baseEnd_1058590 : Nat := 241584660463608220202951

theorem tailTrace_1058590 : CollatzResearch.WordTrace tailWord_1058590 prefixEnd_1058590 241584660463608220202951 := by
  unfold tailWord_1058590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4826243654364587202932653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25739966156611131748974149 4826243654364587202932653)
  ·
    refine ⟨1809841370386720201099745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4826243654364587202932653 1809841370386720201099745)
    ·
      refine ⟨1357381027790040150824809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1809841370386720201099745 1357381027790040150824809)
      ·
        refine ⟨1018035770842530113118607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1357381027790040150824809 1018035770842530113118607)
        ·
          refine ⟨1527053656263795169677911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018035770842530113118607 1527053656263795169677911)
          ·
            refine ⟨2290580484395692754516867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527053656263795169677911 2290580484395692754516867)
            ·
              refine ⟨3435870726593539131775301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2290580484395692754516867 3435870726593539131775301)
              ·
                refine ⟨644225761236288587207869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3435870726593539131775301 644225761236288587207869)
                ·
                  refine ⟨241584660463608220202951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644225761236288587207869 241584660463608220202951)
                  ·
                    rfl

theorem cell21_1058590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_1058590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058590 prefixEnd_1058590 := by exact prefixLift 1058590
  have htrace : WordTrace (prefixWord ++ tailWord_1058590) baseStart_1058590 baseEnd_1058590 := by
    simpa [prefixWord, tailWord_1058590, baseEnd_1058590] using wordTrace_append hprefix tailTrace_1058590
  have hstable : (prefixWord ++ tailWord_1058590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058590).length < 2 ^ (prefixWord ++ tailWord_1058590).sum := by decide
  have hdescent : baseEnd_1058590 < baseStart_1058590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058691 : List Nat := [1, 1, 1, 3, 4, 2, 3, 3, 3]
def baseStart_1058691 : Nat := 118140960795 + 1058691 * 2 ^ 59
def prefixEnd_1058691 : Nat := 4983230072969 + 3 ^ 40 * 1058691 * 2
def baseEnd_1058691 : Nat := 241607710039654489019411

theorem tailTrace_1058691 : CollatzResearch.WordTrace tailWord_1058691 prefixEnd_1058691 241607710039654489019411 := by
  unfold tailWord_1058691
  simp only [CollatzResearch.WordTrace]
  refine ⟨38613633007550791872887927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25742422005033861248591951 38613633007550791872887927)
  ·
    refine ⟨57920449511326187809331891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38613633007550791872887927 57920449511326187809331891)
    ·
      refine ⟨86880674266989281713997837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57920449511326187809331891 86880674266989281713997837)
      ·
        refine ⟨32580252850120980642749189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86880674266989281713997837 32580252850120980642749189)
        ·
          refine ⟨6108797409397683870515473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32580252850120980642749189 6108797409397683870515473)
          ·
            refine ⟨4581598057048262902886605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6108797409397683870515473 4581598057048262902886605)
            ·
              refine ⟨1718099271393098588582477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4581598057048262902886605 1718099271393098588582477)
              ·
                refine ⟨644287226772411970718429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1718099271393098588582477 644287226772411970718429)
                ·
                  refine ⟨241607710039654489019411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644287226772411970718429 241607710039654489019411)
                  ·
                    rfl

theorem cell21_1058691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 3].length) (baseStart_1058691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058691 prefixEnd_1058691 := by exact prefixLift 1058691
  have htrace : WordTrace (prefixWord ++ tailWord_1058691) baseStart_1058691 baseEnd_1058691 := by
    simpa [prefixWord, tailWord_1058691, baseEnd_1058691] using wordTrace_append hprefix tailTrace_1058691
  have hstable : (prefixWord ++ tailWord_1058691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058691).length < 2 ^ (prefixWord ++ tailWord_1058691).sum := by decide
  have hdescent : baseEnd_1058691 < baseStart_1058691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058722 : List Nat := [3, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1058722 : Nat := 118140960795 + 1058722 * 2 ^ 59
def prefixEnd_1058722 : Nat := 4983230072969 + 3 ^ 40 * 1058722 * 2
def baseEnd_1058722 : Nat := 241614784662005324002681

theorem tailTrace_1058722 : CollatzResearch.WordTrace tailWord_1058722 prefixEnd_1058722 241614784662005324002681 := by
  unfold tailWord_1058722
  simp only [CollatzResearch.WordTrace]
  refine ⟨9653690917609621041816605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25743175780292322778177613 9653690917609621041816605)
  ·
    refine ⟨3620134094103607890681227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9653690917609621041816605 3620134094103607890681227)
    ·
      refine ⟨5430201141155411836021841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3620134094103607890681227 5430201141155411836021841)
      ·
        refine ⟨4072650855866558877016381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5430201141155411836021841 4072650855866558877016381)
        ·
          refine ⟨1527244070949959578881143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4072650855866558877016381 1527244070949959578881143)
          ·
            refine ⟨2290866106424939368321715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527244070949959578881143 2290866106424939368321715)
            ·
              refine ⟨3436299159637409052482573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2290866106424939368321715 3436299159637409052482573)
              ·
                refine ⟨1288612184864028394680965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3436299159637409052482573 1288612184864028394680965)
                ·
                  refine ⟨241614784662005324002681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1288612184864028394680965 241614784662005324002681)
                  ·
                    rfl

theorem cell21_1058722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1058722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058722 prefixEnd_1058722 := by exact prefixLift 1058722
  have htrace : WordTrace (prefixWord ++ tailWord_1058722) baseStart_1058722 baseEnd_1058722 := by
    simpa [prefixWord, tailWord_1058722, baseEnd_1058722] using wordTrace_append hprefix tailTrace_1058722
  have hstable : (prefixWord ++ tailWord_1058722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058722).length < 2 ^ (prefixWord ++ tailWord_1058722).sum := by decide
  have hdescent : baseEnd_1058722 < baseStart_1058722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058930 : List Nat := [3, 2, 1, 2, 2, 11]
def baseStart_1058930 : Nat := 118140960795 + 1058930 * 2 ^ 59
def prefixEnd_1058930 : Nat := 4983230072969 + 3 ^ 40 * 1058930 * 2
def baseEnd_1058930 : Nat := 8950453818364562390207

theorem tailTrace_1058930 : CollatzResearch.WordTrace tailWord_1058930 prefixEnd_1058930 8950453818364562390207 := by
  unfold tailWord_1058930
  simp only [CollatzResearch.WordTrace]
  refine ⟨9655587513421233922709561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25748233369123290460558829 9655587513421233922709561)
  ·
    refine ⟨7241690635065925442032171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9655587513421233922709561 7241690635065925442032171)
    ·
      refine ⟨10862535952598888163048257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7241690635065925442032171 10862535952598888163048257)
      ·
        refine ⟨8146901964449166122286193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10862535952598888163048257 8146901964449166122286193)
        ·
          refine ⟨6110176473336874591714645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8146901964449166122286193 6110176473336874591714645)
          ·
            refine ⟨8950453818364562390207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6110176473336874591714645 8950453818364562390207)
            ·
              rfl

theorem cell21_1058930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 11].length) (baseStart_1058930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058930 prefixEnd_1058930 := by exact prefixLift 1058930
  have htrace : WordTrace (prefixWord ++ tailWord_1058930) baseStart_1058930 baseEnd_1058930 := by
    simpa [prefixWord, tailWord_1058930, baseEnd_1058930] using wordTrace_append hprefix tailTrace_1058930
  have hstable : (prefixWord ++ tailWord_1058930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058930).length < 2 ^ (prefixWord ++ tailWord_1058930).sum := by decide
  have hdescent : baseEnd_1058930 < baseStart_1058930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058947 : List Nat := [1, 1, 1, 3, 3, 5, 1, 6]
def baseStart_1058947 : Nat := 118140960795 + 1058947 * 2 ^ 59
def prefixEnd_1058947 : Nat := 4983230072969 + 3 ^ 40 * 1058947 * 2
def baseEnd_1058947 : Nat := 80555377575818310917407

theorem tailTrace_1058947 : CollatzResearch.WordTrace tailWord_1058947 prefixEnd_1058947 80555377575818310917407 := by
  unfold tailWord_1058947
  simp only [CollatzResearch.WordTrace]
  refine ⟨38622970094623347594207095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25748646729748898396138063 38622970094623347594207095)
  ·
    refine ⟨57934455141935021391310643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38622970094623347594207095 57934455141935021391310643)
    ·
      refine ⟨86901682712902532086965965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57934455141935021391310643 86901682712902532086965965)
      ·
        refine ⟨32588131017338449532612237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86901682712902532086965965 32588131017338449532612237)
        ·
          refine ⟨12220549131501918574729589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32588131017338449532612237 12220549131501918574729589)
          ·
            refine ⟨1145676481078304866380899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12220549131501918574729589 1145676481078304866380899)
            ·
              refine ⟨1718514721617457299571349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145676481078304866380899 1718514721617457299571349)
              ·
                refine ⟨80555377575818310917407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1718514721617457299571349 80555377575818310917407)
                ·
                  rfl

theorem cell21_1058947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 6].length) (baseStart_1058947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1058947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1058947 prefixEnd_1058947 := by exact prefixLift 1058947
  have htrace : WordTrace (prefixWord ++ tailWord_1058947) baseStart_1058947 baseEnd_1058947 := by
    simpa [prefixWord, tailWord_1058947, baseEnd_1058947] using wordTrace_append hprefix tailTrace_1058947
  have hstable : (prefixWord ++ tailWord_1058947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058947).length < 2 ^ (prefixWord ++ tailWord_1058947).sum := by decide
  have hdescent : baseEnd_1058947 < baseStart_1058947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059029 : List Nat := [1, 3, 2, 4, 3, 1, 1, 3, 3]
def baseStart_1059029 : Nat := 118140960795 + 1059029 * 2 ^ 59
def prefixEnd_1059029 : Nat := 4983230072969 + 3 ^ 40 * 1059029 * 2
def baseEnd_1059029 : Nat := 241684846244641012385387

theorem tailTrace_1059029 : CollatzResearch.WordTrace tailWord_1059029 prefixEnd_1059029 241684846244641012385387 := by
  unfold tailWord_1059029
  simp only [CollatzResearch.WordTrace]
  refine ⟨38625960880326275598692141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25750640586884183732461427 38625960880326275598692141)
  ·
    refine ⟨14484735330122353349509553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38625960880326275598692141 14484735330122353349509553)
    ·
      refine ⟨10863551497591765012132165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14484735330122353349509553 10863551497591765012132165)
      ·
        refine ⟨2036915905798455939774781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10863551497591765012132165 2036915905798455939774781)
        ·
          refine ⟨763843464674420977415543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2036915905798455939774781 763843464674420977415543)
          ·
            refine ⟨1145765197011631466123315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763843464674420977415543 1145765197011631466123315)
            ·
              refine ⟨1718647795517447199184973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145765197011631466123315 1718647795517447199184973)
              ·
                refine ⟨644492923319042699694365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1718647795517447199184973 644492923319042699694365)
                ·
                  refine ⟨241684846244641012385387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644492923319042699694365 241684846244641012385387)
                  ·
                    rfl

theorem cell21_1059029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_1059029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059029 prefixEnd_1059029 := by exact prefixLift 1059029
  have htrace : WordTrace (prefixWord ++ tailWord_1059029) baseStart_1059029 baseEnd_1059029 := by
    simpa [prefixWord, tailWord_1059029, baseEnd_1059029] using wordTrace_append hprefix tailTrace_1059029
  have hstable : (prefixWord ++ tailWord_1059029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059029).length < 2 ^ (prefixWord ++ tailWord_1059029).sum := by decide
  have hdescent : baseEnd_1059029 < baseStart_1059029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059051 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 6]
def baseStart_1059051 : Nat := 118140960795 + 1059051 * 2 ^ 59
def prefixEnd_1059051 : Nat := 4983230072969 + 3 ^ 40 * 1059051 * 2
def baseEnd_1059051 : Nat := 241689866944373863018675

theorem tailTrace_1059051 : CollatzResearch.WordTrace tailWord_1059051 prefixEnd_1059051 241689866944373863018675 := by
  unfold tailWord_1059051
  simp only [CollatzResearch.WordTrace]
  refine ⟨38626763286246573355993007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25751175524164382237328671 38626763286246573355993007)
  ·
    refine ⟨57940144929369860033989511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38626763286246573355993007 57940144929369860033989511)
    ·
      refine ⟨86910217394054790050984267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57940144929369860033989511 86910217394054790050984267)
      ·
        refine ⟨130365326091082185076476401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86910217394054790050984267 130365326091082185076476401)
        ·
          refine ⟨97773994568311638807357301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130365326091082185076476401 97773994568311638807357301)
          ·
            refine ⟨9166311990779216138189747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97773994568311638807357301 9166311990779216138189747)
            ·
              refine ⟨13749467986168824207284621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9166311990779216138189747 13749467986168824207284621)
              ·
                refine ⟨5156050494813309077731733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13749467986168824207284621 5156050494813309077731733)
                ·
                  refine ⟨241689866944373863018675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5156050494813309077731733 241689866944373863018675)
                  ·
                    rfl

theorem cell21_1059051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_1059051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059051 prefixEnd_1059051 := by exact prefixLift 1059051
  have htrace : WordTrace (prefixWord ++ tailWord_1059051) baseStart_1059051 baseEnd_1059051 := by
    simpa [prefixWord, tailWord_1059051, baseEnd_1059051] using wordTrace_append hprefix tailTrace_1059051
  have hstable : (prefixWord ++ tailWord_1059051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059051).length < 2 ^ (prefixWord ++ tailWord_1059051).sum := by decide
  have hdescent : baseEnd_1059051 < baseStart_1059051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059082 : List Nat := [3, 1, 2, 2, 1, 1, 4, 7]
def baseStart_1059082 : Nat := 118140960795 + 1059082 * 2 ^ 59
def prefixEnd_1059082 : Nat := 4983230072969 + 3 ^ 40 * 1059082 * 2
def baseEnd_1059082 : Nat := 80565647188908232667315

theorem tailTrace_1059082 : CollatzResearch.WordTrace tailWord_1059082 prefixEnd_1059082 80565647188908232667315 := by
  unfold tailWord_1059082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9656973487283566412592875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25751929299422843766914333 9656973487283566412592875)
  ·
    refine ⟨14485460230925349618889313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9656973487283566412592875 14485460230925349618889313)
    ·
      refine ⟨10864095173194012214166985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14485460230925349618889313 10864095173194012214166985)
      ·
        refine ⟨8148071379895509160625239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10864095173194012214166985 8148071379895509160625239)
        ·
          refine ⟨12222107069843263740937859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8148071379895509160625239 12222107069843263740937859)
          ·
            refine ⟨18333160604764895611406789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12222107069843263740937859 18333160604764895611406789)
            ·
              refine ⟨3437467613393417927138773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18333160604764895611406789 3437467613393417927138773)
              ·
                refine ⟨80565647188908232667315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3437467613393417927138773 80565647188908232667315)
                ·
                  rfl

theorem cell21_1059082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_1059082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059082 prefixEnd_1059082 := by exact prefixLift 1059082
  have htrace : WordTrace (prefixWord ++ tailWord_1059082) baseStart_1059082 baseEnd_1059082 := by
    simpa [prefixWord, tailWord_1059082, baseEnd_1059082] using wordTrace_append hprefix tailTrace_1059082
  have hstable : (prefixWord ++ tailWord_1059082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059082).length < 2 ^ (prefixWord ++ tailWord_1059082).sum := by decide
  have hdescent : baseEnd_1059082 < baseStart_1059082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059102 : List Nat := [4, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1059102 : Nat := 118140960795 + 1059102 * 2 ^ 59
def prefixEnd_1059102 : Nat := 4983230072969 + 3 ^ 40 * 1059102 * 2
def baseEnd_1059102 : Nat := 241701505839209107668571

theorem tailTrace_1059102 : CollatzResearch.WordTrace tailWord_1059102 prefixEnd_1059102 241701505839209107668571 := by
  unfold tailWord_1059102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4828577926132726133262445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25752415606041206044066373 4828577926132726133262445)
  ·
    refine ⟨1810716722299772299973417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4828577926132726133262445 1810716722299772299973417)
    ·
      refine ⟨1358037541724829224980063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1810716722299772299973417 1358037541724829224980063)
      ·
        refine ⟨2037056312587243837470095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1358037541724829224980063 2037056312587243837470095)
        ·
          refine ⟨3055584468880865756205143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2037056312587243837470095 3055584468880865756205143)
          ·
            refine ⟨4583376703321298634307715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3055584468880865756205143 4583376703321298634307715)
            ·
              refine ⟨6875065054981947951461573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4583376703321298634307715 6875065054981947951461573)
              ·
                refine ⟨1289074697809115240899045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6875065054981947951461573 1289074697809115240899045)
                ·
                  refine ⟨241701505839209107668571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1289074697809115240899045 241701505839209107668571)
                  ·
                    rfl

theorem cell21_1059102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1059102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059102 prefixEnd_1059102 := by exact prefixLift 1059102
  have htrace : WordTrace (prefixWord ++ tailWord_1059102) baseStart_1059102 baseEnd_1059102 := by
    simpa [prefixWord, tailWord_1059102, baseEnd_1059102] using wordTrace_append hprefix tailTrace_1059102
  have hstable : (prefixWord ++ tailWord_1059102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059102).length < 2 ^ (prefixWord ++ tailWord_1059102).sum := by decide
  have hdescent : baseEnd_1059102 < baseStart_1059102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059178 : List Nat := [3, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_1059178 : Nat := 118140960795 + 1059178 * 2 ^ 59
def prefixEnd_1059178 : Nat := 4983230072969 + 3 ^ 40 * 1059178 * 2
def baseEnd_1059178 : Nat := 241718850074649864401749

theorem tailTrace_1059178 : CollatzResearch.WordTrace tailWord_1059178 prefixEnd_1059178 241718850074649864401749 := by
  unfold tailWord_1059178
  simp only [CollatzResearch.WordTrace]
  refine ⟨9657848839196618511466547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25754263571190982697244125 9657848839196618511466547)
  ·
    refine ⟨14486773258794927767199821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9657848839196618511466547 14486773258794927767199821)
    ·
      refine ⟨5432539972048097912699933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14486773258794927767199821 5432539972048097912699933)
      ·
        refine ⟨2037202489518036717262475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5432539972048097912699933 2037202489518036717262475)
        ·
          refine ⟨3055803734277055075893713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2037202489518036717262475 3055803734277055075893713)
          ·
            refine ⟨2291852800707791306920285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3055803734277055075893713 2291852800707791306920285)
            ·
              refine ⟨859444800265421740095107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2291852800707791306920285 859444800265421740095107)
              ·
                refine ⟨1289167200398132610142661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859444800265421740095107 1289167200398132610142661)
                ·
                  refine ⟨241718850074649864401749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1289167200398132610142661 241718850074649864401749)
                  ·
                    rfl

theorem cell21_1059178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_1059178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059178 prefixEnd_1059178 := by exact prefixLift 1059178
  have htrace : WordTrace (prefixWord ++ tailWord_1059178) baseStart_1059178 baseEnd_1059178 := by
    simpa [prefixWord, tailWord_1059178, baseEnd_1059178] using wordTrace_append hprefix tailTrace_1059178
  have hstable : (prefixWord ++ tailWord_1059178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059178).length < 2 ^ (prefixWord ++ tailWord_1059178).sum := by decide
  have hdescent : baseEnd_1059178 < baseStart_1059178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059324 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 9]
def baseStart_1059324 : Nat := 118140960795 + 1059324 * 2 ^ 59
def prefixEnd_1059324 : Nat := 4983230072969 + 3 ^ 40 * 1059324 * 2
def baseEnd_1059324 : Nat := 241752169263786054968117

theorem tailTrace_1059324 : CollatzResearch.WordTrace tailWord_1059324 prefixEnd_1059324 241752169263786054968117 := by
  unfold tailWord_1059324
  simp only [CollatzResearch.WordTrace]
  refine ⟨19318360207128770490340513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25757813609505027320454017 19318360207128770490340513)
  ·
    refine ⟨14488770155346577867755385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19318360207128770490340513 14488770155346577867755385)
    ·
      refine ⟨10866577616509933400816539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14488770155346577867755385 10866577616509933400816539)
      ·
        refine ⟨16299866424764900101224809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10866577616509933400816539 16299866424764900101224809)
        ·
          refine ⟨12224899818573675075918607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16299866424764900101224809 12224899818573675075918607)
          ·
            refine ⟨18337349727860512613877911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12224899818573675075918607 18337349727860512613877911)
            ·
              refine ⟨27506024591790768920816867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18337349727860512613877911 27506024591790768920816867)
              ·
                refine ⟨41259036887686153381225301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27506024591790768920816867 41259036887686153381225301)
                ·
                  refine ⟨241752169263786054968117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41259036887686153381225301 241752169263786054968117)
                  ·
                    rfl

theorem cell21_1059324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_1059324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059324 prefixEnd_1059324 := by exact prefixLift 1059324
  have htrace : WordTrace (prefixWord ++ tailWord_1059324) baseStart_1059324 baseEnd_1059324 := by
    simpa [prefixWord, tailWord_1059324, baseEnd_1059324] using wordTrace_append hprefix tailTrace_1059324
  have hstable : (prefixWord ++ tailWord_1059324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059324).length < 2 ^ (prefixWord ++ tailWord_1059324).sum := by decide
  have hdescent : baseEnd_1059324 < baseStart_1059324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059386 : List Nat := [3, 1, 1, 1, 3, 5, 7]
def baseStart_1059386 : Nat := 118140960795 + 1059386 * 2 ^ 59
def prefixEnd_1059386 : Nat := 4983230072969 + 3 ^ 40 * 1059386 * 2
def baseEnd_1059386 : Nat := 26862924278720858326073

theorem tailTrace_1059386 : CollatzResearch.WordTrace tailWord_1059386 prefixEnd_1059386 26862924278720858326073 := by
  unfold tailWord_1059386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9659745435008231392359503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25759321160021950379625341 9659745435008231392359503)
  ·
    refine ⟨14489618152512347088539255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9659745435008231392359503 14489618152512347088539255)
    ·
      refine ⟨21734427228768520632808883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14489618152512347088539255 21734427228768520632808883)
      ·
        refine ⟨32601640843152780949213325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21734427228768520632808883 32601640843152780949213325)
        ·
          refine ⟨12225615316182292855954997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32601640843152780949213325 12225615316182292855954997)
          ·
            refine ⟨1146151435892089955245781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12225615316182292855954997 1146151435892089955245781)
            ·
              refine ⟨26862924278720858326073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1146151435892089955245781 26862924278720858326073)
              ·
                rfl

theorem cell21_1059386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 7].length) (baseStart_1059386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059386 prefixEnd_1059386 := by exact prefixLift 1059386
  have htrace : WordTrace (prefixWord ++ tailWord_1059386) baseStart_1059386 baseEnd_1059386 := by
    simpa [prefixWord, tailWord_1059386, baseEnd_1059386] using wordTrace_append hprefix tailTrace_1059386
  have hstable : (prefixWord ++ tailWord_1059386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059386).length < 2 ^ (prefixWord ++ tailWord_1059386).sum := by decide
  have hdescent : baseEnd_1059386 < baseStart_1059386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059434 : List Nat := [3, 1, 3, 2, 1, 1, 2, 5, 3]
def baseStart_1059434 : Nat := 118140960795 + 1059434 * 2 ^ 59
def prefixEnd_1059434 : Nat := 4983230072969 + 3 ^ 40 * 1059434 * 2
def baseEnd_1059434 : Nat := 241777272762450308134559

theorem tailTrace_1059434 : CollatzResearch.WordTrace tailWord_1059434 prefixEnd_1059434 241777272762450308134559 := by
  unfold tailWord_1059434
  simp only [CollatzResearch.WordTrace]
  refine ⟨9660183110964757441796339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25760488295906019844790237 9660183110964757441796339)
  ·
    refine ⟨14490274666447136162694509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9660183110964757441796339 14490274666447136162694509)
    ·
      refine ⟨5433852999917676061010441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14490274666447136162694509 5433852999917676061010441)
      ·
        refine ⟨4075389749938257045757831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5433852999917676061010441 4075389749938257045757831)
        ·
          refine ⟨6113084624907385568636747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075389749938257045757831 6113084624907385568636747)
          ·
            refine ⟨9169626937361078352955121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6113084624907385568636747 9169626937361078352955121)
            ·
              refine ⟨6877220203020808764716341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9169626937361078352955121 6877220203020808764716341)
              ·
                refine ⟨644739394033200821692157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6877220203020808764716341 644739394033200821692157)
                ·
                  refine ⟨241777272762450308134559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644739394033200821692157 241777272762450308134559)
                  ·
                    rfl

theorem cell21_1059434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_1059434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059434 prefixEnd_1059434 := by exact prefixLift 1059434
  have htrace : WordTrace (prefixWord ++ tailWord_1059434) baseStart_1059434 baseEnd_1059434 := by
    simpa [prefixWord, tailWord_1059434, baseEnd_1059434] using wordTrace_append hprefix tailTrace_1059434
  have hstable : (prefixWord ++ tailWord_1059434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059434).length < 2 ^ (prefixWord ++ tailWord_1059434).sum := by decide
  have hdescent : baseEnd_1059434 < baseStart_1059434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059507 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 6]
def baseStart_1059507 : Nat := 118140960795 + 1059507 * 2 ^ 59
def prefixEnd_1059507 : Nat := 4983230072969 + 3 ^ 40 * 1059507 * 2
def baseEnd_1059507 : Nat := 241793932357018403417743

theorem tailTrace_1059507 : CollatzResearch.WordTrace tailWord_1059507 prefixEnd_1059507 241793932357018403417743 := by
  unfold tailWord_1059507
  simp only [CollatzResearch.WordTrace]
  refine ⟨38643394972594563234592775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25762263315063042156395183 38643394972594563234592775)
  ·
    refine ⟨57965092458891844851889163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38643394972594563234592775 57965092458891844851889163)
    ·
      refine ⟨86947638688337767277833745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57965092458891844851889163 86947638688337767277833745)
      ·
        refine ⟨65210729016253325458375309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86947638688337767277833745 65210729016253325458375309)
        ·
          refine ⟨24454023381094997046890741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65210729016253325458375309 24454023381094997046890741)
          ·
            refine ⟨2292564691977655973146007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24454023381094997046890741 2292564691977655973146007)
            ·
              refine ⟨3438847037966483959719011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2292564691977655973146007 3438847037966483959719011)
              ·
                refine ⟨5158270556949725939578517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3438847037966483959719011 5158270556949725939578517)
                ·
                  refine ⟨241793932357018403417743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5158270556949725939578517 241793932357018403417743)
                  ·
                    rfl

theorem cell21_1059507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 6].length) (baseStart_1059507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059507 prefixEnd_1059507 := by exact prefixLift 1059507
  have htrace : WordTrace (prefixWord ++ tailWord_1059507) baseStart_1059507 baseEnd_1059507 := by
    simpa [prefixWord, tailWord_1059507, baseEnd_1059507] using wordTrace_append hprefix tailTrace_1059507
  have hstable : (prefixWord ++ tailWord_1059507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059507).length < 2 ^ (prefixWord ++ tailWord_1059507).sum := by decide
  have hdescent : baseEnd_1059507 < baseStart_1059507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059614 : List Nat := [4, 3, 2, 12]
def baseStart_1059614 : Nat := 118140960795 + 1059614 * 2 ^ 59
def prefixEnd_1059614 : Nat := 4983230072969 + 3 ^ 40 * 1059614 * 2
def baseEnd_1059614 : Nat := 995137247797571996437

theorem tailTrace_1059614 : CollatzResearch.WordTrace tailWord_1059614 prefixEnd_1059614 995137247797571996437 := by
  unfold tailWord_1059614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4830912197900865063592237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25764865055471280339158597 4830912197900865063592237)
  ·
    refine ⟨1811592074212824398847089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4830912197900865063592237 1811592074212824398847089)
    ·
      refine ⟨1358694055659618299135317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1811592074212824398847089 1358694055659618299135317)
      ·
        refine ⟨995137247797571996437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1358694055659618299135317 995137247797571996437)
        ·
          rfl

theorem cell21_1059614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 12].length) (baseStart_1059614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059614 prefixEnd_1059614 := by exact prefixLift 1059614
  have htrace : WordTrace (prefixWord ++ tailWord_1059614) baseStart_1059614 baseEnd_1059614 := by
    simpa [prefixWord, tailWord_1059614, baseEnd_1059614] using wordTrace_append hprefix tailTrace_1059614
  have hstable : (prefixWord ++ tailWord_1059614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059614).length < 2 ^ (prefixWord ++ tailWord_1059614).sum := by decide
  have hdescent : baseEnd_1059614 < baseStart_1059614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059620 : List Nat := [2, 3, 1, 3, 3, 2, 2, 2, 3]
def baseStart_1059620 : Nat := 118140960795 + 1059620 * 2 ^ 59
def prefixEnd_1059620 : Nat := 4983230072969 + 3 ^ 40 * 1059620 * 2
def baseEnd_1059620 : Nat := 241819720496555318034179

theorem tailTrace_1059620 : CollatzResearch.WordTrace tailWord_1059620 prefixEnd_1059620 241819720496555318034179 := by
  unfold tailWord_1059620
  simp only [CollatzResearch.WordTrace]
  refine ⟨19323758210592591766728157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25765010947456789022304209 19323758210592591766728157)
  ·
    refine ⟨7246409328972221912523059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19323758210592591766728157 7246409328972221912523059)
    ·
      refine ⟨10869613993458332868784589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7246409328972221912523059 10869613993458332868784589)
      ·
        refine ⟨4076105247546874825794221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10869613993458332868784589 4076105247546874825794221)
        ·
          refine ⟨1528539467830078059672833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4076105247546874825794221 1528539467830078059672833)
          ·
            refine ⟨1146404600872558544754625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1528539467830078059672833 1146404600872558544754625)
            ·
              refine ⟨859803450654418908565969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1146404600872558544754625 859803450654418908565969)
              ·
                refine ⟨644852587990814181424477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859803450654418908565969 644852587990814181424477)
                ·
                  refine ⟨241819720496555318034179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644852587990814181424477 241819720496555318034179)
                  ·
                    rfl

theorem cell21_1059620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_1059620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059620 prefixEnd_1059620 := by exact prefixLift 1059620
  have htrace : WordTrace (prefixWord ++ tailWord_1059620) baseStart_1059620 baseEnd_1059620 := by
    simpa [prefixWord, tailWord_1059620, baseEnd_1059620] using wordTrace_append hprefix tailTrace_1059620
  have hstable : (prefixWord ++ tailWord_1059620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059620).length < 2 ^ (prefixWord ++ tailWord_1059620).sum := by decide
  have hdescent : baseEnd_1059620 < baseStart_1059620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059628 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 5]
def baseStart_1059628 : Nat := 118140960795 + 1059628 * 2 ^ 59
def prefixEnd_1059628 : Nat := 4983230072969 + 3 ^ 40 * 1059628 * 2
def baseEnd_1059628 : Nat := 241821546205549081900829

theorem tailTrace_1059628 : CollatzResearch.WordTrace tailWord_1059628 prefixEnd_1059628 241821546205549081900829 := by
  unfold tailWord_1059628
  simp only [CollatzResearch.WordTrace]
  refine ⟨19323904102578100449873769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25765205470104133933165025 19323904102578100449873769)
  ·
    refine ⟨14492928076933575337405327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19323904102578100449873769 14492928076933575337405327)
    ·
      refine ⟨21739392115400363006107991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14492928076933575337405327 21739392115400363006107991)
      ·
        refine ⟨32609088173100544509161987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21739392115400363006107991 32609088173100544509161987)
        ·
          refine ⟨48913632259650816763742981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32609088173100544509161987 48913632259650816763742981)
          ·
            refine ⟨9171306048684528143201809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48913632259650816763742981 9171306048684528143201809)
            ·
              refine ⟨6878479536513396107401357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9171306048684528143201809 6878479536513396107401357)
              ·
                refine ⟨2579429826192523540275509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6878479536513396107401357 2579429826192523540275509)
                ·
                  refine ⟨241821546205549081900829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2579429826192523540275509 241821546205549081900829)
                  ·
                    rfl

theorem cell21_1059628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_1059628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059628 prefixEnd_1059628 := by exact prefixLift 1059628
  have htrace : WordTrace (prefixWord ++ tailWord_1059628) baseStart_1059628 baseEnd_1059628 := by
    simpa [prefixWord, tailWord_1059628, baseEnd_1059628] using wordTrace_append hprefix tailTrace_1059628
  have hstable : (prefixWord ++ tailWord_1059628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059628).length < 2 ^ (prefixWord ++ tailWord_1059628).sum := by decide
  have hdescent : baseEnd_1059628 < baseStart_1059628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059673 : List Nat := [1, 2, 1, 2, 2, 5, 8]
def baseStart_1059673 : Nat := 118140960795 + 1059673 * 2 ^ 59
def prefixEnd_1059673 : Nat := 4983230072969 + 3 ^ 40 * 1059673 * 2
def baseEnd_1059673 : Nat := 26870201757626555961193

theorem tailTrace_1059673 : CollatzResearch.WordTrace tailWord_1059673 prefixEnd_1059673 26870201757626555961193 := by
  unfold tailWord_1059673
  simp only [CollatzResearch.WordTrace]
  refine ⟨38649449489993173585135673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25766299659995449056757115 38649449489993173585135673)
  ·
    refine ⟨28987087117494880188851755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38649449489993173585135673 28987087117494880188851755)
    ·
      refine ⟨43480630676242320283277633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28987087117494880188851755 43480630676242320283277633)
      ·
        refine ⟨32610473007181740212458225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43480630676242320283277633 32610473007181740212458225)
        ·
          refine ⟨24457854755386305159343669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32610473007181740212458225 24457854755386305159343669)
          ·
            refine ⟨2292923883317466108688469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24457854755386305159343669 2292923883317466108688469)
            ·
              refine ⟨26870201757626555961193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2292923883317466108688469 26870201757626555961193)
              ·
                rfl

theorem cell21_1059673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 8].length) (baseStart_1059673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059673 prefixEnd_1059673 := by exact prefixLift 1059673
  have htrace : WordTrace (prefixWord ++ tailWord_1059673) baseStart_1059673 baseEnd_1059673 := by
    simpa [prefixWord, tailWord_1059673, baseEnd_1059673] using wordTrace_append hprefix tailTrace_1059673
  have hstable : (prefixWord ++ tailWord_1059673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059673).length < 2 ^ (prefixWord ++ tailWord_1059673).sum := by decide
  have hdescent : baseEnd_1059673 < baseStart_1059673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059676 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 6]
def baseStart_1059676 : Nat := 118140960795 + 1059676 * 2 ^ 59
def prefixEnd_1059676 : Nat := 4983230072969 + 3 ^ 40 * 1059676 * 2
def baseEnd_1059676 : Nat := 241832500459511665100731

theorem tailTrace_1059676 : CollatzResearch.WordTrace tailWord_1059676 prefixEnd_1059676 241832500459511665100731 := by
  unfold tailWord_1059676
  simp only [CollatzResearch.WordTrace]
  refine ⟨19324779454491152548747441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25766372605988203398329921 19324779454491152548747441)
  ·
    refine ⟨14493584590868364411560581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19324779454491152548747441 14493584590868364411560581)
    ·
      refine ⟨2717547110787818327167609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14493584590868364411560581 2717547110787818327167609)
      ·
        refine ⟨2038160333090863745375707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2717547110787818327167609 2038160333090863745375707)
        ·
          refine ⟨3057240499636295618063561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038160333090863745375707 3057240499636295618063561)
          ·
            refine ⟨2292930374727221713547671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3057240499636295618063561 2292930374727221713547671)
            ·
              refine ⟨3439395562090832570321507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2292930374727221713547671 3439395562090832570321507)
              ·
                refine ⟨5159093343136248855482261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3439395562090832570321507 5159093343136248855482261)
                ·
                  refine ⟨241832500459511665100731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5159093343136248855482261 241832500459511665100731)
                  ·
                    rfl

theorem cell21_1059676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_1059676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059676 prefixEnd_1059676 := by exact prefixLift 1059676
  have htrace : WordTrace (prefixWord ++ tailWord_1059676) baseStart_1059676 baseEnd_1059676 := by
    simpa [prefixWord, tailWord_1059676, baseEnd_1059676] using wordTrace_append hprefix tailTrace_1059676
  have hstable : (prefixWord ++ tailWord_1059676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059676).length < 2 ^ (prefixWord ++ tailWord_1059676).sum := by decide
  have hdescent : baseEnd_1059676 < baseStart_1059676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059735 : List Nat := [1, 1, 3, 3, 1, 2, 2, 4, 4]
def baseStart_1059735 : Nat := 118140960795 + 1059735 * 2 ^ 59
def prefixEnd_1059735 : Nat := 4983230072969 + 3 ^ 40 * 1059735 * 2
def baseEnd_1059735 : Nat := 241845965063340673617277

theorem tailTrace_1059735 : CollatzResearch.WordTrace tailWord_1059735 prefixEnd_1059735 241845965063340673617277 := by
  unfold tailWord_1059735
  simp only [CollatzResearch.WordTrace]
  refine ⟨38651710815768558173892659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25767807210512372115928439 38651710815768558173892659)
  ·
    refine ⟨57977566223652837260838989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38651710815768558173892659 57977566223652837260838989)
    ·
      refine ⟨21741587333869813972814621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57977566223652837260838989 21741587333869813972814621)
      ·
        refine ⟨8153095250201180239805483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21741587333869813972814621 8153095250201180239805483)
        ·
          refine ⟨12229642875301770359708225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8153095250201180239805483 12229642875301770359708225)
          ·
            refine ⟨9172232156476327769781169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12229642875301770359708225 9172232156476327769781169)
            ·
              refine ⟨6879174117357245827335877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9172232156476327769781169 6879174117357245827335877)
              ·
                refine ⟨1289845147004483592625477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6879174117357245827335877 1289845147004483592625477)
                ·
                  refine ⟨241845965063340673617277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1289845147004483592625477 241845965063340673617277)
                  ·
                    rfl

theorem cell21_1059735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 4].length) (baseStart_1059735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059735 prefixEnd_1059735 := by exact prefixLift 1059735
  have htrace : WordTrace (prefixWord ++ tailWord_1059735) baseStart_1059735 baseEnd_1059735 := by
    simpa [prefixWord, tailWord_1059735, baseEnd_1059735] using wordTrace_append hprefix tailTrace_1059735
  have hstable : (prefixWord ++ tailWord_1059735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059735).length < 2 ^ (prefixWord ++ tailWord_1059735).sum := by decide
  have hdescent : baseEnd_1059735 < baseStart_1059735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059738 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_1059738 : Nat := 118140960795 + 1059738 * 2 ^ 59
def prefixEnd_1059738 : Nat := 4983230072969 + 3 ^ 40 * 1059738 * 2
def baseEnd_1059738 : Nat := 241846649704213335067271

theorem tailTrace_1059738 : CollatzResearch.WordTrace tailWord_1059738 prefixEnd_1059738 241846649704213335067271 := by
  unfold tailWord_1059738
  simp only [CollatzResearch.WordTrace]
  refine ⟨9662955058689422421562967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25767880156505126457501245 9662955058689422421562967)
  ·
    refine ⟨14494432588034133632344451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9662955058689422421562967 14494432588034133632344451)
    ·
      refine ⟨21741648882051200448516677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14494432588034133632344451 21741648882051200448516677)
      ·
        refine ⟨4076559165384600084096877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21741648882051200448516677 4076559165384600084096877)
        ·
          refine ⟨1528709687019225031536329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4076559165384600084096877 1528709687019225031536329)
          ·
            refine ⟨1146532265264418773652247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1528709687019225031536329 1146532265264418773652247)
            ·
              refine ⟨1719798397896628160478371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146532265264418773652247 1719798397896628160478371)
              ·
                refine ⟨2579697596844942240717557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719798397896628160478371 2579697596844942240717557)
                ·
                  refine ⟨241846649704213335067271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2579697596844942240717557 241846649704213335067271)
                  ·
                    rfl

theorem cell21_1059738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_1059738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059738 prefixEnd_1059738 := by exact prefixLift 1059738
  have htrace : WordTrace (prefixWord ++ tailWord_1059738) baseStart_1059738 baseEnd_1059738 := by
    simpa [prefixWord, tailWord_1059738, baseEnd_1059738] using wordTrace_append hprefix tailTrace_1059738
  have hstable : (prefixWord ++ tailWord_1059738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059738).length < 2 ^ (prefixWord ++ tailWord_1059738).sum := by decide
  have hdescent : baseEnd_1059738 < baseStart_1059738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059789 : List Nat := [1, 6, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1059789 : Nat := 118140960795 + 1059789 * 2 ^ 59
def prefixEnd_1059789 : Nat := 4983230072969 + 3 ^ 40 * 1059789 * 2
def baseEnd_1059789 : Nat := 241858288599048579717167

theorem tailTrace_1059789 : CollatzResearch.WordTrace tailWord_1059789 prefixEnd_1059789 241858288599048579717167 := by
  unfold tailWord_1059789
  simp only [CollatzResearch.WordTrace]
  refine ⟨38653680357572925396358421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25769120238381950264238947 38653680357572925396358421)
  ·
    refine ⟨1811891266761230877954301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38653680357572925396358421 1811891266761230877954301)
    ·
      refine ⟨679459225035461579232863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1811891266761230877954301 679459225035461579232863)
      ·
        refine ⟨1019188837553192368849295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679459225035461579232863 1019188837553192368849295)
        ·
          refine ⟨1528783256329788553273943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019188837553192368849295 1528783256329788553273943)
          ·
            refine ⟨2293174884494682829910915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528783256329788553273943 2293174884494682829910915)
            ·
              refine ⟨3439762326742024244866373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293174884494682829910915 3439762326742024244866373)
              ·
                refine ⟨644955436264129545912445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3439762326742024244866373 644955436264129545912445)
                ·
                  refine ⟨241858288599048579717167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644955436264129545912445 241858288599048579717167)
                  ·
                    rfl

theorem cell21_1059789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1059789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059789 prefixEnd_1059789 := by exact prefixLift 1059789
  have htrace : WordTrace (prefixWord ++ tailWord_1059789) baseStart_1059789 baseEnd_1059789 := by
    simpa [prefixWord, tailWord_1059789, baseEnd_1059789] using wordTrace_append hprefix tailTrace_1059789
  have hstable : (prefixWord ++ tailWord_1059789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059789).length < 2 ^ (prefixWord ++ tailWord_1059789).sum := by decide
  have hdescent : baseEnd_1059789 < baseStart_1059789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059811 : List Nat := [1, 1, 1, 6, 1, 1, 1, 5, 4]
def baseStart_1059811 : Nat := 118140960795 + 1059811 * 2 ^ 59
def prefixEnd_1059811 : Nat := 4983230072969 + 3 ^ 40 * 1059811 * 2
def baseEnd_1059811 : Nat := 241863309298781430350455

theorem tailTrace_1059811 : CollatzResearch.WordTrace tailWord_1059811 prefixEnd_1059811 241863309298781430350455 := by
  unfold tailWord_1059811
  simp only [CollatzResearch.WordTrace]
  refine ⟨38654482763493223153659287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25769655175662148769106191 38654482763493223153659287)
  ·
    refine ⟨57981724145239834730488931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38654482763493223153659287 57981724145239834730488931)
    ·
      refine ⟨86972586217859752095733397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57981724145239834730488931 86972586217859752095733397)
      ·
        refine ⟨4076839978962175879487503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86972586217859752095733397 4076839978962175879487503)
        ·
          refine ⟨6115259968443263819231255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4076839978962175879487503 6115259968443263819231255)
          ·
            refine ⟨9172889952664895728846883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6115259968443263819231255 9172889952664895728846883)
            ·
              refine ⟨13759334928997343593270325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9172889952664895728846883 13759334928997343593270325)
              ·
                refine ⟨1289937649593500961869093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13759334928997343593270325 1289937649593500961869093)
                ·
                  refine ⟨241863309298781430350455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1289937649593500961869093 241863309298781430350455)
                  ·
                    rfl

theorem cell21_1059811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 4].length) (baseStart_1059811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059811 prefixEnd_1059811 := by exact prefixLift 1059811
  have htrace : WordTrace (prefixWord ++ tailWord_1059811) baseStart_1059811 baseEnd_1059811 := by
    simpa [prefixWord, tailWord_1059811, baseEnd_1059811] using wordTrace_append hprefix tailTrace_1059811
  have hstable : (prefixWord ++ tailWord_1059811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059811).length < 2 ^ (prefixWord ++ tailWord_1059811).sum := by decide
  have hdescent : baseEnd_1059811 < baseStart_1059811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059901 : List Nat := [1, 4, 1, 3, 1, 2, 9]
def baseStart_1059901 : Nat := 118140960795 + 1059901 * 2 ^ 59
def prefixEnd_1059901 : Nat := 4983230072969 + 3 ^ 40 * 1059901 * 2
def baseEnd_1059901 : Nat := 26875983169440141538919

theorem tailTrace_1059901 : CollatzResearch.WordTrace tailWord_1059901 prefixEnd_1059901 26875983169440141538919 := by
  unfold tailWord_1059901
  simp only [CollatzResearch.WordTrace]
  refine ⟨38657765333167168524435557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25771843555444779016290371 38657765333167168524435557)
  ·
    refine ⟨7248330999968844098331667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38657765333167168524435557 7248330999968844098331667)
    ·
      refine ⟨10872496499953266147497501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7248330999968844098331667 10872496499953266147497501)
      ·
        refine ⟨4077186187482474805311563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10872496499953266147497501 4077186187482474805311563)
        ·
          refine ⟨6115779281223712207967345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4077186187482474805311563 6115779281223712207967345)
          ·
            refine ⟨4586834460917784155975509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6115779281223712207967345 4586834460917784155975509)
            ·
              refine ⟨26875983169440141538919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4586834460917784155975509 26875983169440141538919)
              ·
                rfl

theorem cell21_1059901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 9].length) (baseStart_1059901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059901 prefixEnd_1059901 := by exact prefixLift 1059901
  have htrace : WordTrace (prefixWord ++ tailWord_1059901) baseStart_1059901 baseEnd_1059901 := by
    simpa [prefixWord, tailWord_1059901, baseEnd_1059901] using wordTrace_append hprefix tailTrace_1059901
  have hstable : (prefixWord ++ tailWord_1059901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059901).length < 2 ^ (prefixWord ++ tailWord_1059901).sum := by decide
  have hdescent : baseEnd_1059901 < baseStart_1059901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059932 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 7]
def baseStart_1059932 : Nat := 118140960795 + 1059932 * 2 ^ 59
def prefixEnd_1059932 : Nat := 4983230072969 + 3 ^ 40 * 1059932 * 2
def baseEnd_1059932 : Nat := 241890923147312108833541

theorem tailTrace_1059932 : CollatzResearch.WordTrace tailWord_1059932 prefixEnd_1059932 241890923147312108833541 := by
  unfold tailWord_1059932
  simp only [CollatzResearch.WordTrace]
  refine ⟨19329447998027430409407025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25772597330703240545876033 19329447998027430409407025)
  ·
    refine ⟨14497085998520572807055269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19329447998027430409407025 14497085998520572807055269)
    ·
      refine ⟨2718203624722607401322863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14497085998520572807055269 2718203624722607401322863)
      ·
        refine ⟨4077305437083911101984295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2718203624722607401322863 4077305437083911101984295)
        ·
          refine ⟨6115958155625866652976443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4077305437083911101984295 6115958155625866652976443)
          ·
            refine ⟨9173937233438799979464665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6115958155625866652976443 9173937233438799979464665)
            ·
              refine ⟨6880452925079099984598499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9173937233438799979464665 6880452925079099984598499)
              ·
                refine ⟨10320679387618649976897749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6880452925079099984598499 10320679387618649976897749)
                ·
                  refine ⟨241890923147312108833541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10320679387618649976897749 241890923147312108833541)
                  ·
                    rfl

theorem cell21_1059932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_1059932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059932 prefixEnd_1059932 := by exact prefixLift 1059932
  have htrace : WordTrace (prefixWord ++ tailWord_1059932) baseStart_1059932 baseEnd_1059932 := by
    simpa [prefixWord, tailWord_1059932, baseEnd_1059932] using wordTrace_append hprefix tailTrace_1059932
  have hstable : (prefixWord ++ tailWord_1059932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059932).length < 2 ^ (prefixWord ++ tailWord_1059932).sum := by decide
  have hdescent : baseEnd_1059932 < baseStart_1059932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059977 : List Nat := [1, 2, 1, 1, 4, 3, 3, 6]
def baseStart_1059977 : Nat := 118140960795 + 1059977 * 2 ^ 59
def prefixEnd_1059977 : Nat := 4983230072969 + 3 ^ 40 * 1059977 * 2
def baseEnd_1059977 : Nat := 80633730920134010194483

theorem tailTrace_1059977 : CollatzResearch.WordTrace tailWord_1059977 prefixEnd_1059977 80633730920134010194483 := by
  unfold tailWord_1059977
  simp only [CollatzResearch.WordTrace]
  refine ⟨38660537280891833504202185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25773691520594555669468123 38660537280891833504202185)
  ·
    refine ⟨28995402960668875128151639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38660537280891833504202185 28995402960668875128151639)
    ·
      refine ⟨43493104441003312692227459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28995402960668875128151639 43493104441003312692227459)
      ·
        refine ⟨65239656661504969038341189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43493104441003312692227459 65239656661504969038341189)
        ·
          refine ⟨12232435624032181694688973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65239656661504969038341189 12232435624032181694688973)
          ·
            refine ⟨4587163359012068135508365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12232435624032181694688973 4587163359012068135508365)
            ·
              refine ⟨1720186259629525550815637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4587163359012068135508365 1720186259629525550815637)
              ·
                refine ⟨80633730920134010194483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1720186259629525550815637 80633730920134010194483)
                ·
                  rfl

theorem cell21_1059977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 6].length) (baseStart_1059977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1059977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1059977 prefixEnd_1059977 := by exact prefixLift 1059977
  have htrace : WordTrace (prefixWord ++ tailWord_1059977) baseStart_1059977 baseEnd_1059977 := by
    simpa [prefixWord, tailWord_1059977, baseEnd_1059977] using wordTrace_append hprefix tailTrace_1059977
  have hstable : (prefixWord ++ tailWord_1059977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059977).length < 2 ^ (prefixWord ++ tailWord_1059977).sum := by decide
  have hdescent : baseEnd_1059977 < baseStart_1059977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060025 : List Nat := [1, 2, 1, 4, 1, 3, 2, 4, 3]
def baseStart_1060025 : Nat := 118140960795 + 1060025 * 2 ^ 59
def prefixEnd_1060025 : Nat := 4983230072969 + 3 ^ 40 * 1060025 * 2
def baseEnd_1060025 : Nat := 241912147014364613783351

theorem tailTrace_1060025 : CollatzResearch.WordTrace tailWord_1060025 prefixEnd_1060025 241912147014364613783351 := by
  unfold tailWord_1060025
  simp only [CollatzResearch.WordTrace]
  refine ⟨38662287984717937701949529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25774858656478625134633019 38662287984717937701949529)
  ·
    refine ⟨28996715988538453276462147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38662287984717937701949529 28996715988538453276462147)
    ·
      refine ⟨43495073982807679914693221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28996715988538453276462147 43495073982807679914693221)
      ·
        refine ⟨8155326371776439984004979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43495073982807679914693221 8155326371776439984004979)
        ·
          refine ⟨12232989557664659976007469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8155326371776439984004979 12232989557664659976007469)
          ·
            refine ⟨4587371084124247491002801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12232989557664659976007469 4587371084124247491002801)
            ·
              refine ⟨3440528313093185618252101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4587371084124247491002801 3440528313093185618252101)
              ·
                refine ⟨645099058704972303422269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3440528313093185618252101 645099058704972303422269)
                ·
                  refine ⟨241912147014364613783351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645099058704972303422269 241912147014364613783351)
                  ·
                    rfl

theorem cell21_1060025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 3].length) (baseStart_1060025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060025 prefixEnd_1060025 := by exact prefixLift 1060025
  have htrace : WordTrace (prefixWord ++ tailWord_1060025) baseStart_1060025 baseEnd_1060025 := by
    simpa [prefixWord, tailWord_1060025, baseEnd_1060025] using wordTrace_append hprefix tailTrace_1060025
  have hstable : (prefixWord ++ tailWord_1060025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060025).length < 2 ^ (prefixWord ++ tailWord_1060025).sum := by decide
  have hdescent : baseEnd_1060025 < baseStart_1060025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060045 : List Nat := [1, 6, 2, 2, 1, 2, 2, 5]
def baseStart_1060045 : Nat := 118140960795 + 1060045 * 2 ^ 59
def prefixEnd_1060045 : Nat := 4983230072969 + 3 ^ 40 * 1060045 * 2
def baseEnd_1060045 : Nat := 80638903762283007816659

theorem tailTrace_1060045 : CollatzResearch.WordTrace tailWord_1060045 prefixEnd_1060045 80638903762283007816659 := by
  unfold tailWord_1060045
  simp only [CollatzResearch.WordTrace]
  refine ⟨38663017444645481117677589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25775344963096987411785059 38663017444645481117677589)
  ·
    refine ⟨1812328942717756927391137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38663017444645481117677589 1812328942717756927391137)
    ·
      refine ⟨1359246707038317695543353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1812328942717756927391137 1359246707038317695543353)
      ·
        refine ⟨1019435030278738271657515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1359246707038317695543353 1019435030278738271657515)
        ·
          refine ⟨1529152545418107407486273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019435030278738271657515 1529152545418107407486273)
          ·
            refine ⟨1146864409063580555614705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1529152545418107407486273 1146864409063580555614705)
            ·
              refine ⟨860148306797685416711029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1146864409063580555614705 860148306797685416711029)
              ·
                refine ⟨80638903762283007816659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 860148306797685416711029 80638903762283007816659)
                ·
                  rfl

theorem cell21_1060045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 5].length) (baseStart_1060045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060045 prefixEnd_1060045 := by exact prefixLift 1060045
  have htrace : WordTrace (prefixWord ++ tailWord_1060045) baseStart_1060045 baseEnd_1060045 := by
    simpa [prefixWord, tailWord_1060045, baseEnd_1060045] using wordTrace_append hprefix tailTrace_1060045
  have hstable : (prefixWord ++ tailWord_1060045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060045).length < 2 ^ (prefixWord ++ tailWord_1060045).sum := by decide
  have hdescent : baseEnd_1060045 < baseStart_1060045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060143 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 5]
def baseStart_1060143 : Nat := 118140960795 + 1060143 * 2 ^ 59
def prefixEnd_1060143 : Nat := 4983230072969 + 3 ^ 40 * 1060143 * 2
def baseEnd_1060143 : Nat := 241939076222022630816443

theorem tailTrace_1060143 : CollatzResearch.WordTrace tailWord_1060143 prefixEnd_1060143 241939076222022630816443 := by
  unfold tailWord_1060143
  simp only [CollatzResearch.WordTrace]
  refine ⟨38666591798290443854745083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25777727865526962569830055 38666591798290443854745083)
  ·
    refine ⟨57999887697435665782117625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38666591798290443854745083 57999887697435665782117625)
    ·
      refine ⟨43499915773076749336588219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57999887697435665782117625 43499915773076749336588219)
      ·
        refine ⟨65249873659615124004882329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43499915773076749336588219 65249873659615124004882329)
        ·
          refine ⟨48937405244711343003661747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65249873659615124004882329 48937405244711343003661747)
          ·
            refine ⟨73406107867067014505492621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48937405244711343003661747 73406107867067014505492621)
            ·
              refine ⟨27527290450150130439559733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73406107867067014505492621 27527290450150130439559733)
              ·
                refine ⟨2580683479701574728708725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27527290450150130439559733 2580683479701574728708725)
                ·
                  refine ⟨241939076222022630816443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2580683479701574728708725 241939076222022630816443)
                  ·
                    rfl

theorem cell21_1060143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 5].length) (baseStart_1060143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060143 prefixEnd_1060143 := by exact prefixLift 1060143
  have htrace : WordTrace (prefixWord ++ tailWord_1060143) baseStart_1060143 baseEnd_1060143 := by
    simpa [prefixWord, tailWord_1060143, baseEnd_1060143] using wordTrace_append hprefix tailTrace_1060143
  have hstable : (prefixWord ++ tailWord_1060143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060143).length < 2 ^ (prefixWord ++ tailWord_1060143).sum := by decide
  have hdescent : baseEnd_1060143 < baseStart_1060143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060146 : List Nat := [3, 2, 1, 1, 4, 3, 1, 6]
def baseStart_1060146 : Nat := 118140960795 + 1060146 * 2 ^ 59
def prefixEnd_1060146 : Nat := 4983230072969 + 3 ^ 40 * 1060146 * 2
def baseEnd_1060146 : Nat := 80646586954298430755479

theorem tailTrace_1060146 : CollatzResearch.WordTrace tailWord_1060146 prefixEnd_1060146 80646586954298430755479 := by
  unfold tailWord_1060146
  simp only [CollatzResearch.WordTrace]
  refine ⟨9666675304319893841776073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25777800811519716911402861 9666675304319893841776073)
  ·
    refine ⟨7250006478239920381332055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9666675304319893841776073 7250006478239920381332055)
    ·
      refine ⟨10875009717359880571998083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7250006478239920381332055 10875009717359880571998083)
      ·
        refine ⟨16312514576039820857997125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10875009717359880571998083 16312514576039820857997125)
        ·
          refine ⟨3058596483007466410874461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16312514576039820857997125 3058596483007466410874461)
          ·
            refine ⟨1146973681127799904077923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3058596483007466410874461 1146973681127799904077923)
            ·
              refine ⟨1720460521691699856116885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146973681127799904077923 1720460521691699856116885)
              ·
                refine ⟨80646586954298430755479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1720460521691699856116885 80646586954298430755479)
                ·
                  rfl

theorem cell21_1060146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_1060146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060146 prefixEnd_1060146 := by exact prefixLift 1060146
  have htrace : WordTrace (prefixWord ++ tailWord_1060146) baseStart_1060146 baseEnd_1060146 := by
    simpa [prefixWord, tailWord_1060146, baseEnd_1060146] using wordTrace_append hprefix tailTrace_1060146
  have hstable : (prefixWord ++ tailWord_1060146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060146).length < 2 ^ (prefixWord ++ tailWord_1060146).sum := by decide
  have hdescent : baseEnd_1060146 < baseStart_1060146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060174 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_1060174 : Nat := 118140960795 + 1060174 * 2 ^ 59
def prefixEnd_1060174 : Nat := 4983230072969 + 3 ^ 40 * 1060174 * 2
def baseEnd_1060174 : Nat := 241946150844373465799713

theorem tailTrace_1060174 : CollatzResearch.WordTrace tailWord_1060174 prefixEnd_1060174 241946150844373465799713 := by
  unfold tailWord_1060174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4833465307647267018640447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25778481640785424099415717 4833465307647267018640447)
  ·
    refine ⟨7250197961470900527960671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4833465307647267018640447 7250197961470900527960671)
    ·
      refine ⟨10875296942206350791941007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7250197961470900527960671 10875296942206350791941007)
      ·
        refine ⟨16312945413309526187911511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10875296942206350791941007 16312945413309526187911511)
        ·
          refine ⟨24469418119964289281867267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16312945413309526187911511 24469418119964289281867267)
          ·
            refine ⟨36704127179946433922800901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24469418119964289281867267 36704127179946433922800901)
            ·
              refine ⟨6882023846239956360525169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36704127179946433922800901 6882023846239956360525169)
              ·
                refine ⟨5161517884679967270393877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6882023846239956360525169 5161517884679967270393877)
                ·
                  refine ⟨241946150844373465799713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5161517884679967270393877 241946150844373465799713)
                  ·
                    rfl

theorem cell21_1060174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_1060174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060174 prefixEnd_1060174 := by exact prefixLift 1060174
  have htrace : WordTrace (prefixWord ++ tailWord_1060174) baseStart_1060174 baseEnd_1060174 := by
    simpa [prefixWord, tailWord_1060174, baseEnd_1060174] using wordTrace_append hprefix tailTrace_1060174
  have hstable : (prefixWord ++ tailWord_1060174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060174).length < 2 ^ (prefixWord ++ tailWord_1060174).sum := by decide
  have hdescent : baseEnd_1060174 < baseStart_1060174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060177 : List Nat := [1, 2, 2, 1, 4, 1, 4, 3, 3]
def baseStart_1060177 : Nat := 118140960795 + 1060177 * 2 ^ 59
def prefixEnd_1060177 : Nat := 4983230072969 + 3 ^ 40 * 1060177 * 2
def baseEnd_1060177 : Nat := 241946835485246127249707

theorem tailTrace_1060177 : CollatzResearch.WordTrace tailWord_1060177 prefixEnd_1060177 241946835485246127249707 := by
  unfold tailWord_1060177
  simp only [CollatzResearch.WordTrace]
  refine ⟨38667831880167267661482785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25778554586778178440988523 38667831880167267661482785)
  ·
    refine ⟨29000873910125450746112089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38667831880167267661482785 29000873910125450746112089)
    ·
      refine ⟨21750655432594088059584067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29000873910125450746112089 21750655432594088059584067)
      ·
        refine ⟨32625983148891132089376101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21750655432594088059584067 32625983148891132089376101)
        ·
          refine ⟨6117371840417087266758019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32625983148891132089376101 6117371840417087266758019)
          ·
            refine ⟨9176057760625630900137029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6117371840417087266758019 9176057760625630900137029)
            ·
              refine ⟨1720510830117305793775693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9176057760625630900137029 1720510830117305793775693)
              ·
                refine ⟨645191561293989672665885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1720510830117305793775693 645191561293989672665885)
                ·
                  refine ⟨241946835485246127249707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645191561293989672665885 241946835485246127249707)
                  ·
                    rfl

theorem cell21_1060177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 3].length) (baseStart_1060177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060177 prefixEnd_1060177 := by exact prefixLift 1060177
  have htrace : WordTrace (prefixWord ++ tailWord_1060177) baseStart_1060177 baseEnd_1060177 := by
    simpa [prefixWord, tailWord_1060177, baseEnd_1060177] using wordTrace_append hprefix tailTrace_1060177
  have hstable : (prefixWord ++ tailWord_1060177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060177).length < 2 ^ (prefixWord ++ tailWord_1060177).sum := by decide
  have hdescent : baseEnd_1060177 < baseStart_1060177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060219 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 5]
def baseStart_1060219 : Nat := 118140960795 + 1060219 * 2 ^ 59
def prefixEnd_1060219 : Nat := 4983230072969 + 3 ^ 40 * 1060219 * 2
def baseEnd_1060219 : Nat := 241956420457463387549621

theorem tailTrace_1060219 : CollatzResearch.WordTrace tailWord_1060219 prefixEnd_1060219 241956420457463387549621 := by
  unfold tailWord_1060219
  simp only [CollatzResearch.WordTrace]
  refine ⟨38669363746015108834511711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25779575830676739223007807 38669363746015108834511711)
  ·
    refine ⟨58004045619022663251767567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38669363746015108834511711 58004045619022663251767567)
    ·
      refine ⟨87006068428533994877651351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58004045619022663251767567 87006068428533994877651351)
      ·
        refine ⟨130509102642800992316477027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87006068428533994877651351 130509102642800992316477027)
        ·
          refine ⟨195763653964201488474715541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130509102642800992316477027 195763653964201488474715541)
          ·
            refine ⟨9176421279571944772252291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 195763653964201488474715541 9176421279571944772252291)
            ·
              refine ⟨13764631919357917158378437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9176421279571944772252291 13764631919357917158378437)
              ·
                refine ⟨2580868484879609467195957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13764631919357917158378437 2580868484879609467195957)
                ·
                  refine ⟨241956420457463387549621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2580868484879609467195957 241956420457463387549621)
                  ·
                    rfl

theorem cell21_1060219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 5].length) (baseStart_1060219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060219 prefixEnd_1060219 := by exact prefixLift 1060219
  have htrace : WordTrace (prefixWord ++ tailWord_1060219) baseStart_1060219 baseEnd_1060219 := by
    simpa [prefixWord, tailWord_1060219, baseEnd_1060219] using wordTrace_append hprefix tailTrace_1060219
  have hstable : (prefixWord ++ tailWord_1060219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060219).length < 2 ^ (prefixWord ++ tailWord_1060219).sum := by decide
  have hdescent : baseEnd_1060219 < baseStart_1060219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060250 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_1060250 : Nat := 118140960795 + 1060250 * 2 ^ 59
def prefixEnd_1060250 : Nat := 4983230072969 + 3 ^ 40 * 1060250 * 2
def baseEnd_1060250 : Nat := 241963495079814222532891

theorem tailTrace_1060250 : CollatzResearch.WordTrace tailWord_1060250 prefixEnd_1060250 241963495079814222532891 := by
  unfold tailWord_1060250
  simp only [CollatzResearch.WordTrace]
  refine ⟨9667623602225700282222551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25780329605935200752593469 9667623602225700282222551)
  ·
    refine ⟨14501435403338550423333827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9667623602225700282222551 14501435403338550423333827)
    ·
      refine ⟨21752153105007825635000741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14501435403338550423333827 21752153105007825635000741)
      ·
        refine ⟨4078528707188967306562639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21752153105007825635000741 4078528707188967306562639)
        ·
          refine ⟨6117793060783450959843959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4078528707188967306562639 6117793060783450959843959)
          ·
            refine ⟨9176689591175176439765939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6117793060783450959843959 9176689591175176439765939)
            ·
              refine ⟨13765034386762764659648909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9176689591175176439765939 13765034386762764659648909)
              ·
                refine ⟨5161887895036036747368341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13765034386762764659648909 5161887895036036747368341)
                ·
                  refine ⟨241963495079814222532891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5161887895036036747368341 241963495079814222532891)
                  ·
                    rfl

theorem cell21_1060250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_1060250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060250 prefixEnd_1060250 := by exact prefixLift 1060250
  have htrace : WordTrace (prefixWord ++ tailWord_1060250) baseStart_1060250 baseEnd_1060250 := by
    simpa [prefixWord, tailWord_1060250, baseEnd_1060250] using wordTrace_append hprefix tailTrace_1060250
  have hstable : (prefixWord ++ tailWord_1060250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060250).length < 2 ^ (prefixWord ++ tailWord_1060250).sum := by decide
  have hdescent : baseEnd_1060250 < baseStart_1060250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060253 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 5]
def baseStart_1060253 : Nat := 118140960795 + 1060253 * 2 ^ 59
def prefixEnd_1060253 : Nat := 4983230072969 + 3 ^ 40 * 1060253 * 2
def baseEnd_1060253 : Nat := 241964179720686883982885

theorem tailTrace_1060253 : CollatzResearch.WordTrace tailWord_1060253 prefixEnd_1060253 241964179720686883982885 := by
  unfold tailWord_1060253
  simp only [CollatzResearch.WordTrace]
  refine ⟨38670603827891932641249413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25780402551927955094166275 38670603827891932641249413)
  ·
    refine ⟨7250738217729737370234265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38670603827891932641249413 7250738217729737370234265)
    ·
      refine ⟨5438053663297303027675699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7250738217729737370234265 5438053663297303027675699)
      ·
        refine ⟨8157080494945954541513549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5438053663297303027675699 8157080494945954541513549)
        ·
          refine ⟨3058905185604732953067581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8157080494945954541513549 3058905185604732953067581)
          ·
            refine ⟨1147089444601774857400343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3058905185604732953067581 1147089444601774857400343)
            ·
              refine ⟨1720634166902662286100515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147089444601774857400343 1720634166902662286100515)
              ·
                refine ⟨2580951250353993429150773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1720634166902662286100515 2580951250353993429150773)
                ·
                  refine ⟨241964179720686883982885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2580951250353993429150773 241964179720686883982885)
                  ·
                    rfl

theorem cell21_1060253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_1060253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060253 prefixEnd_1060253 := by exact prefixLift 1060253
  have htrace : WordTrace (prefixWord ++ tailWord_1060253) baseStart_1060253 baseEnd_1060253 := by
    simpa [prefixWord, tailWord_1060253, baseEnd_1060253] using wordTrace_append hprefix tailTrace_1060253
  have hstable : (prefixWord ++ tailWord_1060253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060253).length < 2 ^ (prefixWord ++ tailWord_1060253).sum := by decide
  have hdescent : baseEnd_1060253 < baseStart_1060253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060371 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 5]
def baseStart_1060371 : Nat := 118140960795 + 1060371 * 2 ^ 59
def prefixEnd_1060371 : Nat := 4983230072969 + 3 ^ 40 * 1060371 * 2
def baseEnd_1060371 : Nat := 241991108928344901015977

theorem tailTrace_1060371 : CollatzResearch.WordTrace tailWord_1060371 prefixEnd_1060371 241991108928344901015977 := by
  unfold tailWord_1060371
  simp only [CollatzResearch.WordTrace]
  refine ⟨38674907641464438794044967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25783271760976292529363311 38674907641464438794044967)
  ·
    refine ⟨58012361462196658191067451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38674907641464438794044967 58012361462196658191067451)
    ·
      refine ⟨87018542193294987286601177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58012361462196658191067451 87018542193294987286601177)
      ·
        refine ⟨65263906644971240464950883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87018542193294987286601177 65263906644971240464950883)
        ·
          refine ⟨97895859967456860697426325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65263906644971240464950883 97895859967456860697426325)
          ·
            refine ⟨4588868435974540345191859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97895859967456860697426325 4588868435974540345191859)
            ·
              refine ⟨6883302653961810517787789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4588868435974540345191859 6883302653961810517787789)
              ·
                refine ⟨2581238495235678944170421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6883302653961810517787789 2581238495235678944170421)
                ·
                  refine ⟨241991108928344901015977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2581238495235678944170421 241991108928344901015977)
                  ·
                    rfl

theorem cell21_1060371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 5].length) (baseStart_1060371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060371 prefixEnd_1060371 := by exact prefixLift 1060371
  have htrace : WordTrace (prefixWord ++ tailWord_1060371) baseStart_1060371 baseEnd_1060371 := by
    simpa [prefixWord, tailWord_1060371, baseEnd_1060371] using wordTrace_append hprefix tailTrace_1060371
  have hstable : (prefixWord ++ tailWord_1060371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060371).length < 2 ^ (prefixWord ++ tailWord_1060371).sum := by decide
  have hdescent : baseEnd_1060371 < baseStart_1060371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060405 : List Nat := [1, 3, 3, 1, 1, 3, 3, 3, 3]
def baseStart_1060405 : Nat := 118140960795 + 1060405 * 2 ^ 59
def prefixEnd_1060405 : Nat := 4983230072969 + 3 ^ 40 * 1060405 * 2
def baseEnd_1060405 : Nat := 241998868191568397449241

theorem tailTrace_1060405 : CollatzResearch.WordTrace tailWord_1060405 prefixEnd_1060405 241998868191568397449241 := by
  unfold tailWord_1060405
  simp only [CollatzResearch.WordTrace]
  refine ⟨38676147723341262600782669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25784098482227508400521779 38676147723341262600782669)
  ·
    refine ⟨14503555396252973475293501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38676147723341262600782669 14503555396252973475293501)
    ·
      refine ⟨5438833273594865053235063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14503555396252973475293501 5438833273594865053235063)
      ·
        refine ⟨8158249910392297579852595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5438833273594865053235063 8158249910392297579852595)
        ·
          refine ⟨12237374865588446369778893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8158249910392297579852595 12237374865588446369778893)
          ·
            refine ⟨4589015574595667388667085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12237374865588446369778893 4589015574595667388667085)
            ·
              refine ⟨1720880840473375270750157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4589015574595667388667085 1720880840473375270750157)
              ·
                refine ⟨645330315177515726531309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1720880840473375270750157 645330315177515726531309)
                ·
                  refine ⟨241998868191568397449241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645330315177515726531309 241998868191568397449241)
                  ·
                    rfl

theorem cell21_1060405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_1060405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060405 prefixEnd_1060405 := by exact prefixLift 1060405
  have htrace : WordTrace (prefixWord ++ tailWord_1060405) baseStart_1060405 baseEnd_1060405 := by
    simpa [prefixWord, tailWord_1060405, baseEnd_1060405] using wordTrace_append hprefix tailTrace_1060405
  have hstable : (prefixWord ++ tailWord_1060405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060405).length < 2 ^ (prefixWord ++ tailWord_1060405).sum := by decide
  have hdescent : baseEnd_1060405 < baseStart_1060405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060481 : List Nat := [1, 2, 4, 2, 1, 3, 1, 4, 3]
def baseStart_1060481 : Nat := 118140960795 + 1060481 * 2 ^ 59
def prefixEnd_1060481 : Nat := 4983230072969 + 3 ^ 40 * 1060481 * 2
def baseEnd_1060481 : Nat := 242016212427009154182419

theorem tailTrace_1060481 : CollatzResearch.WordTrace tailWord_1060481 prefixEnd_1060481 242016212427009154182419 := by
  unfold tailWord_1060481
  simp only [CollatzResearch.WordTrace]
  refine ⟨38678919671065927580549297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25785946447377285053699531 38678919671065927580549297)
  ·
    refine ⟨29009189753299445685411973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38678919671065927580549297 29009189753299445685411973)
    ·
      refine ⟨5439223078743646066014745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29009189753299445685411973 5439223078743646066014745)
      ·
        refine ⟨4079417309057734549511059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5439223078743646066014745 4079417309057734549511059)
        ·
          refine ⟨6119125963586601824266589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4079417309057734549511059 6119125963586601824266589)
          ·
            refine ⟨2294672236344975684099971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6119125963586601824266589 2294672236344975684099971)
            ·
              refine ⟨3442008354517463526149957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294672236344975684099971 3442008354517463526149957)
              ·
                refine ⟨645376566472024411153117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3442008354517463526149957 645376566472024411153117)
                ·
                  refine ⟨242016212427009154182419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645376566472024411153117 242016212427009154182419)
                  ·
                    rfl

theorem cell21_1060481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 3].length) (baseStart_1060481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060481 prefixEnd_1060481 := by exact prefixLift 1060481
  have htrace : WordTrace (prefixWord ++ tailWord_1060481) baseStart_1060481 baseEnd_1060481 := by
    simpa [prefixWord, tailWord_1060481, baseEnd_1060481] using wordTrace_append hprefix tailTrace_1060481
  have hstable : (prefixWord ++ tailWord_1060481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060481).length < 2 ^ (prefixWord ++ tailWord_1060481).sum := by decide
  have hdescent : baseEnd_1060481 < baseStart_1060481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060526 : List Nat := [4, 1, 4, 1, 2, 1, 8]
def baseStart_1060526 : Nat := 118140960795 + 1060526 * 2 ^ 59
def prefixEnd_1060526 : Nat := 4983230072969 + 3 ^ 40 * 1060526 * 2
def baseEnd_1060526 : Nat := 26891831337788786214703

theorem tailTrace_1060526 : CollatzResearch.WordTrace tailWord_1060526 prefixEnd_1060526 26891831337788786214703 := by
  unfold tailWord_1060526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4835070119487862533242179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25787040637268600177291621 4835070119487862533242179)
  ·
    refine ⟨7252605179231793799863269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4835070119487862533242179 7252605179231793799863269)
    ·
      refine ⟨1359863471105961337474363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7252605179231793799863269 1359863471105961337474363)
      ·
        refine ⟨2039795206658942006211545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359863471105961337474363 2039795206658942006211545)
        ·
          refine ⟨1529846404994206504658659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2039795206658942006211545 1529846404994206504658659)
          ·
            refine ⟨2294769607491309756987989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529846404994206504658659 2294769607491309756987989)
            ·
              refine ⟨26891831337788786214703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2294769607491309756987989 26891831337788786214703)
              ·
                rfl

theorem cell21_1060526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 8].length) (baseStart_1060526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060526 prefixEnd_1060526 := by exact prefixLift 1060526
  have htrace : WordTrace (prefixWord ++ tailWord_1060526) baseStart_1060526 baseEnd_1060526 := by
    simpa [prefixWord, tailWord_1060526, baseEnd_1060526] using wordTrace_append hprefix tailTrace_1060526
  have hstable : (prefixWord ++ tailWord_1060526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060526).length < 2 ^ (prefixWord ++ tailWord_1060526).sum := by decide
  have hdescent : baseEnd_1060526 < baseStart_1060526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060540 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 5]
def baseStart_1060540 : Nat := 118140960795 + 1060540 * 2 ^ 59
def prefixEnd_1060540 : Nat := 4983230072969 + 3 ^ 40 * 1060540 * 2
def baseEnd_1060540 : Nat := 242029677030838162698965

theorem tailTrace_1060540 : CollatzResearch.WordTrace tailWord_1060540 prefixEnd_1060540 242029677030838162698965 := by
  unfold tailWord_1060540
  simp only [CollatzResearch.WordTrace]
  refine ⟨19340535788926090328473537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25787381051901453771298049 19340535788926090328473537)
  ·
    refine ⟨14505401841694567746355153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19340535788926090328473537 14505401841694567746355153)
    ·
      refine ⟨10879051381270925809766365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14505401841694567746355153 10879051381270925809766365)
      ·
        refine ⟨4079644267976597178662387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10879051381270925809766365 4079644267976597178662387)
        ·
          refine ⟨6119466401964895767993581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4079644267976597178662387 6119466401964895767993581)
          ·
            refine ⟨2294799900736835912997593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6119466401964895767993581 2294799900736835912997593)
            ·
              refine ⟨1721099925552626934748195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2294799900736835912997593 1721099925552626934748195)
              ·
                refine ⟨2581649888328940402122293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1721099925552626934748195 2581649888328940402122293)
                ·
                  refine ⟨242029677030838162698965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2581649888328940402122293 242029677030838162698965)
                  ·
                    rfl

theorem cell21_1060540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_1060540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060540 prefixEnd_1060540 := by exact prefixLift 1060540
  have htrace : WordTrace (prefixWord ++ tailWord_1060540) baseStart_1060540 baseEnd_1060540 := by
    simpa [prefixWord, tailWord_1060540, baseEnd_1060540] using wordTrace_append hprefix tailTrace_1060540
  have hstable : (prefixWord ++ tailWord_1060540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060540).length < 2 ^ (prefixWord ++ tailWord_1060540).sum := by decide
  have hdescent : baseEnd_1060540 < baseStart_1060540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060557 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1060557 : Nat := 118140960795 + 1060557 * 2 ^ 59
def prefixEnd_1060557 : Nat := 4983230072969 + 3 ^ 40 * 1060557 * 2
def baseEnd_1060557 : Nat := 242033556662449910915597

theorem tailTrace_1060557 : CollatzResearch.WordTrace tailWord_1060557 prefixEnd_1060557 242033556662449910915597 := by
  unfold tailWord_1060557
  simp only [CollatzResearch.WordTrace]
  refine ⟨38681691618790592560315925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25787794412527061706877283 38681691618790592560315925)
  ·
    refine ⟨1813204294630809026264809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38681691618790592560315925 1813204294630809026264809)
    ·
      refine ⟨1359903220973106769698607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1813204294630809026264809 1359903220973106769698607)
      ·
        refine ⟨2039854831459660154547911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359903220973106769698607 2039854831459660154547911)
        ·
          refine ⟨3059782247189490231821867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2039854831459660154547911 3059782247189490231821867)
          ·
            refine ⟨4589673370784235347732801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059782247189490231821867 4589673370784235347732801)
            ·
              refine ⟨3442255028088176510799601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4589673370784235347732801 3442255028088176510799601)
              ·
                refine ⟨2581691271066132383099701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3442255028088176510799601 2581691271066132383099701)
                ·
                  refine ⟨242033556662449910915597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2581691271066132383099701 242033556662449910915597)
                  ·
                    rfl

theorem cell21_1060557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1060557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060557 prefixEnd_1060557 := by exact prefixLift 1060557
  have htrace : WordTrace (prefixWord ++ tailWord_1060557) baseStart_1060557 baseEnd_1060557 := by
    simpa [prefixWord, tailWord_1060557, baseEnd_1060557] using wordTrace_append hprefix tailTrace_1060557
  have hstable : (prefixWord ++ tailWord_1060557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060557).length < 2 ^ (prefixWord ++ tailWord_1060557).sum := by decide
  have hdescent : baseEnd_1060557 < baseStart_1060557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060568 : List Nat := [2, 1, 2, 2, 3, 1, 3, 7]
def baseStart_1060568 : Nat := 118140960795 + 1060568 * 2 ^ 59
def prefixEnd_1060568 : Nat := 4983230072969 + 3 ^ 40 * 1060568 * 2
def baseEnd_1060568 : Nat := 80678689004105445410747

theorem tailTrace_1060568 : CollatzResearch.WordTrace tailWord_1060568 prefixEnd_1060568 80678689004105445410747 := by
  unfold tailWord_1060568
  simp only [CollatzResearch.WordTrace]
  refine ⟨19341046410875370719483179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25788061881167160959310905 19341046410875370719483179)
  ·
    refine ⟨29011569616313056079224769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19341046410875370719483179 29011569616313056079224769)
    ·
      refine ⟨21758677212234792059418577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29011569616313056079224769 21758677212234792059418577)
      ·
        refine ⟨16319007909176094044563933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21758677212234792059418577 16319007909176094044563933)
        ·
          refine ⟨6119627965941035266711475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16319007909176094044563933 6119627965941035266711475)
          ·
            refine ⟨9179441948911552900067213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6119627965941035266711475 9179441948911552900067213)
            ·
              refine ⟨3442290730841832337525205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9179441948911552900067213 3442290730841832337525205)
              ·
                refine ⟨80678689004105445410747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3442290730841832337525205 80678689004105445410747)
                ·
                  rfl

theorem cell21_1060568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_1060568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060568 prefixEnd_1060568 := by exact prefixLift 1060568
  have htrace : WordTrace (prefixWord ++ tailWord_1060568) baseStart_1060568 baseEnd_1060568 := by
    simpa [prefixWord, tailWord_1060568, baseEnd_1060568] using wordTrace_append hprefix tailTrace_1060568
  have hstable : (prefixWord ++ tailWord_1060568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060568).length < 2 ^ (prefixWord ++ tailWord_1060568).sum := by decide
  have hdescent : baseEnd_1060568 < baseStart_1060568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060599 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 5]
def baseStart_1060599 : Nat := 118140960795 + 1060599 * 2 ^ 59
def prefixEnd_1060599 : Nat := 4983230072969 + 3 ^ 40 * 1060599 * 2
def baseEnd_1060599 : Nat := 242043141634667171215511

theorem tailTrace_1060599 : CollatzResearch.WordTrace tailWord_1060599 prefixEnd_1060599 242043141634667171215511 := by
  unfold tailWord_1060599
  simp only [CollatzResearch.WordTrace]
  refine ⟨38683223484638433733344851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25788815656425622488896567 38683223484638433733344851)
  ·
    refine ⟨58024835226957650600017277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38683223484638433733344851 58024835226957650600017277)
    ·
      refine ⟨21759313210109118975006479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58024835226957650600017277 21759313210109118975006479)
      ·
        refine ⟨32638969815163678462509719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21759313210109118975006479 32638969815163678462509719)
        ·
          refine ⟨48958454722745517693764579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32638969815163678462509719 48958454722745517693764579)
          ·
            refine ⟨73437682084118276540646869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48958454722745517693764579 73437682084118276540646869)
            ·
              refine ⟨1721195673846522106421411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 73437682084118276540646869 1721195673846522106421411)
              ·
                refine ⟨2581793510769783159632117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1721195673846522106421411 2581793510769783159632117)
                ·
                  refine ⟨242043141634667171215511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2581793510769783159632117 242043141634667171215511)
                  ·
                    rfl

theorem cell21_1060599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 5].length) (baseStart_1060599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060599 prefixEnd_1060599 := by exact prefixLift 1060599
  have htrace : WordTrace (prefixWord ++ tailWord_1060599) baseStart_1060599 baseEnd_1060599 := by
    simpa [prefixWord, tailWord_1060599, baseEnd_1060599] using wordTrace_append hprefix tailTrace_1060599
  have hstable : (prefixWord ++ tailWord_1060599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060599).length < 2 ^ (prefixWord ++ tailWord_1060599).sum := by decide
  have hdescent : baseEnd_1060599 < baseStart_1060599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060644 : List Nat := [2, 3, 1, 3, 2, 10]
def baseStart_1060644 : Nat := 118140960795 + 1060644 * 2 ^ 59
def prefixEnd_1060644 : Nat := 4983230072969 + 3 ^ 40 * 1060644 * 2
def baseEnd_1060644 : Nat := 8964941157324336776497

theorem tailTrace_1060644 : CollatzResearch.WordTrace tailWord_1060644 prefixEnd_1060644 8964941157324336776497 := by
  unfold tailWord_1060644
  simp only [CollatzResearch.WordTrace]
  refine ⟨19342432384737703209366493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25789909846316937612488657 19342432384737703209366493)
  ·
    refine ⟨7253412144276638703512435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19342432384737703209366493 7253412144276638703512435)
    ·
      refine ⟨10880118216414958055268653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7253412144276638703512435 10880118216414958055268653)
      ·
        refine ⟨4080044331155609270725745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10880118216414958055268653 4080044331155609270725745)
        ·
          refine ⟨3060033248366706953044309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4080044331155609270725745 3060033248366706953044309)
          ·
            refine ⟨8964941157324336776497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3060033248366706953044309 8964941157324336776497)
            ·
              rfl

theorem cell21_1060644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 10].length) (baseStart_1060644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060644 prefixEnd_1060644 := by exact prefixLift 1060644
  have htrace : WordTrace (prefixWord ++ tailWord_1060644) baseStart_1060644 baseEnd_1060644 := by
    simpa [prefixWord, tailWord_1060644, baseEnd_1060644] using wordTrace_append hprefix tailTrace_1060644
  have hstable : (prefixWord ++ tailWord_1060644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060644).length < 2 ^ (prefixWord ++ tailWord_1060644).sum := by decide
  have hdescent : baseEnd_1060644 < baseStart_1060644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060675 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 5]
def baseStart_1060675 : Nat := 118140960795 + 1060675 * 2 ^ 59
def prefixEnd_1060675 : Nat := 4983230072969 + 3 ^ 40 * 1060675 * 2
def baseEnd_1060675 : Nat := 242060485870107927948689

theorem tailTrace_1060675 : CollatzResearch.WordTrace tailWord_1060675 prefixEnd_1060675 242060485870107927948689 := by
  unfold tailWord_1060675
  simp only [CollatzResearch.WordTrace]
  refine ⟨38685995432363098713111479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25790663621575399142074319 38685995432363098713111479)
  ·
    refine ⟨58028993148544648069667219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38685995432363098713111479 58028993148544648069667219)
    ·
      refine ⟨87043489722816972104500829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58028993148544648069667219 87043489722816972104500829)
      ·
        refine ⟨32641308646056364539187811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87043489722816972104500829 32641308646056364539187811)
        ·
          refine ⟨48961962969084546808781717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32641308646056364539187811 48961962969084546808781717)
          ·
            refine ⟨2295092014175838131661643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48961962969084546808781717 2295092014175838131661643)
            ·
              refine ⟨3442638021263757197492465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295092014175838131661643 3442638021263757197492465)
              ·
                refine ⟨2581978515947817898119349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3442638021263757197492465 2581978515947817898119349)
                ·
                  refine ⟨242060485870107927948689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2581978515947817898119349 242060485870107927948689)
                  ·
                    rfl

theorem cell21_1060675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 5].length) (baseStart_1060675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060675 prefixEnd_1060675 := by exact prefixLift 1060675
  have htrace : WordTrace (prefixWord ++ tailWord_1060675) baseStart_1060675 baseEnd_1060675 := by
    simpa [prefixWord, tailWord_1060675, baseEnd_1060675] using wordTrace_append hprefix tailTrace_1060675
  have hstable : (prefixWord ++ tailWord_1060675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060675).length < 2 ^ (prefixWord ++ tailWord_1060675).sum := by decide
  have hdescent : baseEnd_1060675 < baseStart_1060675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060813 : List Nat := [1, 6, 3, 11]
def baseStart_1060813 : Nat := 118140960795 + 1060813 * 2 ^ 59
def prefixEnd_1060813 : Nat := 4983230072969 + 3 ^ 40 * 1060813 * 2
def baseEnd_1060813 : Nat := 996263289507203105549

theorem tailTrace_1060813 : CollatzResearch.WordTrace tailWord_1060813 prefixEnd_1060813 996263289507203105549 := by
  unfold tailWord_1060813
  simp only [CollatzResearch.WordTrace]
  refine ⟨38691028705863148281635093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25794019137242098854423395 38691028705863148281635093)
  ·
    refine ⟨1813641970587335075701645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38691028705863148281635093 1813641970587335075701645)
    ·
      refine ⟨680115738970250653388117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1813641970587335075701645 680115738970250653388117)
      ·
        refine ⟨996263289507203105549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 680115738970250653388117 996263289507203105549)
        ·
          rfl

theorem cell21_1060813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 11].length) (baseStart_1060813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060813 prefixEnd_1060813 := by exact prefixLift 1060813
  have htrace : WordTrace (prefixWord ++ tailWord_1060813) baseStart_1060813 baseEnd_1060813 := by
    simpa [prefixWord, tailWord_1060813, baseEnd_1060813] using wordTrace_append hprefix tailTrace_1060813
  have hstable : (prefixWord ++ tailWord_1060813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060813).length < 2 ^ (prefixWord ++ tailWord_1060813).sum := by decide
  have hdescent : baseEnd_1060813 < baseStart_1060813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060906 : List Nat := [3, 1, 4, 1, 2, 3, 2, 5]
def baseStart_1060906 : Nat := 118140960795 + 1060906 * 2 ^ 59
def prefixEnd_1060906 : Nat := 4983230072969 + 3 ^ 40 * 1060906 * 2
def baseEnd_1060906 : Nat := 80704401072434286532739

theorem tailTrace_1060906 : CollatzResearch.WordTrace tailWord_1060906 prefixEnd_1060906 80704401072434286532739 := by
  unfold tailWord_1060906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9673605173631556291192643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25796280463017483443180381 9673605173631556291192643)
  ·
    refine ⟨14510407760447334436788965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9673605173631556291192643 14510407760447334436788965)
    ·
      refine ⟨2720701455083875206897931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14510407760447334436788965 2720701455083875206897931)
      ·
        refine ⟨4081052182625812810346897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2720701455083875206897931 4081052182625812810346897)
        ·
          refine ⟨3060789136969359607760173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4081052182625812810346897 3060789136969359607760173)
          ·
            refine ⟨1147795926363509852910065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3060789136969359607760173 1147795926363509852910065)
            ·
              refine ⟨860846944772632389682549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1147795926363509852910065 860846944772632389682549)
              ·
                refine ⟨80704401072434286532739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 860846944772632389682549 80704401072434286532739)
                ·
                  rfl

theorem cell21_1060906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_1060906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060906 prefixEnd_1060906 := by exact prefixLift 1060906
  have htrace : WordTrace (prefixWord ++ tailWord_1060906) baseStart_1060906 baseEnd_1060906 := by
    simpa [prefixWord, tailWord_1060906, baseEnd_1060906] using wordTrace_append hprefix tailTrace_1060906
  have hstable : (prefixWord ++ tailWord_1060906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060906).length < 2 ^ (prefixWord ++ tailWord_1060906).sum := by decide
  have hdescent : baseEnd_1060906 < baseStart_1060906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060917 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 6]
def baseStart_1060917 : Nat := 118140960795 + 1060917 * 2 ^ 59
def prefixEnd_1060917 : Nat := 4983230072969 + 3 ^ 40 * 1060917 * 2
def baseEnd_1060917 : Nat := 242115713567169284914861

theorem tailTrace_1060917 : CollatzResearch.WordTrace tailWord_1060917 prefixEnd_1060917 242115713567169284914861 := by
  unfold tailWord_1060917
  simp only [CollatzResearch.WordTrace]
  refine ⟨38694821897486374043421005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25796547931657582695614003 38694821897486374043421005)
  ·
    refine ⟨14510558211557390266282877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38694821897486374043421005 14510558211557390266282877)
    ·
      refine ⟨5441459329334021349856079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14510558211557390266282877 5441459329334021349856079)
      ·
        refine ⟨8162188994001032024784119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5441459329334021349856079 8162188994001032024784119)
        ·
          refine ⟨12243283491001548037176179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8162188994001032024784119 12243283491001548037176179)
          ·
            refine ⟨18364925236502322055764269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12243283491001548037176179 18364925236502322055764269)
            ·
              refine ⟨6886846963688370770911601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18364925236502322055764269 6886846963688370770911601)
              ·
                refine ⟨5165135222766278078183701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6886846963688370770911601 5165135222766278078183701)
                ·
                  refine ⟨242115713567169284914861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5165135222766278078183701 242115713567169284914861)
                  ·
                    rfl

theorem cell21_1060917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_1060917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060917 prefixEnd_1060917 := by exact prefixLift 1060917
  have htrace : WordTrace (prefixWord ++ tailWord_1060917) baseStart_1060917 baseEnd_1060917 := by
    simpa [prefixWord, tailWord_1060917, baseEnd_1060917] using wordTrace_append hprefix tailTrace_1060917
  have hstable : (prefixWord ++ tailWord_1060917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060917).length < 2 ^ (prefixWord ++ tailWord_1060917).sum := by decide
  have hdescent : baseEnd_1060917 < baseStart_1060917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060996 : List Nat := [2, 3, 2, 1, 2, 1, 3, 4, 3]
def baseStart_1060996 : Nat := 118140960795 + 1060996 * 2 ^ 59
def prefixEnd_1060996 : Nat := 4983230072969 + 3 ^ 40 * 1060996 * 2
def baseEnd_1060996 : Nat := 242133742443482703098033

theorem tailTrace_1060996 : CollatzResearch.WordTrace tailWord_1060996 prefixEnd_1060996 242133742443482703098033 := by
  unfold tailWord_1060996
  simp only [CollatzResearch.WordTrace]
  refine ⟨19348851632100085267773421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25798468842800113690364561 19348851632100085267773421)
  ·
    refine ⟨7255819362037531975415033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19348851632100085267773421 7255819362037531975415033)
    ·
      refine ⟨5441864521528148981561275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7255819362037531975415033 5441864521528148981561275)
      ·
        refine ⟨8162796782292223472341913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5441864521528148981561275 8162796782292223472341913)
        ·
          refine ⟨6122097586719167604256435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8162796782292223472341913 6122097586719167604256435)
          ·
            refine ⟨9183146380078751406384653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6122097586719167604256435 9183146380078751406384653)
            ·
              refine ⟨3443679892529531777394245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9183146380078751406384653 3443679892529531777394245)
              ·
                refine ⟨645689979849287208261421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3443679892529531777394245 645689979849287208261421)
                ·
                  refine ⟨242133742443482703098033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645689979849287208261421 242133742443482703098033)
                  ·
                    rfl

theorem cell21_1060996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_1060996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1060996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1060996 prefixEnd_1060996 := by exact prefixLift 1060996
  have htrace : WordTrace (prefixWord ++ tailWord_1060996) baseStart_1060996 baseEnd_1060996 := by
    simpa [prefixWord, tailWord_1060996, baseEnd_1060996] using wordTrace_append hprefix tailTrace_1060996
  have hstable : (prefixWord ++ tailWord_1060996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060996).length < 2 ^ (prefixWord ++ tailWord_1060996).sum := by decide
  have hdescent : baseEnd_1060996 < baseStart_1060996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061010 : List Nat := [3, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_1061010 : Nat := 118140960795 + 1061010 * 2 ^ 59
def prefixEnd_1061010 : Nat := 4983230072969 + 3 ^ 40 * 1061010 * 2
def baseEnd_1061010 : Nat := 242136937434221789864671

theorem tailTrace_1061010 : CollatzResearch.WordTrace tailWord_1061010 prefixEnd_1061010 242136937434221789864671 := by
  unfold tailWord_1061010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9674553471537362731639121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25798809257432967284370989 9674553471537362731639121)
  ·
    refine ⟨7255915103653022048729341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9674553471537362731639121 7255915103653022048729341)
    ·
      refine ⟨2720968163869883268273503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7255915103653022048729341 2720968163869883268273503)
      ·
        refine ⟨4081452245804824902410255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2720968163869883268273503 4081452245804824902410255)
        ·
          refine ⟨6122178368707237353615383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081452245804824902410255 6122178368707237353615383)
          ·
            refine ⟨9183267553060856030423075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6122178368707237353615383 9183267553060856030423075)
            ·
              refine ⟨13774901329591284045634613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9183267553060856030423075 13774901329591284045634613)
              ·
                refine ⟨1291396999649182879278245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13774901329591284045634613 1291396999649182879278245)
                ·
                  refine ⟨242136937434221789864671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1291396999649182879278245 242136937434221789864671)
                  ·
                    rfl

theorem cell21_1061010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_1061010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061010 prefixEnd_1061010 := by exact prefixLift 1061010
  have htrace : WordTrace (prefixWord ++ tailWord_1061010) baseStart_1061010 baseEnd_1061010 := by
    simpa [prefixWord, tailWord_1061010, baseEnd_1061010] using wordTrace_append hprefix tailTrace_1061010
  have hstable : (prefixWord ++ tailWord_1061010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061010).length < 2 ^ (prefixWord ++ tailWord_1061010).sum := by decide
  have hdescent : baseEnd_1061010 < baseStart_1061010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061221 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 6]
def baseStart_1061221 : Nat := 118140960795 + 1061221 * 2 ^ 59
def prefixEnd_1061221 : Nat := 4983230072969 + 3 ^ 40 * 1061221 * 2
def baseEnd_1061221 : Nat := 242185090508932311847573

theorem tailTrace_1061221 : CollatzResearch.WordTrace tailWord_1061221 prefixEnd_1061221 242185090508932311847573 := by
  unfold tailWord_1061221
  simp only [CollatzResearch.WordTrace]
  refine ⟨38705909688385033962487517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25803939792256689308325011 38705909688385033962487517)
  ·
    refine ⟨14514716133144387735932819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38705909688385033962487517 14514716133144387735932819)
    ·
      refine ⟨21772074199716581603899229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14514716133144387735932819 21772074199716581603899229)
      ·
        refine ⟨8164527824893718101462211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21772074199716581603899229 8164527824893718101462211)
        ·
          refine ⟨12246791737340577152193317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8164527824893718101462211 12246791737340577152193317)
          ·
            refine ⟨2296273450751358216036247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12246791737340577152193317 2296273450751358216036247)
            ·
              refine ⟨3444410176127037324054371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2296273450751358216036247 3444410176127037324054371)
              ·
                refine ⟨5166615264190555986081557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3444410176127037324054371 5166615264190555986081557)
                ·
                  refine ⟨242185090508932311847573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5166615264190555986081557 242185090508932311847573)
                  ·
                    rfl

theorem cell21_1061221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_1061221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061221 prefixEnd_1061221 := by exact prefixLift 1061221
  have htrace : WordTrace (prefixWord ++ tailWord_1061221) baseStart_1061221 baseEnd_1061221 := by
    simpa [prefixWord, tailWord_1061221, baseEnd_1061221] using wordTrace_append hprefix tailTrace_1061221
  have hstable : (prefixWord ++ tailWord_1061221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061221).length < 2 ^ (prefixWord ++ tailWord_1061221).sum := by decide
  have hdescent : baseEnd_1061221 < baseStart_1061221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061224 : List Nat := [2, 1, 4, 2, 2, 1, 2, 4, 3]
def baseStart_1061224 : Nat := 118140960795 + 1061224 * 2 ^ 59
def prefixEnd_1061224 : Nat := 4983230072969 + 3 ^ 40 * 1061224 * 2
def baseEnd_1061224 : Nat := 242185775149804973297567

theorem tailTrace_1061224 : CollatzResearch.WordTrace tailWord_1061224 prefixEnd_1061224 242185775149804973297567 := by
  unfold tailWord_1061224
  simp only [CollatzResearch.WordTrace]
  refine ⟨19353009553687082737423363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25804012738249443649897817 19353009553687082737423363)
  ·
    refine ⟨29029514330530624106135045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19353009553687082737423363 29029514330530624106135045)
    ·
      refine ⟨5443033936974492019900321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29029514330530624106135045 5443033936974492019900321)
      ·
        refine ⟨4082275452730869014925241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5443033936974492019900321 4082275452730869014925241)
        ·
          refine ⟨3061706589548151761193931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4082275452730869014925241 3061706589548151761193931)
          ·
            refine ⟨4592559884322227641790897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3061706589548151761193931 4592559884322227641790897)
            ·
              refine ⟨3444419913241670731343173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4592559884322227641790897 3444419913241670731343173)
              ·
                refine ⟨645828733732813262126845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3444419913241670731343173 645828733732813262126845)
                ·
                  refine ⟨242185775149804973297567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645828733732813262126845 242185775149804973297567)
                  ·
                    rfl

theorem cell21_1061224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 3].length) (baseStart_1061224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061224 prefixEnd_1061224 := by exact prefixLift 1061224
  have htrace : WordTrace (prefixWord ++ tailWord_1061224) baseStart_1061224 baseEnd_1061224 := by
    simpa [prefixWord, tailWord_1061224, baseEnd_1061224] using wordTrace_append hprefix tailTrace_1061224
  have hstable : (prefixWord ++ tailWord_1061224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061224).length < 2 ^ (prefixWord ++ tailWord_1061224).sum := by decide
  have hdescent : baseEnd_1061224 < baseStart_1061224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061258 : List Nat := [3, 1, 2, 5, 1, 2, 1, 3, 3]
def baseStart_1061258 : Nat := 118140960795 + 1061258 * 2 ^ 59
def prefixEnd_1061258 : Nat := 4983230072969 + 3 ^ 40 * 1061258 * 2
def baseEnd_1061258 : Nat := 242193534413028469730831

theorem tailTrace_1061258 : CollatzResearch.WordTrace tailWord_1061258 prefixEnd_1061258 242193534413028469730831 := by
  unfold tailWord_1061258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9676814797312747320396107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25804839459500659521056285 9676814797312747320396107)
  ·
    refine ⟨14515222195969120980594161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9676814797312747320396107 14515222195969120980594161)
    ·
      refine ⟨10886416646976840735445621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14515222195969120980594161 10886416646976840735445621)
      ·
        refine ⟨1020601560654078818948027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10886416646976840735445621 1020601560654078818948027)
        ·
          refine ⟨1530902340981118228422041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020601560654078818948027 1530902340981118228422041)
          ·
            refine ⟨1148176755735838671316531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1530902340981118228422041 1148176755735838671316531)
            ·
              refine ⟨1722265133603758006974797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148176755735838671316531 1722265133603758006974797)
              ·
                refine ⟨645849425101409252615549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1722265133603758006974797 645849425101409252615549)
                ·
                  refine ⟨242193534413028469730831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645849425101409252615549 242193534413028469730831)
                  ·
                    rfl

theorem cell21_1061258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_1061258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061258 prefixEnd_1061258 := by exact prefixLift 1061258
  have htrace : WordTrace (prefixWord ++ tailWord_1061258) baseStart_1061258 baseEnd_1061258 := by
    simpa [prefixWord, tailWord_1061258, baseEnd_1061258] using wordTrace_append hprefix tailTrace_1061258
  have hstable : (prefixWord ++ tailWord_1061258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061258).length < 2 ^ (prefixWord ++ tailWord_1061258).sum := by decide
  have hdescent : baseEnd_1061258 < baseStart_1061258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061283 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 5]
def baseStart_1061283 : Nat := 118140960795 + 1061283 * 2 ^ 59
def prefixEnd_1061283 : Nat := 4983230072969 + 3 ^ 40 * 1061283 * 2
def baseEnd_1061283 : Nat := 242199239753633981814113

theorem tailTrace_1061283 : CollatzResearch.WordTrace tailWord_1061283 prefixEnd_1061283 242199239753633981814113 := by
  unfold tailWord_1061283
  simp only [CollatzResearch.WordTrace]
  refine ⟨38708171014160418551244503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25805447342773612367496335 38708171014160418551244503)
  ·
    refine ⟨58062256521240627826866755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38708171014160418551244503 58062256521240627826866755)
    ·
      refine ⟨87093384781860941740300133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58062256521240627826866755 87093384781860941740300133)
      ·
        refine ⟨16330009646598926576306275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87093384781860941740300133 16330009646598926576306275)
        ·
          refine ⟨24495014469898389864459413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16330009646598926576306275 24495014469898389864459413)
          ·
            refine ⟨1148203803276487024896535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24495014469898389864459413 1148203803276487024896535)
            ·
              refine ⟨1722305704914730537344803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148203803276487024896535 1722305704914730537344803)
              ·
                refine ⟨2583458557372095806017205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1722305704914730537344803 2583458557372095806017205)
                ·
                  refine ⟨242199239753633981814113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2583458557372095806017205 242199239753633981814113)
                  ·
                    rfl

theorem cell21_1061283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 5].length) (baseStart_1061283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061283 prefixEnd_1061283 := by exact prefixLift 1061283
  have htrace : WordTrace (prefixWord ++ tailWord_1061283) baseStart_1061283 baseEnd_1061283 := by
    simpa [prefixWord, tailWord_1061283, baseEnd_1061283] using wordTrace_append hprefix tailTrace_1061283
  have hstable : (prefixWord ++ tailWord_1061283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061283).length < 2 ^ (prefixWord ++ tailWord_1061283).sum := by decide
  have hdescent : baseEnd_1061283 < baseStart_1061283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061387 : List Nat := [1, 1, 1, 1, 7, 2, 8]
def baseStart_1061387 : Nat := 118140960795 + 1061387 * 2 ^ 59
def prefixEnd_1061387 : Nat := 4983230072969 + 3 ^ 40 * 1061387 * 2
def baseEnd_1061387 : Nat := 26913663774505879120063

theorem tailTrace_1061387 : CollatzResearch.WordTrace tailWord_1061387 prefixEnd_1061387 26913663774505879120063 := by
  unfold tailWord_1061387
  simp only [CollatzResearch.WordTrace]
  refine ⟨38711964205783644313030415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25807976137189096208686943 38711964205783644313030415)
  ·
    refine ⟨58067946308675466469545623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38711964205783644313030415 58067946308675466469545623)
    ·
      refine ⟨87101919463013199704318435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58067946308675466469545623 87101919463013199704318435)
      ·
        refine ⟨130652879194519799556477653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87101919463013199704318435 130652879194519799556477653)
        ·
          refine ⟨3062176856121557802104945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 130652879194519799556477653 3062176856121557802104945)
          ·
            refine ⟨2296632642091168351578709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3062176856121557802104945 2296632642091168351578709)
            ·
              refine ⟨26913663774505879120063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2296632642091168351578709 26913663774505879120063)
              ·
                rfl

theorem cell21_1061387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 8].length) (baseStart_1061387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061387 prefixEnd_1061387 := by exact prefixLift 1061387
  have htrace : WordTrace (prefixWord ++ tailWord_1061387) baseStart_1061387 baseEnd_1061387 := by
    simpa [prefixWord, tailWord_1061387, baseEnd_1061387] using wordTrace_append hprefix tailTrace_1061387
  have hstable : (prefixWord ++ tailWord_1061387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061387).length < 2 ^ (prefixWord ++ tailWord_1061387).sum := by decide
  have hdescent : baseEnd_1061387 < baseStart_1061387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061390 : List Nat := [4, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_1061390 : Nat := 118140960795 + 1061390 * 2 ^ 59
def prefixEnd_1061390 : Nat := 4983230072969 + 3 ^ 40 * 1061390 * 2
def baseEnd_1061390 : Nat := 242223658611425573530561

theorem tailTrace_1061390 : CollatzResearch.WordTrace tailWord_1061390 prefixEnd_1061390 242223658611425573530561 := by
  unfold tailWord_1061390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4839009203096596978173703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25808049083181850550259749 4839009203096596978173703)
  ·
    refine ⟨7258513804644895467260555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4839009203096596978173703 7258513804644895467260555)
    ·
      refine ⟨10887770706967343200890833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7258513804644895467260555 10887770706967343200890833)
      ·
        refine ⟨8165828030225507400668125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10887770706967343200890833 8165828030225507400668125)
        ·
          refine ⟨3062185511334565275250547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8165828030225507400668125 3062185511334565275250547)
          ·
            refine ⟨4593278267001847912875821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062185511334565275250547 4593278267001847912875821)
            ·
              refine ⟨1722479350125692967328433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4593278267001847912875821 1722479350125692967328433)
              ·
                refine ⟨1291859512594269725496325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1722479350125692967328433 1291859512594269725496325)
                ·
                  refine ⟨242223658611425573530561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1291859512594269725496325 242223658611425573530561)
                  ·
                    rfl

theorem cell21_1061390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_1061390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061390 prefixEnd_1061390 := by exact prefixLift 1061390
  have htrace : WordTrace (prefixWord ++ tailWord_1061390) baseStart_1061390 baseEnd_1061390 := by
    simpa [prefixWord, tailWord_1061390, baseEnd_1061390] using wordTrace_append hprefix tailTrace_1061390
  have hstable : (prefixWord ++ tailWord_1061390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061390).length < 2 ^ (prefixWord ++ tailWord_1061390).sum := by decide
  have hdescent : baseEnd_1061390 < baseStart_1061390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061401 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 9]
def baseStart_1061401 : Nat := 118140960795 + 1061401 * 2 ^ 59
def prefixEnd_1061401 : Nat := 4983230072969 + 3 ^ 40 * 1061401 * 2
def baseEnd_1061401 : Nat := 242226168961291998847205

theorem tailTrace_1061401 : CollatzResearch.WordTrace tailWord_1061401 prefixEnd_1061401 242226168961291998847205 := by
  unfold tailWord_1061401
  simp only [CollatzResearch.WordTrace]
  refine ⟨38712474827732924704040057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25808316551821949802693371 38712474827732924704040057)
  ·
    refine ⟨29034356120799693528030043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38712474827732924704040057 29034356120799693528030043)
    ·
      refine ⟨43551534181199540292045065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29034356120799693528030043 43551534181199540292045065)
      ·
        refine ⟨32663650635899655219033799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43551534181199540292045065 32663650635899655219033799)
        ·
          refine ⟨48995475953849482828550699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32663650635899655219033799 48995475953849482828550699)
          ·
            refine ⟨73493213930774224242826049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48995475953849482828550699 73493213930774224242826049)
            ·
              refine ⟨55119910448080668182119537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73493213930774224242826049 55119910448080668182119537)
              ·
                refine ⟨41339932836060501136589653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55119910448080668182119537 41339932836060501136589653)
                ·
                  refine ⟨242226168961291998847205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41339932836060501136589653 242226168961291998847205)
                  ·
                    rfl

theorem cell21_1061401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_1061401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061401 prefixEnd_1061401 := by exact prefixLift 1061401
  have htrace : WordTrace (prefixWord ++ tailWord_1061401) baseStart_1061401 baseEnd_1061401 := by
    simpa [prefixWord, tailWord_1061401, baseEnd_1061401] using wordTrace_append hprefix tailTrace_1061401
  have hstable : (prefixWord ++ tailWord_1061401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061401).length < 2 ^ (prefixWord ++ tailWord_1061401).sum := by decide
  have hdescent : baseEnd_1061401 < baseStart_1061401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061432 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 8]
def baseStart_1061432 : Nat := 118140960795 + 1061432 * 2 ^ 59
def prefixEnd_1061432 : Nat := 4983230072969 + 3 ^ 40 * 1061432 * 2
def baseEnd_1061432 : Nat := 242233243583642833830475

theorem tailTrace_1061432 : CollatzResearch.WordTrace tailWord_1061432 prefixEnd_1061432 242233243583642833830475 := by
  unfold tailWord_1061432
  simp only [CollatzResearch.WordTrace]
  refine ⟨19356802745310308499209275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25809070327080411332279033 19356802745310308499209275)
  ·
    refine ⟨29035204117965462748813913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19356802745310308499209275 29035204117965462748813913)
    ·
      refine ⟨21776403088474097061610435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29035204117965462748813913 21776403088474097061610435)
      ·
        refine ⟨32664604632711145592415653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21776403088474097061610435 32664604632711145592415653)
        ·
          refine ⟨6124613368633339798577935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32664604632711145592415653 6124613368633339798577935)
          ·
            refine ⟨9186920052950009697866903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6124613368633339798577935 9186920052950009697866903)
            ·
              refine ⟨13780380079425014546800355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9186920052950009697866903 13780380079425014546800355)
              ·
                refine ⟨20670570119137521820200533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13780380079425014546800355 20670570119137521820200533)
                ·
                  refine ⟨242233243583642833830475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20670570119137521820200533 242233243583642833830475)
                  ·
                    rfl

theorem cell21_1061432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_1061432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061432 prefixEnd_1061432 := by exact prefixLift 1061432
  have htrace : WordTrace (prefixWord ++ tailWord_1061432) baseStart_1061432 baseEnd_1061432 := by
    simpa [prefixWord, tailWord_1061432, baseEnd_1061432] using wordTrace_append hprefix tailTrace_1061432
  have hstable : (prefixWord ++ tailWord_1061432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061432).length < 2 ^ (prefixWord ++ tailWord_1061432).sum := by decide
  have hdescent : baseEnd_1061432 < baseStart_1061432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061438 : List Nat := [4, 2, 1, 4, 2, 1, 7]
def baseStart_1061438 : Nat := 118140960795 + 1061438 * 2 ^ 59
def prefixEnd_1061438 : Nat := 4983230072969 + 3 ^ 40 * 1061438 * 2
def baseEnd_1061438 : Nat := 26914956985043128525607

theorem tailTrace_1061438 : CollatzResearch.WordTrace tailWord_1061438 prefixEnd_1061438 26914956985043128525607 := by
  unfold tailWord_1061438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4839228041074860002892121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25809216219065920015424645 4839228041074860002892121)
  ·
    refine ⟨3629421030806145002169091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4839228041074860002892121 3629421030806145002169091)
    ·
      refine ⟨5444131546209217503253637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3629421030806145002169091 5444131546209217503253637)
      ·
        refine ⟨1020774664914228281860057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5444131546209217503253637 1020774664914228281860057)
        ·
          refine ⟨765580998685671211395043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020774664914228281860057 765580998685671211395043)
          ·
            refine ⟨1148371498028506817092565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765580998685671211395043 1148371498028506817092565)
            ·
              refine ⟨26914956985043128525607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1148371498028506817092565 26914956985043128525607)
              ·
                rfl

theorem cell21_1061438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 7].length) (baseStart_1061438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061438 prefixEnd_1061438 := by exact prefixLift 1061438
  have htrace : WordTrace (prefixWord ++ tailWord_1061438) baseStart_1061438 baseEnd_1061438 := by
    simpa [prefixWord, tailWord_1061438, baseEnd_1061438] using wordTrace_append hprefix tailTrace_1061438
  have hstable : (prefixWord ++ tailWord_1061438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061438).length < 2 ^ (prefixWord ++ tailWord_1061438).sum := by decide
  have hdescent : baseEnd_1061438 < baseStart_1061438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061452 : List Nat := [2, 2, 1, 3, 1, 2, 5, 2, 3]
def baseStart_1061452 : Nat := 118140960795 + 1061452 * 2 ^ 59
def prefixEnd_1061452 : Nat := 4983230072969 + 3 ^ 40 * 1061452 * 2
def baseEnd_1061452 : Nat := 242237807856127243497101

theorem tailTrace_1061452 : CollatzResearch.WordTrace tailWord_1061452 prefixEnd_1061452 242237807856127243497101 := by
  unfold tailWord_1061452
  simp only [CollatzResearch.WordTrace]
  refine ⟨19357167475274080207073305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25809556633698773609431073 19357167475274080207073305)
  ·
    refine ⟨14517875606455560155304979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19357167475274080207073305 14517875606455560155304979)
    ·
      refine ⟨21776813409683340232957469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14517875606455560155304979 21776813409683340232957469)
      ·
        refine ⟨8166305028631252587359051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21776813409683340232957469 8166305028631252587359051)
        ·
          refine ⟨12249457542946878881038577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8166305028631252587359051 12249457542946878881038577)
          ·
            refine ⟨9187093157210159160778933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12249457542946878881038577 9187093157210159160778933)
            ·
              refine ⟨861289983488452421323025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9187093157210159160778933 861289983488452421323025)
              ·
                refine ⟨645967487616339315992269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861289983488452421323025 645967487616339315992269)
                ·
                  refine ⟨242237807856127243497101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645967487616339315992269 242237807856127243497101)
                  ·
                    rfl

theorem cell21_1061452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_1061452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061452 prefixEnd_1061452 := by exact prefixLift 1061452
  have htrace : WordTrace (prefixWord ++ tailWord_1061452) baseStart_1061452 baseEnd_1061452 := by
    simpa [prefixWord, tailWord_1061452, baseEnd_1061452] using wordTrace_append hprefix tailTrace_1061452
  have hstable : (prefixWord ++ tailWord_1061452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061452).length < 2 ^ (prefixWord ++ tailWord_1061452).sum := by decide
  have hdescent : baseEnd_1061452 < baseStart_1061452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061463 : List Nat := [1, 1, 3, 2, 2, 2, 4, 6]
def baseStart_1061463 : Nat := 118140960795 + 1061463 * 2 ^ 59
def prefixEnd_1061463 : Nat := 4983230072969 + 3 ^ 40 * 1061463 * 2
def baseEnd_1061463 : Nat := 80746772735331222937915

theorem tailTrace_1061463 : CollatzResearch.WordTrace tailWord_1061463 prefixEnd_1061463 80746772735331222937915 := by
  unfold tailWord_1061463
  simp only [CollatzResearch.WordTrace]
  refine ⟨38714736153508309292797043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25809824102338872861864695 38714736153508309292797043)
  ·
    refine ⟨58072104230262463939195565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38714736153508309292797043 58072104230262463939195565)
    ·
      refine ⟨21777039086348423977198337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58072104230262463939195565 21777039086348423977198337)
      ·
        refine ⟨16332779314761317982898753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21777039086348423977198337 16332779314761317982898753)
        ·
          refine ⟨12249584486070988487174065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16332779314761317982898753 12249584486070988487174065)
          ·
            refine ⟨9187188364553241365380549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12249584486070988487174065 9187188364553241365380549)
            ·
              refine ⟨1722597818353732756008853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9187188364553241365380549 1722597818353732756008853)
              ·
                refine ⟨80746772735331222937915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1722597818353732756008853 80746772735331222937915)
                ·
                  rfl

theorem cell21_1061463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 6].length) (baseStart_1061463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061463 prefixEnd_1061463 := by exact prefixLift 1061463
  have htrace : WordTrace (prefixWord ++ tailWord_1061463) baseStart_1061463 baseEnd_1061463 := by
    simpa [prefixWord, tailWord_1061463, baseEnd_1061463] using wordTrace_append hprefix tailTrace_1061463
  have hstable : (prefixWord ++ tailWord_1061463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061463).length < 2 ^ (prefixWord ++ tailWord_1061463).sum := by decide
  have hdescent : baseEnd_1061463 < baseStart_1061463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061511 : List Nat := [1, 1, 4, 2, 1, 2, 3, 4, 3]
def baseStart_1061511 : Nat := 118140960795 + 1061511 * 2 ^ 59
def prefixEnd_1061511 : Nat := 4983230072969 + 3 ^ 40 * 1061511 * 2
def baseEnd_1061511 : Nat := 242251272459956252013647

theorem tailTrace_1061511 : CollatzResearch.WordTrace tailWord_1061511 prefixEnd_1061511 242251272459956252013647 := by
  unfold tailWord_1061511
  simp only [CollatzResearch.WordTrace]
  refine ⟨38716486857334413490544387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25810991238222942327029591 38716486857334413490544387)
  ·
    refine ⟨58074730286001620235816581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38716486857334413490544387 58074730286001620235816581)
    ·
      refine ⟨10889011928625303794215609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58074730286001620235816581 10889011928625303794215609)
      ·
        refine ⟨8166758946468977845661707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10889011928625303794215609 8166758946468977845661707)
        ·
          refine ⟨12250138419703466768492561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8166758946468977845661707 12250138419703466768492561)
          ·
            refine ⟨9187603814777600076369421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12250138419703466768492561 9187603814777600076369421)
            ·
              refine ⟨3445351430541600028638533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9187603814777600076369421 3445351430541600028638533)
              ·
                refine ⟨646003393226550005369725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3445351430541600028638533 646003393226550005369725)
                ·
                  refine ⟨242251272459956252013647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 646003393226550005369725 242251272459956252013647)
                  ·
                    rfl

theorem cell21_1061511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 3].length) (baseStart_1061511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061511 prefixEnd_1061511 := by exact prefixLift 1061511
  have htrace : WordTrace (prefixWord ++ tailWord_1061511) baseStart_1061511 baseEnd_1061511 := by
    simpa [prefixWord, tailWord_1061511, baseEnd_1061511] using wordTrace_append hprefix tailTrace_1061511
  have hstable : (prefixWord ++ tailWord_1061511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061511).length < 2 ^ (prefixWord ++ tailWord_1061511).sum := by decide
  have hdescent : baseEnd_1061511 < baseStart_1061511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061559 : List Nat := [1, 1, 3, 1, 7, 1, 1, 2, 4]
def baseStart_1061559 : Nat := 118140960795 + 1061559 * 2 ^ 59
def prefixEnd_1061559 : Nat := 4983230072969 + 3 ^ 40 * 1061559 * 2
def baseEnd_1061559 : Nat := 242262226713918835213549

theorem tailTrace_1061559 : CollatzResearch.WordTrace tailWord_1061559 prefixEnd_1061559 242262226713918835213549 := by
  unfold tailWord_1061559
  simp only [CollatzResearch.WordTrace]
  refine ⟨38718237561160517688291731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25812158374107011792194487 38718237561160517688291731)
  ·
    refine ⟨58077356341740776532437597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38718237561160517688291731 58077356341740776532437597)
    ·
      refine ⟨21779008628152791199664099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58077356341740776532437597 21779008628152791199664099)
      ·
        refine ⟨32668512942229186799496149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21779008628152791199664099 32668512942229186799496149)
        ·
          refine ⟨765668272083496565613191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32668512942229186799496149 765668272083496565613191)
          ·
            refine ⟨1148502408125244848419787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765668272083496565613191 1148502408125244848419787)
            ·
              refine ⟨1722753612187867272629681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148502408125244848419787 1722753612187867272629681)
              ·
                refine ⟨1292065209140900454472261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1722753612187867272629681 1292065209140900454472261)
                ·
                  refine ⟨242262226713918835213549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1292065209140900454472261 242262226713918835213549)
                  ·
                    rfl

theorem cell21_1061559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 4].length) (baseStart_1061559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061559 prefixEnd_1061559 := by exact prefixLift 1061559
  have htrace : WordTrace (prefixWord ++ tailWord_1061559) baseStart_1061559 baseEnd_1061559 := by
    simpa [prefixWord, tailWord_1061559, baseEnd_1061559] using wordTrace_append hprefix tailTrace_1061559
  have hstable : (prefixWord ++ tailWord_1061559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061559).length < 2 ^ (prefixWord ++ tailWord_1061559).sum := by decide
  have hdescent : baseEnd_1061559 < baseStart_1061559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061604 : List Nat := [2, 3, 1, 1, 1, 6, 1, 3, 3]
def baseStart_1061604 : Nat := 118140960795 + 1061604 * 2 ^ 59
def prefixEnd_1061604 : Nat := 4983230072969 + 3 ^ 40 * 1061604 * 2
def baseEnd_1061604 : Nat := 242272496327008756963457

theorem tailTrace_1061604 : CollatzResearch.WordTrace tailWord_1061604 prefixEnd_1061604 242272496327008756963457 := by
  unfold tailWord_1061604
  simp only [CollatzResearch.WordTrace]
  refine ⟨19359939422998745186839933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25813252563998326915786577 19359939422998745186839933)
  ·
    refine ⟨7259977283624529445064975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19359939422998745186839933 7259977283624529445064975)
    ·
      refine ⟨10889965925436794167597463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7259977283624529445064975 10889965925436794167597463)
      ·
        refine ⟨16334948888155191251396195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10889965925436794167597463 16334948888155191251396195)
        ·
          refine ⟨24502423332232786877094293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16334948888155191251396195 24502423332232786877094293)
          ·
            refine ⟨1148551093698411884863795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24502423332232786877094293 1148551093698411884863795)
            ·
              refine ⟨1722826640547617827295693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148551093698411884863795 1722826640547617827295693)
              ·
                refine ⟨646059990205356685235885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1722826640547617827295693 646059990205356685235885)
                ·
                  refine ⟨242272496327008756963457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 646059990205356685235885 242272496327008756963457)
                  ·
                    rfl

theorem cell21_1061604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_1061604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061604 prefixEnd_1061604 := by exact prefixLift 1061604
  have htrace : WordTrace (prefixWord ++ tailWord_1061604) baseStart_1061604 baseEnd_1061604 := by
    simpa [prefixWord, tailWord_1061604, baseEnd_1061604] using wordTrace_append hprefix tailTrace_1061604
  have hstable : (prefixWord ++ tailWord_1061604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061604).length < 2 ^ (prefixWord ++ tailWord_1061604).sum := by decide
  have hdescent : baseEnd_1061604 < baseStart_1061604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061615 : List Nat := [1, 1, 2, 1, 5, 4, 7]
def baseStart_1061615 : Nat := 118140960795 + 1061615 * 2 ^ 59
def prefixEnd_1061615 : Nat := 4983230072969 + 3 ^ 40 * 1061615 * 2
def baseEnd_1061615 : Nat := 26919445186319464697789

theorem tailTrace_1061615 : CollatzResearch.WordTrace tailWord_1061615 prefixEnd_1061615 26919445186319464697789 := by
  unfold tailWord_1061615
  simp only [CollatzResearch.WordTrace]
  refine ⟨38720280048957639252330299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25813520032638426168220199 38720280048957639252330299)
  ·
    refine ⟨58080420073436458878495449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38720280048957639252330299 58080420073436458878495449)
    ·
      refine ⟨43560315055077344158871587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58080420073436458878495449 43560315055077344158871587)
      ·
        refine ⟨65340472582616016238307381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43560315055077344158871587 65340472582616016238307381)
        ·
          refine ⟨6125669304620251522341317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65340472582616016238307381 6125669304620251522341317)
          ·
            refine ⟨1148562994616297160438997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6125669304620251522341317 1148562994616297160438997)
            ·
              refine ⟨26919445186319464697789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1148562994616297160438997 26919445186319464697789)
              ·
                rfl

theorem cell21_1061615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 7].length) (baseStart_1061615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061615 prefixEnd_1061615 := by exact prefixLift 1061615
  have htrace : WordTrace (prefixWord ++ tailWord_1061615) baseStart_1061615 baseEnd_1061615 := by
    simpa [prefixWord, tailWord_1061615, baseEnd_1061615] using wordTrace_append hprefix tailTrace_1061615
  have hstable : (prefixWord ++ tailWord_1061615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061615).length < 2 ^ (prefixWord ++ tailWord_1061615).sum := by decide
  have hdescent : baseEnd_1061615 < baseStart_1061615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061705 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 7]
def baseStart_1061705 : Nat := 118140960795 + 1061705 * 2 ^ 59
def prefixEnd_1061705 : Nat := 4983230072969 + 3 ^ 40 * 1061705 * 2
def baseEnd_1061705 : Nat := 242295545903055025779917

theorem tailTrace_1061705 : CollatzResearch.WordTrace tailWord_1061705 prefixEnd_1061705 242295545903055025779917 := by
  unfold tailWord_1061705
  simp only [CollatzResearch.WordTrace]
  refine ⟨38723562618631584623106569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25815708412421056415404379 38723562618631584623106569)
  ·
    refine ⟨29042671963973688467329927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38723562618631584623106569 29042671963973688467329927)
    ·
      refine ⟨43564007945960532700994891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29042671963973688467329927 43564007945960532700994891)
      ·
        refine ⟨65346011918940799051492337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43564007945960532700994891 65346011918940799051492337)
        ·
          refine ⟨49009508939205599288619253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65346011918940799051492337 49009508939205599288619253)
          ·
            refine ⟨4594641463050524933308055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49009508939205599288619253 4594641463050524933308055)
            ·
              refine ⟨6891962194575787399962083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594641463050524933308055 6891962194575787399962083)
              ·
                refine ⟨10337943291863681099943125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6891962194575787399962083 10337943291863681099943125)
                ·
                  refine ⟨242295545903055025779917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10337943291863681099943125 242295545903055025779917)
                  ·
                    rfl

theorem cell21_1061705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_1061705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061705 prefixEnd_1061705 := by exact prefixLift 1061705
  have htrace : WordTrace (prefixWord ++ tailWord_1061705) baseStart_1061705 baseEnd_1061705 := by
    simpa [prefixWord, tailWord_1061705, baseEnd_1061705] using wordTrace_append hprefix tailTrace_1061705
  have hstable : (prefixWord ++ tailWord_1061705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061705).length < 2 ^ (prefixWord ++ tailWord_1061705).sum := by decide
  have hdescent : baseEnd_1061705 < baseStart_1061705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061708 : List Nat := [2, 2, 1, 3, 3, 2, 3, 5]
def baseStart_1061708 : Nat := 118140960795 + 1061708 * 2 ^ 59
def prefixEnd_1061708 : Nat := 4983230072969 + 3 ^ 40 * 1061708 * 2
def baseEnd_1061708 : Nat := 80765410181309229076637

theorem tailTrace_1061708 : CollatzResearch.WordTrace tailWord_1061708 prefixEnd_1061708 80765410181309229076637 := by
  unfold tailWord_1061708
  simp only [CollatzResearch.WordTrace]
  refine ⟨19361836018810358067732889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25815781358413810756977185 19361836018810358067732889)
  ·
    refine ⟨14521377014107768550799667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19361836018810358067732889 14521377014107768550799667)
    ·
      refine ⟨21782065521161652826199501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14521377014107768550799667 21782065521161652826199501)
      ·
        refine ⟨8168274570435619809824813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21782065521161652826199501 8168274570435619809824813)
        ·
          refine ⟨3063102963913357428684305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8168274570435619809824813 3063102963913357428684305)
          ·
            refine ⟨2297327222935018071513229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3063102963913357428684305 2297327222935018071513229)
            ·
              refine ⟨861497708600631776817461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2297327222935018071513229 861497708600631776817461)
              ·
                refine ⟨80765410181309229076637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 861497708600631776817461 80765410181309229076637)
                ·
                  rfl

theorem cell21_1061708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 5].length) (baseStart_1061708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061708 prefixEnd_1061708 := by exact prefixLift 1061708
  have htrace : WordTrace (prefixWord ++ tailWord_1061708) baseStart_1061708 baseEnd_1061708 := by
    simpa [prefixWord, tailWord_1061708, baseEnd_1061708] using wordTrace_append hprefix tailTrace_1061708
  have hstable : (prefixWord ++ tailWord_1061708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061708).length < 2 ^ (prefixWord ++ tailWord_1061708).sum := by decide
  have hdescent : baseEnd_1061708 < baseStart_1061708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061767 : List Nat := [1, 1, 4, 2, 3, 2, 1, 7]
def baseStart_1061767 : Nat := 118140960795 + 1061767 * 2 ^ 59
def prefixEnd_1061767 : Nat := 4983230072969 + 3 ^ 40 * 1061767 * 2
def baseEnd_1061767 : Nat := 80769898382585565248819

theorem tailTrace_1061767 : CollatzResearch.WordTrace tailWord_1061767 prefixEnd_1061767 80769898382585565248819 := by
  unfold tailWord_1061767
  simp only [CollatzResearch.WordTrace]
  refine ⟨38725823944406969211863555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25817215962937979474575703 38725823944406969211863555)
  ·
    refine ⟨58088735916610453817795333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38725823944406969211863555 58088735916610453817795333)
    ·
      refine ⟨10891637984364460090836625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58088735916610453817795333 10891637984364460090836625)
      ·
        refine ⟨8168728488273345068127469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10891637984364460090836625 8168728488273345068127469)
        ·
          refine ⟨3063273183102504400547801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8168728488273345068127469 3063273183102504400547801)
          ·
            refine ⟨2297454887326878300410851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3063273183102504400547801 2297454887326878300410851)
            ·
              refine ⟨3446182330990317450616277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297454887326878300410851 3446182330990317450616277)
              ·
                refine ⟨80769898382585565248819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3446182330990317450616277 80769898382585565248819)
                ·
                  rfl

theorem cell21_1061767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 7].length) (baseStart_1061767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061767 prefixEnd_1061767 := by exact prefixLift 1061767
  have htrace : WordTrace (prefixWord ++ tailWord_1061767) baseStart_1061767 baseEnd_1061767 := by
    simpa [prefixWord, tailWord_1061767, baseEnd_1061767] using wordTrace_append hprefix tailTrace_1061767
  have hstable : (prefixWord ++ tailWord_1061767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061767).length < 2 ^ (prefixWord ++ tailWord_1061767).sum := by decide
  have hdescent : baseEnd_1061767 < baseStart_1061767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061846 : List Nat := [5, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1061846 : Nat := 118140960795 + 1061846 * 2 ^ 59
def prefixEnd_1061846 : Nat := 4983230072969 + 3 ^ 40 * 1061846 * 2
def baseEnd_1061846 : Nat := 242327724024070113929629

theorem tailTrace_1061846 : CollatzResearch.WordTrace tailWord_1061846 prefixEnd_1061846 242327724024070113929629 := by
  unfold tailWord_1061846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2420544081945047856499337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25819136874080510469326261 2420544081945047856499337)
  ·
    refine ⟨1815408061458785892374503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2420544081945047856499337 1815408061458785892374503)
    ·
      refine ⟨2723112092188178838561755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1815408061458785892374503 2723112092188178838561755)
      ·
        refine ⟨4084668138282268257842633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2723112092188178838561755 4084668138282268257842633)
        ·
          refine ⟨3063501103711701193381975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4084668138282268257842633 3063501103711701193381975)
          ·
            refine ⟨4595251655567551790072963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063501103711701193381975 4595251655567551790072963)
            ·
              refine ⟨6892877483351327685109445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4595251655567551790072963 6892877483351327685109445)
              ·
                refine ⟨1292414528128373940958021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6892877483351327685109445 1292414528128373940958021)
                ·
                  refine ⟨242327724024070113929629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1292414528128373940958021 242327724024070113929629)
                  ·
                    rfl

theorem cell21_1061846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1061846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061846 prefixEnd_1061846 := by exact prefixLift 1061846
  have htrace : WordTrace (prefixWord ++ tailWord_1061846) baseStart_1061846 baseEnd_1061846 := by
    simpa [prefixWord, tailWord_1061846, baseEnd_1061846] using wordTrace_append hprefix tailTrace_1061846
  have hstable : (prefixWord ++ tailWord_1061846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061846).length < 2 ^ (prefixWord ++ tailWord_1061846).sum := by decide
  have hdescent : baseEnd_1061846 < baseStart_1061846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061857 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 5]
def baseStart_1061857 : Nat := 118140960795 + 1061857 * 2 ^ 59
def prefixEnd_1061857 : Nat := 4983230072969 + 3 ^ 40 * 1061857 * 2
def baseEnd_1061857 : Nat := 242330234373936539246273

theorem tailTrace_1061857 : CollatzResearch.WordTrace tailWord_1061857 prefixEnd_1061857 242330234373936539246273 := by
  unfold tailWord_1061857
  simp only [CollatzResearch.WordTrace]
  refine ⟨38729106514080914582639825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25819404342720609721759883 38729106514080914582639825)
  ·
    refine ⟨29046829885560685936979869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38729106514080914582639825 29046829885560685936979869)
    ·
      refine ⟨10892561207085257226367451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29046829885560685936979869 10892561207085257226367451)
      ·
        refine ⟨16338841810627885839551177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10892561207085257226367451 16338841810627885839551177)
        ·
          refine ⟨12254131357970914379663383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16338841810627885839551177 12254131357970914379663383)
          ·
            refine ⟨18381197036956371569495075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12254131357970914379663383 18381197036956371569495075)
            ·
              refine ⟨27571795555434557354242613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18381197036956371569495075 27571795555434557354242613)
              ·
                refine ⟨2584855833321989751960245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27571795555434557354242613 2584855833321989751960245)
                ·
                  refine ⟨242330234373936539246273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2584855833321989751960245 242330234373936539246273)
                  ·
                    rfl

theorem cell21_1061857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_1061857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061857 prefixEnd_1061857 := by exact prefixLift 1061857
  have htrace : WordTrace (prefixWord ++ tailWord_1061857) baseStart_1061857 baseEnd_1061857 := by
    simpa [prefixWord, tailWord_1061857, baseEnd_1061857] using wordTrace_append hprefix tailTrace_1061857
  have hstable : (prefixWord ++ tailWord_1061857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061857).length < 2 ^ (prefixWord ++ tailWord_1061857).sum := by decide
  have hdescent : baseEnd_1061857 < baseStart_1061857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061922 : List Nat := [3, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1061922 : Nat := 118140960795 + 1061922 * 2 ^ 59
def prefixEnd_1061922 : Nat := 4983230072969 + 3 ^ 40 * 1061922 * 2
def baseEnd_1061922 : Nat := 242345068259510870662807

theorem tailTrace_1061922 : CollatzResearch.WordTrace tailWord_1061922 prefixEnd_1061922 242345068259510870662807 := by
  unfold tailWord_1061922
  simp only [CollatzResearch.WordTrace]
  refine ⟨9682869314711357670939005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25820984839230287122504013 9682869314711357670939005)
  ·
    refine ⟨3631075993016759126602127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9682869314711357670939005 3631075993016759126602127)
    ·
      refine ⟨5446613989525138689903191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3631075993016759126602127 5446613989525138689903191)
      ·
        refine ⟨8169920984287708034854787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5446613989525138689903191 8169920984287708034854787)
        ·
          refine ⟨12254881476431562052282181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8169920984287708034854787 12254881476431562052282181)
          ·
            refine ⟨2297790276830917884802909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12254881476431562052282181 2297790276830917884802909)
            ·
              refine ⟨861671353811594206801091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2297790276830917884802909 861671353811594206801091)
              ·
                refine ⟨1292507030717391310201637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 861671353811594206801091 1292507030717391310201637)
                ·
                  refine ⟨242345068259510870662807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1292507030717391310201637 242345068259510870662807)
                  ·
                    rfl

theorem cell21_1061922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1061922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061922 prefixEnd_1061922 := by exact prefixLift 1061922
  have htrace : WordTrace (prefixWord ++ tailWord_1061922) baseStart_1061922 baseEnd_1061922 := by
    simpa [prefixWord, tailWord_1061922, baseEnd_1061922] using wordTrace_append hprefix tailTrace_1061922
  have hstable : (prefixWord ++ tailWord_1061922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061922).length < 2 ^ (prefixWord ++ tailWord_1061922).sum := by decide
  have hdescent : baseEnd_1061922 < baseStart_1061922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061964 : List Nat := [2, 2, 1, 3, 1, 1, 1, 6, 4]
def baseStart_1061964 : Nat := 118140960795 + 1061964 * 2 ^ 59
def prefixEnd_1061964 : Nat := 4983230072969 + 3 ^ 40 * 1061964 * 2
def baseEnd_1061964 : Nat := 242354653231728130962721

theorem tailTrace_1061964 : CollatzResearch.WordTrace tailWord_1061964 prefixEnd_1061964 242354653231728130962721 := by
  unfold tailWord_1061964
  simp only [CollatzResearch.WordTrace]
  refine ⟨19366504562346635928392473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25822006083128847904523297 19366504562346635928392473)
  ·
    refine ⟨14524878421759976946294355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19366504562346635928392473 14524878421759976946294355)
    ·
      refine ⟨21787317632639965419441533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14524878421759976946294355 21787317632639965419441533)
      ·
        refine ⟨8170244112239987032290575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21787317632639965419441533 8170244112239987032290575)
        ·
          refine ⟨12255366168359980548435863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8170244112239987032290575 12255366168359980548435863)
          ·
            refine ⟨18383049252539970822653795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12255366168359980548435863 18383049252539970822653795)
            ·
              refine ⟨27574573878809956233980693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18383049252539970822653795 27574573878809956233980693)
              ·
                refine ⟨1292558150569216698467845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27574573878809956233980693 1292558150569216698467845)
                ·
                  refine ⟨242354653231728130962721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1292558150569216698467845 242354653231728130962721)
                  ·
                    rfl

theorem cell21_1061964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_1061964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1061964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1061964 prefixEnd_1061964 := by exact prefixLift 1061964
  have htrace : WordTrace (prefixWord ++ tailWord_1061964) baseStart_1061964 baseEnd_1061964 := by
    simpa [prefixWord, tailWord_1061964, baseEnd_1061964] using wordTrace_append hprefix tailTrace_1061964
  have hstable : (prefixWord ++ tailWord_1061964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061964).length < 2 ^ (prefixWord ++ tailWord_1061964).sum := by decide
  have hdescent : baseEnd_1061964 < baseStart_1061964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062192 : List Nat := [2, 1, 1, 1, 2, 2, 6, 2, 4]
def baseStart_1062192 : Nat := 118140960795 + 1062192 * 2 ^ 59
def prefixEnd_1062192 : Nat := 4983230072969 + 3 ^ 40 * 1062192 * 2
def baseEnd_1062192 : Nat := 242406685938050401162255

theorem tailTrace_1062192 : CollatzResearch.WordTrace tailWord_1062192 prefixEnd_1062192 242406685938050401162255 := by
  unfold tailWord_1062192
  simp only [CollatzResearch.WordTrace]
  refine ⟨19370662483933633398042415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25827549978578177864056553 19370662483933633398042415)
  ·
    refine ⟨29055993725900450097063623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19370662483933633398042415 29055993725900450097063623)
    ·
      refine ⟨43583990588850675145595435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29055993725900450097063623 43583990588850675145595435)
      ·
        refine ⟨65375985883276012718393153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43583990588850675145595435 65375985883276012718393153)
        ·
          refine ⟨49031989412457009538794865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65375985883276012718393153 49031989412457009538794865)
          ·
            refine ⟨36773992059342757154096149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49031989412457009538794865 36773992059342757154096149)
            ·
              refine ⟨1723780877781691741598257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36773992059342757154096149 1723780877781691741598257)
              ·
                refine ⟨1292835658336268806198693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1723780877781691741598257 1292835658336268806198693)
                ·
                  refine ⟨242406685938050401162255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1292835658336268806198693 242406685938050401162255)
                  ·
                    rfl

theorem cell21_1062192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_1062192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062192 prefixEnd_1062192 := by exact prefixLift 1062192
  have htrace : WordTrace (prefixWord ++ tailWord_1062192) baseStart_1062192 baseEnd_1062192 := by
    simpa [prefixWord, tailWord_1062192, baseEnd_1062192] using wordTrace_append hprefix tailTrace_1062192
  have hstable : (prefixWord ++ tailWord_1062192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062192).length < 2 ^ (prefixWord ++ tailWord_1062192).sum := by decide
  have hdescent : baseEnd_1062192 < baseStart_1062192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062195 : List Nat := [1, 1, 1, 2, 5, 2, 4, 2, 3]
def baseStart_1062195 : Nat := 118140960795 + 1062195 * 2 ^ 59
def prefixEnd_1062195 : Nat := 4983230072969 + 3 ^ 40 * 1062195 * 2
def baseEnd_1062195 : Nat := 242407370578923062612249

theorem tailTrace_1062195 : CollatzResearch.WordTrace tailWord_1062195 prefixEnd_1062195 242407370578923062612249 := by
  unfold tailWord_1062195
  simp only [CollatzResearch.WordTrace]
  refine ⟨38741434386856398308444039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25827622924570932205629359 38741434386856398308444039)
  ·
    refine ⟨58112151580284597462666059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38741434386856398308444039 58112151580284597462666059)
    ·
      refine ⟨87168227370426896193999089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58112151580284597462666059 87168227370426896193999089)
      ·
        refine ⟨65376170527820172145499317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87168227370426896193999089 65376170527820172145499317)
        ·
          refine ⟨6129015986983141138640561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65376170527820172145499317 6129015986983141138640561)
          ·
            refine ⟨4596761990237355853980421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6129015986983141138640561 4596761990237355853980421)
            ·
              refine ⟨861892873169504222621329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4596761990237355853980421 861892873169504222621329)
              ·
                refine ⟨646419654877128166965997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861892873169504222621329 646419654877128166965997)
                ·
                  refine ⟨242407370578923062612249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 646419654877128166965997 242407370578923062612249)
                  ·
                    rfl

theorem cell21_1062195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 3].length) (baseStart_1062195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062195 prefixEnd_1062195 := by exact prefixLift 1062195
  have htrace : WordTrace (prefixWord ++ tailWord_1062195) baseStart_1062195 baseEnd_1062195 := by
    simpa [prefixWord, tailWord_1062195, baseEnd_1062195] using wordTrace_append hprefix tailTrace_1062195
  have hstable : (prefixWord ++ tailWord_1062195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062195).length < 2 ^ (prefixWord ++ tailWord_1062195).sum := by decide
  have hdescent : baseEnd_1062195 < baseStart_1062195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062198 : List Nat := [5, 1, 2, 3, 2, 1, 1, 6]
def baseStart_1062198 : Nat := 118140960795 + 1062198 * 2 ^ 59
def prefixEnd_1062198 : Nat := 4983230072969 + 3 ^ 40 * 1062198 * 2
def baseEnd_1062198 : Nat := 80802685073265241354081

theorem tailTrace_1062198 : CollatzResearch.WordTrace tailWord_1062198 prefixEnd_1062198 80802685073265241354081 := by
  unfold tailWord_1062198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421346487865345613800203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25827695870563686547202165 2421346487865345613800203)
  ·
    refine ⟨3632019731798018420700305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2421346487865345613800203 3632019731798018420700305)
    ·
      refine ⟨2724014798848513815525229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3632019731798018420700305 2724014798848513815525229)
      ·
        refine ⟨1021505549568192680821961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2724014798848513815525229 1021505549568192680821961)
        ·
          refine ⟨766129162176144510616471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1021505549568192680821961 766129162176144510616471)
          ·
            refine ⟨1149193743264216765924707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766129162176144510616471 1149193743264216765924707)
            ·
              refine ⟨1723790614896325148887061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149193743264216765924707 1723790614896325148887061)
              ·
                refine ⟨80802685073265241354081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1723790614896325148887061 80802685073265241354081)
                ·
                  rfl

theorem cell21_1062198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_1062198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062198 prefixEnd_1062198 := by exact prefixLift 1062198
  have htrace : WordTrace (prefixWord ++ tailWord_1062198) baseStart_1062198 baseEnd_1062198 := by
    simpa [prefixWord, tailWord_1062198, baseEnd_1062198] using wordTrace_append hprefix tailTrace_1062198
  have hstable : (prefixWord ++ tailWord_1062198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062198).length < 2 ^ (prefixWord ++ tailWord_1062198).sum := by decide
  have hdescent : baseEnd_1062198 < baseStart_1062198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062209 : List Nat := [1, 2, 5, 2, 1, 1, 2, 3, 4]
def baseStart_1062209 : Nat := 118140960795 + 1062209 * 2 ^ 59
def prefixEnd_1062209 : Nat := 4983230072969 + 3 ^ 40 * 1062209 * 2
def baseEnd_1062209 : Nat := 242410565569662149378887

theorem tailTrace_1062209 : CollatzResearch.WordTrace tailWord_1062209 prefixEnd_1062209 242410565569662149378887 := by
  unfold tailWord_1062209
  simp only [CollatzResearch.WordTrace]
  refine ⟨38741945008805678699453681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25827963339203785799635787 38741945008805678699453681)
  ·
    refine ⟨29056458756604259024590261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38741945008805678699453681 29056458756604259024590261)
    ·
      refine ⟨2724043008431649283555337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29056458756604259024590261 2724043008431649283555337)
      ·
        refine ⟨2043032256323736962666503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2724043008431649283555337 2043032256323736962666503)
        ·
          refine ⟨3064548384485605443999755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2043032256323736962666503 3064548384485605443999755)
          ·
            refine ⟨4596822576728408165999633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3064548384485605443999755 4596822576728408165999633)
            ·
              refine ⟨3447616932546306124499725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4596822576728408165999633 3447616932546306124499725)
              ·
                refine ⟨1292856349704864796687397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3447616932546306124499725 1292856349704864796687397)
                ·
                  refine ⟨242410565569662149378887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1292856349704864796687397 242410565569662149378887)
                  ·
                    rfl

theorem cell21_1062209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_1062209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062209 prefixEnd_1062209 := by exact prefixLift 1062209
  have htrace : WordTrace (prefixWord ++ tailWord_1062209) baseStart_1062209 baseEnd_1062209 := by
    simpa [prefixWord, tailWord_1062209, baseEnd_1062209] using wordTrace_append hprefix tailTrace_1062209
  have hstable : (prefixWord ++ tailWord_1062209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062209).length < 2 ^ (prefixWord ++ tailWord_1062209).sum := by decide
  have hdescent : baseEnd_1062209 < baseStart_1062209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062372 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 9]
def baseStart_1062372 : Nat := 118140960795 + 1062372 * 2 ^ 59
def prefixEnd_1062372 : Nat := 4983230072969 + 3 ^ 40 * 1062372 * 2
def baseEnd_1062372 : Nat := 242447764390410088161887

theorem tailTrace_1062372 : CollatzResearch.WordTrace tailWord_1062372 prefixEnd_1062372 242447764390410088161887 := by
  unfold tailWord_1062372
  simp only [CollatzResearch.WordTrace]
  refine ⟨19373945053607578768818685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25831926738143438358424913 19373945053607578768818685)
  ·
    refine ⟨7265229395102842038307007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19373945053607578768818685 7265229395102842038307007)
    ·
      refine ⟨10897844092654263057460511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7265229395102842038307007 10897844092654263057460511)
      ·
        refine ⟨16346766138981394586190767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10897844092654263057460511 16346766138981394586190767)
        ·
          refine ⟨24520149208472091879286151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16346766138981394586190767 24520149208472091879286151)
          ·
            refine ⟨36780223812708137818929227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24520149208472091879286151 36780223812708137818929227)
            ·
              refine ⟨55170335719062206728393841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36780223812708137818929227 55170335719062206728393841)
              ·
                refine ⟨41377751789296655046295381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55170335719062206728393841 41377751789296655046295381)
                ·
                  refine ⟨242447764390410088161887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41377751789296655046295381 242447764390410088161887)
                  ·
                    rfl

theorem cell21_1062372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_1062372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062372 prefixEnd_1062372 := by exact prefixLift 1062372
  have htrace : WordTrace (prefixWord ++ tailWord_1062372) baseStart_1062372 baseEnd_1062372 := by
    simpa [prefixWord, tailWord_1062372, baseEnd_1062372] using wordTrace_append hprefix tailTrace_1062372
  have hstable : (prefixWord ++ tailWord_1062372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062372).length < 2 ^ (prefixWord ++ tailWord_1062372).sum := by decide
  have hdescent : baseEnd_1062372 < baseStart_1062372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062375 : List Nat := [1, 1, 5, 2, 1, 4, 1, 6]
def baseStart_1062375 : Nat := 118140960795 + 1062375 * 2 ^ 59
def prefixEnd_1062375 : Nat := 4983230072969 + 3 ^ 40 * 1062375 * 2
def baseEnd_1062375 : Nat := 80816149677094249870627

theorem tailTrace_1062375 : CollatzResearch.WordTrace tailWord_1062375 prefixEnd_1062375 80816149677094249870627 := by
  unfold tailWord_1062375
  simp only [CollatzResearch.WordTrace]
  refine ⟨38747999526204289049996579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25831999684136192699997719 38747999526204289049996579)
  ·
    refine ⟨58121999289306433574994869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38747999526204289049996579 58121999289306433574994869)
    ·
      refine ⟨5448937433372478147655769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58121999289306433574994869 5448937433372478147655769)
      ·
        refine ⟨4086703075029358610741827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5448937433372478147655769 4086703075029358610741827)
        ·
          refine ⟨6130054612544037916112741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4086703075029358610741827 6130054612544037916112741)
          ·
            refine ⟨1149385239852007109271139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6130054612544037916112741 1149385239852007109271139)
            ·
              refine ⟨1724077859778010663906709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149385239852007109271139 1724077859778010663906709)
              ·
                refine ⟨80816149677094249870627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1724077859778010663906709 80816149677094249870627)
                ·
                  rfl

theorem cell21_1062375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 6].length) (baseStart_1062375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062375 prefixEnd_1062375 := by exact prefixLift 1062375
  have htrace : WordTrace (prefixWord ++ tailWord_1062375) baseStart_1062375 baseEnd_1062375 := by
    simpa [prefixWord, tailWord_1062375, baseEnd_1062375] using wordTrace_append hprefix tailTrace_1062375
  have hstable : (prefixWord ++ tailWord_1062375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062375).length < 2 ^ (prefixWord ++ tailWord_1062375).sum := by decide
  have hdescent : baseEnd_1062375 < baseStart_1062375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062417 : List Nat := [1, 2, 2, 1, 1, 2, 12]
def baseStart_1062417 : Nat := 118140960795 + 1062417 * 2 ^ 59
def prefixEnd_1062417 : Nat := 4983230072969 + 3 ^ 40 * 1062417 * 2
def baseEnd_1062417 : Nat := 26939781555944445545755

theorem tailTrace_1062417 : CollatzResearch.WordTrace tailWord_1062417 prefixEnd_1062417 26939781555944445545755 := by
  unfold tailWord_1062417
  simp only [CollatzResearch.WordTrace]
  refine ⟨38749531392052130223025505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25833020928034753482017003 38749531392052130223025505)
  ·
    refine ⟨29062148544039097667269129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38749531392052130223025505 29062148544039097667269129)
    ·
      refine ⟨21796611408029323250451847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29062148544039097667269129 21796611408029323250451847)
      ·
        refine ⟨32694917112043984875677771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21796611408029323250451847 32694917112043984875677771)
        ·
          refine ⟨49042375668065977313516657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32694917112043984875677771 49042375668065977313516657)
          ·
            refine ⟨36781781751049482985137493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49042375668065977313516657 36781781751049482985137493)
            ·
              refine ⟨26939781555944445545755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 36781781751049482985137493 26939781555944445545755)
              ·
                rfl

theorem cell21_1062417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 12].length) (baseStart_1062417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062417 prefixEnd_1062417 := by exact prefixLift 1062417
  have htrace : WordTrace (prefixWord ++ tailWord_1062417) baseStart_1062417 baseEnd_1062417 := by
    simpa [prefixWord, tailWord_1062417, baseEnd_1062417] using wordTrace_append hprefix tailTrace_1062417
  have hstable : (prefixWord ++ tailWord_1062417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062417).length < 2 ^ (prefixWord ++ tailWord_1062417).sum := by decide
  have hdescent : baseEnd_1062417 < baseStart_1062417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062451 : List Nat := [1, 1, 1, 2, 4, 5, 2, 5]
def baseStart_1062451 : Nat := 118140960795 + 1062451 * 2 ^ 59
def prefixEnd_1062451 : Nat := 4983230072969 + 3 ^ 40 * 1062451 * 2
def baseEnd_1062451 : Nat := 80821931088907835448353

theorem tailTrace_1062451 : CollatzResearch.WordTrace tailWord_1062451 prefixEnd_1062451 80821931088907835448353 := by
  unfold tailWord_1062451
  simp only [CollatzResearch.WordTrace]
  refine ⟨38750771473928954029763207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25833847649285969353175471 38750771473928954029763207)
  ·
    refine ⟨58126157210893431044644811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38750771473928954029763207 58126157210893431044644811)
    ·
      refine ⟨87189235816340146566967217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58126157210893431044644811 87189235816340146566967217)
      ·
        refine ⟨65391926862255109925225413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87189235816340146566967217 65391926862255109925225413)
        ·
          refine ⟨12260986286672833110979765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65391926862255109925225413 12260986286672833110979765)
          ·
            refine ⟨1149467464375578104154353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12260986286672833110979765 1149467464375578104154353)
            ·
              refine ⟨862100598281683578115765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149467464375578104154353 862100598281683578115765)
              ·
                refine ⟨80821931088907835448353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 862100598281683578115765 80821931088907835448353)
                ·
                  rfl

theorem cell21_1062451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 5].length) (baseStart_1062451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062451 prefixEnd_1062451 := by exact prefixLift 1062451
  have htrace : WordTrace (prefixWord ++ tailWord_1062451) baseStart_1062451 baseEnd_1062451 := by
    simpa [prefixWord, tailWord_1062451, baseEnd_1062451] using wordTrace_append hprefix tailTrace_1062451
  have hstable : (prefixWord ++ tailWord_1062451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062451).length < 2 ^ (prefixWord ++ tailWord_1062451).sum := by decide
  have hdescent : baseEnd_1062451 < baseStart_1062451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062479 : List Nat := [1, 1, 2, 1, 1, 2, 3, 6, 4]
def baseStart_1062479 : Nat := 118140960795 + 1062479 * 2 ^ 59
def prefixEnd_1062479 : Nat := 4983230072969 + 3 ^ 40 * 1062479 * 2
def baseEnd_1062479 : Nat := 242472183248201679878335

theorem tailTrace_1062479 : CollatzResearch.WordTrace tailWord_1062479 prefixEnd_1062479 242472183248201679878335 := by
  unfold tailWord_1062479
  simp only [CollatzResearch.WordTrace]
  refine ⟨38751792717827514811782491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25834528478551676541188327 38751792717827514811782491)
  ·
    refine ⟨58127689076741272217673737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38751792717827514811782491 58127689076741272217673737)
    ·
      refine ⟨43595766807555954163255303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58127689076741272217673737 43595766807555954163255303)
      ·
        refine ⟨65393650211333931244882955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43595766807555954163255303 65393650211333931244882955)
        ·
          refine ⟨98090475317000896867324433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65393650211333931244882955 98090475317000896867324433)
          ·
            refine ⟨73567856487750672650493325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98090475317000896867324433 73567856487750672650493325)
            ·
              refine ⟨27587946182906502243934997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73567856487750672650493325 27587946182906502243934997)
              ·
                refine ⟨1293184977323742292684453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27587946182906502243934997 1293184977323742292684453)
                ·
                  refine ⟨242472183248201679878335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293184977323742292684453 242472183248201679878335)
                  ·
                    rfl

theorem cell21_1062479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 4].length) (baseStart_1062479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062479 prefixEnd_1062479 := by exact prefixLift 1062479
  have htrace : WordTrace (prefixWord ++ tailWord_1062479) baseStart_1062479 baseEnd_1062479 := by
    simpa [prefixWord, tailWord_1062479, baseEnd_1062479] using wordTrace_append hprefix tailTrace_1062479
  have hstable : (prefixWord ++ tailWord_1062479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062479).length < 2 ^ (prefixWord ++ tailWord_1062479).sum := by decide
  have hdescent : baseEnd_1062479 < baseStart_1062479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062482 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_1062482 : Nat := 118140960795 + 1062482 * 2 ^ 59
def prefixEnd_1062482 : Nat := 4983230072969 + 3 ^ 40 * 1062482 * 2
def baseEnd_1062482 : Nat := 242472867889074341328329

theorem tailTrace_1062482 : CollatzResearch.WordTrace tailWord_1062482 prefixEnd_1062482 242472867889074341328329 := by
  unfold tailWord_1062482
  simp only [CollatzResearch.WordTrace]
  refine ⟨9687975534204161581035425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25834601424544430882761133 9687975534204161581035425)
  ·
    refine ⟨7265981650653121185776569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9687975534204161581035425 7265981650653121185776569)
    ·
      refine ⟨5449486237989840889332427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7265981650653121185776569 5449486237989840889332427)
      ·
        refine ⟨8174229356984761333998641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5449486237989840889332427 8174229356984761333998641)
        ·
          refine ⟨6130672017738571000498981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8174229356984761333998641 6130672017738571000498981)
          ·
            refine ⟨1149501003325982062593559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6130672017738571000498981 1149501003325982062593559)
            ·
              refine ⟨1724251504988973093890339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149501003325982062593559 1724251504988973093890339)
              ·
                refine ⟨2586377257483459640835509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724251504988973093890339 2586377257483459640835509)
                ·
                  refine ⟨242472867889074341328329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2586377257483459640835509 242472867889074341328329)
                  ·
                    rfl

theorem cell21_1062482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_1062482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062482 prefixEnd_1062482 := by exact prefixLift 1062482
  have htrace : WordTrace (prefixWord ++ tailWord_1062482) baseStart_1062482 baseEnd_1062482 := by
    simpa [prefixWord, tailWord_1062482, baseEnd_1062482] using wordTrace_append hprefix tailTrace_1062482
  have hstable : (prefixWord ++ tailWord_1062482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062482).length < 2 ^ (prefixWord ++ tailWord_1062482).sum := by decide
  have hdescent : baseEnd_1062482 < baseStart_1062482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062558 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1062558 : Nat := 118140960795 + 1062558 * 2 ^ 59
def prefixEnd_1062558 : Nat := 4983230072969 + 3 ^ 40 * 1062558 * 2
def baseEnd_1062558 : Nat := 242490212124515098061507

theorem tailTrace_1062558 : CollatzResearch.WordTrace tailWord_1062558 prefixEnd_1062558 242490212124515098061507 := by
  unfold tailWord_1062558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4844334260567663912988541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25836449389694207535938885 4844334260567663912988541)
  ·
    refine ⟨1816625347712873967370703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4844334260567663912988541 1816625347712873967370703)
    ·
      refine ⟨2724938021569310951056055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1816625347712873967370703 2724938021569310951056055)
      ·
        refine ⟨4087407032353966426584083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2724938021569310951056055 4087407032353966426584083)
        ·
          refine ⟨6131110548530949639876125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4087407032353966426584083 6131110548530949639876125)
          ·
            refine ⟨2299166455699106114953547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6131110548530949639876125 2299166455699106114953547)
            ·
              refine ⟨3448749683548659172430321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2299166455699106114953547 3448749683548659172430321)
              ·
                refine ⟨2586562262661494379322741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3448749683548659172430321 2586562262661494379322741)
                ·
                  refine ⟨242490212124515098061507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2586562262661494379322741 242490212124515098061507)
                  ·
                    rfl

theorem cell21_1062558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1062558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062558 prefixEnd_1062558 := by exact prefixLift 1062558
  have htrace : WordTrace (prefixWord ++ tailWord_1062558) baseStart_1062558 baseEnd_1062558 := by
    simpa [prefixWord, tailWord_1062558, baseEnd_1062558] using wordTrace_append hprefix tailTrace_1062558
  have hstable : (prefixWord ++ tailWord_1062558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062558).length < 2 ^ (prefixWord ++ tailWord_1062558).sum := by decide
  have hdescent : baseEnd_1062558 < baseStart_1062558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062634 : List Nat := [3, 1, 3, 1, 1, 1, 5, 3, 3]
def baseStart_1062634 : Nat := 118140960795 + 1062634 * 2 ^ 59
def prefixEnd_1062634 : Nat := 4983230072969 + 3 ^ 40 * 1062634 * 2
def baseEnd_1062634 : Nat := 242507556359955854794685

theorem tailTrace_1062634 : CollatzResearch.WordTrace tailWord_1062634 prefixEnd_1062634 242507556359955854794685 := by
  unfold tailWord_1062634
  simp only [CollatzResearch.WordTrace]
  refine ⟨9689361508066494070918739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25838297354843984189116637 9689361508066494070918739)
  ·
    refine ⟨14534042262099741106378109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9689361508066494070918739 14534042262099741106378109)
    ·
      refine ⟨5450265848287402914891791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14534042262099741106378109 5450265848287402914891791)
      ·
        refine ⟨8175398772431104372337687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5450265848287402914891791 8175398772431104372337687)
        ·
          refine ⟨12263098158646656558506531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8175398772431104372337687 12263098158646656558506531)
          ·
            refine ⟨18394647237969984837759797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12263098158646656558506531 18394647237969984837759797)
            ·
              refine ⟨1724498178559686078539981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18394647237969984837759797 1724498178559686078539981)
              ·
                refine ⟨646686816959882279452493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1724498178559686078539981 646686816959882279452493)
                ·
                  refine ⟨242507556359955854794685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 646686816959882279452493 242507556359955854794685)
                  ·
                    rfl

theorem cell21_1062634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_1062634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062634 prefixEnd_1062634 := by exact prefixLift 1062634
  have htrace : WordTrace (prefixWord ++ tailWord_1062634) baseStart_1062634 baseEnd_1062634 := by
    simpa [prefixWord, tailWord_1062634, baseEnd_1062634] using wordTrace_append hprefix tailTrace_1062634
  have hstable : (prefixWord ++ tailWord_1062634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062634).length < 2 ^ (prefixWord ++ tailWord_1062634).sum := by decide
  have hdescent : baseEnd_1062634 < baseStart_1062634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062769 : List Nat := [1, 2, 2, 2, 1, 3, 1, 6, 3]
def baseStart_1062769 : Nat := 118140960795 + 1062769 * 2 ^ 59
def prefixEnd_1062769 : Nat := 4983230072969 + 3 ^ 40 * 1062769 * 2
def baseEnd_1062769 : Nat := 242538365199225620044409

theorem tailTrace_1062769 : CollatzResearch.WordTrace tailWord_1062769 prefixEnd_1062769 242538365199225620044409 := by
  unfold tailWord_1062769
  simp only [CollatzResearch.WordTrace]
  refine ⟨38762369886776894339839361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25841579924517929559892907 38762369886776894339839361)
  ·
    refine ⟨29071777415082670754879521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38762369886776894339839361 29071777415082670754879521)
    ·
      refine ⟨21803833061312003066159641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29071777415082670754879521 21803833061312003066159641)
      ·
        refine ⟨16352874795984002299619731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21803833061312003066159641 16352874795984002299619731)
        ·
          refine ⟨24529312193976003449429597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16352874795984002299619731 24529312193976003449429597)
          ·
            refine ⟨9198492072741001293536099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24529312193976003449429597 9198492072741001293536099)
            ·
              refine ⟨13797738109111501940304149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9198492072741001293536099 13797738109111501940304149)
              ·
                refine ⟨646768973864601653451757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13797738109111501940304149 646768973864601653451757)
                ·
                  refine ⟨242538365199225620044409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 646768973864601653451757 242538365199225620044409)
                  ·
                    rfl

theorem cell21_1062769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 3].length) (baseStart_1062769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062769 prefixEnd_1062769 := by exact prefixLift 1062769
  have htrace : WordTrace (prefixWord ++ tailWord_1062769) baseStart_1062769 baseEnd_1062769 := by
    simpa [prefixWord, tailWord_1062769, baseEnd_1062769] using wordTrace_append hprefix tailTrace_1062769
  have hstable : (prefixWord ++ tailWord_1062769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062769).length < 2 ^ (prefixWord ++ tailWord_1062769).sum := by decide
  have hdescent : baseEnd_1062769 < baseStart_1062769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062842 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_1062842 : Nat := 118140960795 + 1062842 * 2 ^ 59
def prefixEnd_1062842 : Nat := 4983230072969 + 3 ^ 40 * 1062842 * 2
def baseEnd_1062842 : Nat := 242555024793793715327593

theorem tailTrace_1062842 : CollatzResearch.WordTrace tailWord_1062842 prefixEnd_1062842 242555024793793715327593 := by
  unfold tailWord_1062842
  simp only [CollatzResearch.WordTrace]
  refine ⟨9691258103878106951811695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25843354943674951871497853 9691258103878106951811695)
  ·
    refine ⟨14536887155817160427717543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9691258103878106951811695 14536887155817160427717543)
    ·
      refine ⟨21805330733725740641576315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14536887155817160427717543 21805330733725740641576315)
      ·
        refine ⟨32707996100588610962364473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21805330733725740641576315 32707996100588610962364473)
        ·
          refine ⟨24530997075441458221773355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32707996100588610962364473 24530997075441458221773355)
          ·
            refine ⟨36796495613162187332660033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24530997075441458221773355 36796495613162187332660033)
            ·
              refine ⟨27597371709871640499495025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36796495613162187332660033 27597371709871640499495025)
              ·
                refine ⟨20698028782403730374621269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27597371709871640499495025 20698028782403730374621269)
                ·
                  refine ⟨242555024793793715327593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20698028782403730374621269 242555024793793715327593)
                  ·
                    rfl

theorem cell21_1062842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_1062842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062842 prefixEnd_1062842 := by exact prefixLift 1062842
  have htrace : WordTrace (prefixWord ++ tailWord_1062842) baseStart_1062842 baseEnd_1062842 := by
    simpa [prefixWord, tailWord_1062842, baseEnd_1062842] using wordTrace_append hprefix tailTrace_1062842
  have hstable : (prefixWord ++ tailWord_1062842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062842).length < 2 ^ (prefixWord ++ tailWord_1062842).sum := by decide
  have hdescent : baseEnd_1062842 < baseStart_1062842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062873 : List Nat := [1, 2, 1, 2, 6, 9]
def baseStart_1062873 : Nat := 118140960795 + 1062873 * 2 ^ 59
def prefixEnd_1062873 : Nat := 4983230072969 + 3 ^ 40 * 1062873 * 2
def baseEnd_1062873 : Nat := 8983781459857205567069

theorem tailTrace_1062873 : CollatzResearch.WordTrace tailWord_1062873 prefixEnd_1062873 8983781459857205567069 := by
  unfold tailWord_1062873
  simp only [CollatzResearch.WordTrace]
  refine ⟨38766163078400120101625273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25844108718933413401083515 38766163078400120101625273)
  ·
    refine ⟨29074622308800090076218955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38766163078400120101625273 29074622308800090076218955)
    ·
      refine ⟨43611933463200135114328433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29074622308800090076218955 43611933463200135114328433)
      ·
        refine ⟨32708950097400101335746325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43611933463200135114328433 32708950097400101335746325)
        ·
          refine ⟨1533232035815629750113109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32708950097400101335746325 1533232035815629750113109)
          ·
            refine ⟨8983781459857205567069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1533232035815629750113109 8983781459857205567069)
            ·
              rfl

theorem cell21_1062873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 9].length) (baseStart_1062873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062873 prefixEnd_1062873 := by exact prefixLift 1062873
  have htrace : WordTrace (prefixWord ++ tailWord_1062873) baseStart_1062873 baseEnd_1062873 := by
    simpa [prefixWord, tailWord_1062873, baseEnd_1062873] using wordTrace_append hprefix tailTrace_1062873
  have hstable : (prefixWord ++ tailWord_1062873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062873).length < 2 ^ (prefixWord ++ tailWord_1062873).sum := by decide
  have hdescent : baseEnd_1062873 < baseStart_1062873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062879 : List Nat := [1, 1, 2, 3, 4, 3, 2, 2, 3]
def baseStart_1062879 : Nat := 118140960795 + 1062879 * 2 ^ 59
def prefixEnd_1062879 : Nat := 4983230072969 + 3 ^ 40 * 1062879 * 2
def baseEnd_1062879 : Nat := 242563468697889873210851

theorem tailTrace_1062879 : CollatzResearch.WordTrace tailWord_1062879 prefixEnd_1062879 242563468697889873210851 := by
  unfold tailWord_1062879
  simp only [CollatzResearch.WordTrace]
  refine ⟨38766381916378383126343691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25844254610918922084229127 38766381916378383126343691)
  ·
    refine ⟨58149572874567574689515537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38766381916378383126343691 58149572874567574689515537)
    ·
      refine ⟨43612179655925681017136653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58149572874567574689515537 43612179655925681017136653)
      ·
        refine ⟨16354567370972130381426245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43612179655925681017136653 16354567370972130381426245)
        ·
          refine ⟨3066481382057274446517421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16354567370972130381426245 3066481382057274446517421)
          ·
            refine ⟨1149930518271477917444033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3066481382057274446517421 1149930518271477917444033)
            ·
              refine ⟨862447888703608438083025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149930518271477917444033 862447888703608438083025)
              ·
                refine ⟨646835916527706328562269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 862447888703608438083025 646835916527706328562269)
                ·
                  refine ⟨242563468697889873210851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 646835916527706328562269 242563468697889873210851)
                  ·
                    rfl

theorem cell21_1062879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 3].length) (baseStart_1062879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062879 prefixEnd_1062879 := by exact prefixLift 1062879
  have htrace : WordTrace (prefixWord ++ tailWord_1062879) baseStart_1062879 baseEnd_1062879 := by
    simpa [prefixWord, tailWord_1062879, baseEnd_1062879] using wordTrace_append hprefix tailTrace_1062879
  have hstable : (prefixWord ++ tailWord_1062879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062879).length < 2 ^ (prefixWord ++ tailWord_1062879).sum := by decide
  have hdescent : baseEnd_1062879 < baseStart_1062879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062966 : List Nat := [5, 1, 2, 1, 1, 1, 3, 7]
def baseStart_1062966 : Nat := 118140960795 + 1062966 * 2 ^ 59
def prefixEnd_1062966 : Nat := 4983230072969 + 3 ^ 40 * 1062966 * 2
def baseEnd_1062966 : Nat := 80861107761065685086891

theorem tailTrace_1062966 : CollatzResearch.WordTrace tailWord_1062966 prefixEnd_1062966 80861107761065685086891 := by
  unfold tailWord_1062966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423097191691449811547547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25846370044708797989840501 2423097191691449811547547)
  ·
    refine ⟨3634645787537174717321321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2423097191691449811547547 3634645787537174717321321)
    ·
      refine ⟨2725984340652881037990991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3634645787537174717321321 2725984340652881037990991)
      ·
        refine ⟨4088976510979321556986487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2725984340652881037990991 4088976510979321556986487)
        ·
          refine ⟨6133464766468982335479731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4088976510979321556986487 6133464766468982335479731)
          ·
            refine ⟨9200197149703473503219597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6133464766468982335479731 9200197149703473503219597)
            ·
              refine ⟨3450073931138802563707349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9200197149703473503219597 3450073931138802563707349)
              ·
                refine ⟨80861107761065685086891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3450073931138802563707349 80861107761065685086891)
                ·
                  rfl

theorem cell21_1062966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_1062966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062966 prefixEnd_1062966 := by exact prefixLift 1062966
  have htrace : WordTrace (prefixWord ++ tailWord_1062966) baseStart_1062966 baseEnd_1062966 := by
    simpa [prefixWord, tailWord_1062966, baseEnd_1062966] using wordTrace_append hprefix tailTrace_1062966
  have hstable : (prefixWord ++ tailWord_1062966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062966).length < 2 ^ (prefixWord ++ tailWord_1062966).sum := by decide
  have hdescent : baseEnd_1062966 < baseStart_1062966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062997 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 5]
def baseStart_1062997 : Nat := 118140960795 + 1062997 * 2 ^ 59
def prefixEnd_1062997 : Nat := 4983230072969 + 3 ^ 40 * 1062997 * 2
def baseEnd_1062997 : Nat := 242590397905547890243943

theorem tailTrace_1062997 : CollatzResearch.WordTrace tailWord_1062997 prefixEnd_1062997 242590397905547890243943 := by
  unfold tailWord_1062997
  simp only [CollatzResearch.WordTrace]
  refine ⟨38770685729950889279139245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25847123819967259519426163 38770685729950889279139245)
  ·
    refine ⟨14539007148731583479677217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38770685729950889279139245 14539007148731583479677217)
    ·
      refine ⟨10904255361548687609757913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14539007148731583479677217 10904255361548687609757913)
      ·
        refine ⟨8178191521161515707318435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10904255361548687609757913 8178191521161515707318435)
        ·
          refine ⟨12267287281742273560977653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8178191521161515707318435 12267287281742273560977653)
          ·
            refine ⟨1150058182663338146341655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12267287281742273560977653 1150058182663338146341655)
            ·
              refine ⟨1725087273995007219512483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1150058182663338146341655 1725087273995007219512483)
              ·
                refine ⟨2587630910992510829268725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1725087273995007219512483 2587630910992510829268725)
                ·
                  refine ⟨242590397905547890243943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2587630910992510829268725 242590397905547890243943)
                  ·
                    rfl

theorem cell21_1062997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_1062997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1062997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1062997 prefixEnd_1062997 := by exact prefixLift 1062997
  have htrace : WordTrace (prefixWord ++ tailWord_1062997) baseStart_1062997 baseEnd_1062997 := by
    simpa [prefixWord, tailWord_1062997, baseEnd_1062997] using wordTrace_append hprefix tailTrace_1062997
  have hstable : (prefixWord ++ tailWord_1062997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062997).length < 2 ^ (prefixWord ++ tailWord_1062997).sum := by decide
  have hdescent : baseEnd_1062997 < baseStart_1062997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063104 : List Nat := [2, 1, 1, 2, 5, 3, 1, 2, 4]
def baseStart_1063104 : Nat := 118140960795 + 1063104 * 2 ^ 59
def prefixEnd_1063104 : Nat := 4983230072969 + 3 ^ 40 * 1063104 * 2
def baseEnd_1063104 : Nat := 242614816763339481960391

theorem tailTrace_1063104 : CollatzResearch.WordTrace tailWord_1063104 prefixEnd_1063104 242614816763339481960391 := by
  unfold tailWord_1063104
  simp only [CollatzResearch.WordTrace]
  refine ⟨19387294170281623276642183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25849725560375497702189577 19387294170281623276642183)
  ·
    refine ⟨29080941255422434914963275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19387294170281623276642183 29080941255422434914963275)
    ·
      refine ⟨43621411883133652372444913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29080941255422434914963275 43621411883133652372444913)
      ·
        refine ⟨32716058912350239279333685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43621411883133652372444913 32716058912350239279333685)
        ·
          refine ⟨3067130523032834932437533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32716058912350239279333685 3067130523032834932437533)
          ·
            refine ⟨1150173946137313099664075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3067130523032834932437533 1150173946137313099664075)
            ·
              refine ⟨1725260919205969649496113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1150173946137313099664075 1725260919205969649496113)
              ·
                refine ⟨1293945689404477237122085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1725260919205969649496113 1293945689404477237122085)
                ·
                  refine ⟨242614816763339481960391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293945689404477237122085 242614816763339481960391)
                  ·
                    rfl

theorem cell21_1063104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_1063104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063104 prefixEnd_1063104 := by exact prefixLift 1063104
  have htrace : WordTrace (prefixWord ++ tailWord_1063104) baseStart_1063104 baseEnd_1063104 := by
    simpa [prefixWord, tailWord_1063104, baseEnd_1063104] using wordTrace_append hprefix tailTrace_1063104
  have hstable : (prefixWord ++ tailWord_1063104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063104).length < 2 ^ (prefixWord ++ tailWord_1063104).sum := by decide
  have hdescent : baseEnd_1063104 < baseStart_1063104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063146 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_1063146 : Nat := 118140960795 + 1063146 * 2 ^ 59
def prefixEnd_1063146 : Nat := 4983230072969 + 3 ^ 40 * 1063146 * 2
def baseEnd_1063146 : Nat := 242624401735556742260305

theorem tailTrace_1063146 : CollatzResearch.WordTrace tailWord_1063146 prefixEnd_1063146 242624401735556742260305 := by
  unfold tailWord_1063146
  simp only [CollatzResearch.WordTrace]
  refine ⟨9694030051602771931578323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25850746804274058484208861 9694030051602771931578323)
  ·
    refine ⟨14541045077404157897367485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9694030051602771931578323 14541045077404157897367485)
    ·
      refine ⟨5452891904026559211512807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14541045077404157897367485 5452891904026559211512807)
      ·
        refine ⟨8179337856039838817269211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5452891904026559211512807 8179337856039838817269211)
        ·
          refine ⟨12269006784059758225903817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8179337856039838817269211 12269006784059758225903817)
          ·
            refine ⟨9201755088044818669427863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12269006784059758225903817 9201755088044818669427863)
            ·
              refine ⟨13802632632067228004141795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9201755088044818669427863 13802632632067228004141795)
              ·
                refine ⟨20703948948100842006212693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13802632632067228004141795 20703948948100842006212693)
                ·
                  refine ⟨242624401735556742260305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20703948948100842006212693 242624401735556742260305)
                  ·
                    rfl

theorem cell21_1063146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_1063146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063146 prefixEnd_1063146 := by exact prefixLift 1063146
  have htrace : WordTrace (prefixWord ++ tailWord_1063146) baseStart_1063146 baseEnd_1063146 := by
    simpa [prefixWord, tailWord_1063146, baseEnd_1063146] using wordTrace_append hprefix tailTrace_1063146
  have hstable : (prefixWord ++ tailWord_1063146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063146).length < 2 ^ (prefixWord ++ tailWord_1063146).sum := by decide
  have hdescent : baseEnd_1063146 < baseStart_1063146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063177 : List Nat := [1, 2, 1, 1, 3, 5, 2, 6]
def baseStart_1063177 : Nat := 118140960795 + 1063177 * 2 ^ 59
def prefixEnd_1063177 : Nat := 4983230072969 + 3 ^ 40 * 1063177 * 2
def baseEnd_1063177 : Nat := 80877158785969192414525

theorem tailTrace_1063177 : CollatzResearch.WordTrace tailWord_1063177 prefixEnd_1063177 80877158785969192414525 := by
  unfold tailWord_1063177
  simp only [CollatzResearch.WordTrace]
  refine ⟨38777250869298780020691785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25851500579532520013794523 38777250869298780020691785)
  ·
    refine ⟨29082938151974085015518839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38777250869298780020691785 29082938151974085015518839)
    ·
      refine ⟨43624407227961127523278259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29082938151974085015518839 43624407227961127523278259)
      ·
        refine ⟨65436610841941691284917389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43624407227961127523278259 65436610841941691284917389)
        ·
          refine ⟨24538729065728134231844021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65436610841941691284917389 24538729065728134231844021)
          ·
            refine ⟨2300505849912012584235377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24538729065728134231844021 2300505849912012584235377)
            ·
              refine ⟨1725379387434009438176533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2300505849912012584235377 1725379387434009438176533)
              ·
                refine ⟨80877158785969192414525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1725379387434009438176533 80877158785969192414525)
                ·
                  rfl

theorem cell21_1063177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 6].length) (baseStart_1063177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063177 prefixEnd_1063177 := by exact prefixLift 1063177
  have htrace : WordTrace (prefixWord ++ tailWord_1063177) baseStart_1063177 baseEnd_1063177 := by
    simpa [prefixWord, tailWord_1063177, baseEnd_1063177] using wordTrace_append hprefix tailTrace_1063177
  have hstable : (prefixWord ++ tailWord_1063177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063177).length < 2 ^ (prefixWord ++ tailWord_1063177).sum := by decide
  have hdescent : baseEnd_1063177 < baseStart_1063177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063267 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 7]
def baseStart_1063267 : Nat := 118140960795 + 1063267 * 2 ^ 59
def prefixEnd_1063267 : Nat := 4983230072969 + 3 ^ 40 * 1063267 * 2
def baseEnd_1063267 : Nat := 242652015584087420743391

theorem tailTrace_1063267 : CollatzResearch.WordTrace tailWord_1063267 prefixEnd_1063267 242652015584087420743391 := by
  unfold tailWord_1063267
  simp only [CollatzResearch.WordTrace]
  refine ⟨38780533438972725391468055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25853688959315150260978703 38780533438972725391468055)
  ·
    refine ⟨58170800158459088087202083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38780533438972725391468055 58170800158459088087202083)
    ·
      refine ⟨87256200237688632130803125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58170800158459088087202083 87256200237688632130803125)
      ·
        refine ⟨8180268772283309262262793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87256200237688632130803125 8180268772283309262262793)
        ·
          refine ⟨6135201579212481946697095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8180268772283309262262793 6135201579212481946697095)
          ·
            refine ⟨9202802368818722920045643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6135201579212481946697095 9202802368818722920045643)
            ·
              refine ⟨13804203553228084380068465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9202802368818722920045643 13804203553228084380068465)
              ·
                refine ⟨10353152664921063285051349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13804203553228084380068465 10353152664921063285051349)
                ·
                  refine ⟨242652015584087420743391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10353152664921063285051349 242652015584087420743391)
                  ·
                    rfl

theorem cell21_1063267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_1063267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063267 prefixEnd_1063267 := by exact prefixLift 1063267
  have htrace : WordTrace (prefixWord ++ tailWord_1063267) baseStart_1063267 baseEnd_1063267 := by
    simpa [prefixWord, tailWord_1063267, baseEnd_1063267] using wordTrace_append hprefix tailTrace_1063267
  have hstable : (prefixWord ++ tailWord_1063267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063267).length < 2 ^ (prefixWord ++ tailWord_1063267).sum := by decide
  have hdescent : baseEnd_1063267 < baseStart_1063267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063349 : List Nat := [1, 3, 3, 2, 3, 2, 2, 1, 4]
def baseStart_1063349 : Nat := 118140960795 + 1063349 * 2 ^ 59
def prefixEnd_1063349 : Nat := 4983230072969 + 3 ^ 40 * 1063349 * 2
def baseEnd_1063349 : Nat := 242670729101273500376557

theorem tailTrace_1063349 : CollatzResearch.WordTrace tailWord_1063349 prefixEnd_1063349 242670729101273500376557 := by
  unfold tailWord_1063349
  simp only [CollatzResearch.WordTrace]
  refine ⟨38783524224675653395953101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25855682816450435597302067 38783524224675653395953101)
  ·
    refine ⟨14543821584253370023482413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38783524224675653395953101 14543821584253370023482413)
    ·
      refine ⟨5453933094095013758805905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14543821584253370023482413 5453933094095013758805905)
      ·
        refine ⟨4090449820571260319104429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5453933094095013758805905 4090449820571260319104429)
        ·
          refine ⟨1533918682714222619664161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4090449820571260319104429 1533918682714222619664161)
          ·
            refine ⟨1150439012035666964748121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1533918682714222619664161 1150439012035666964748121)
            ·
              refine ⟨862829259026750223561091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150439012035666964748121 862829259026750223561091)
              ·
                refine ⟨1294243888540125335341637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862829259026750223561091 1294243888540125335341637)
                ·
                  refine ⟨242670729101273500376557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1294243888540125335341637 242670729101273500376557)
                  ·
                    rfl

theorem cell21_1063349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_1063349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063349 prefixEnd_1063349 := by exact prefixLift 1063349
  have htrace : WordTrace (prefixWord ++ tailWord_1063349) baseStart_1063349 baseEnd_1063349 := by
    simpa [prefixWord, tailWord_1063349, baseEnd_1063349] using wordTrace_append hprefix tailTrace_1063349
  have hstable : (prefixWord ++ tailWord_1063349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063349).length < 2 ^ (prefixWord ++ tailWord_1063349).sum := by decide
  have hdescent : baseEnd_1063349 < baseStart_1063349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063391 : List Nat := [1, 1, 2, 3, 3, 3, 2, 2, 4]
def baseStart_1063391 : Nat := 118140960795 + 1063391 * 2 ^ 59
def prefixEnd_1063391 : Nat := 4983230072969 + 3 ^ 40 * 1063391 * 2
def baseEnd_1063391 : Nat := 242680314073490760676471

theorem tailTrace_1063391 : CollatzResearch.WordTrace tailWord_1063391 prefixEnd_1063391 242680314073490760676471 := by
  unfold tailWord_1063391
  simp only [CollatzResearch.WordTrace]
  refine ⟨38785056090523494568982027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25856704060348996379321351 38785056090523494568982027)
  ·
    refine ⟨58177584135785241853473041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38785056090523494568982027 58177584135785241853473041)
    ·
      refine ⟨43633188101838931390104781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58177584135785241853473041 43633188101838931390104781)
      ·
        refine ⟨16362445538189599271289293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43633188101838931390104781 16362445538189599271289293)
        ·
          refine ⟨6135917076821099726733485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16362445538189599271289293 6135917076821099726733485)
          ·
            refine ⟨2300968903807912397525057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6135917076821099726733485 2300968903807912397525057)
            ·
              refine ⟨1725726677855934298143793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2300968903807912397525057 1725726677855934298143793)
              ·
                refine ⟨1294295008391950723607845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1725726677855934298143793 1294295008391950723607845)
                ·
                  refine ⟨242680314073490760676471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1294295008391950723607845 242680314073490760676471)
                  ·
                    rfl

theorem cell21_1063391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 4].length) (baseStart_1063391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063391 prefixEnd_1063391 := by exact prefixLift 1063391
  have htrace : WordTrace (prefixWord ++ tailWord_1063391) baseStart_1063391 baseEnd_1063391 := by
    simpa [prefixWord, tailWord_1063391, baseEnd_1063391] using wordTrace_append hprefix tailTrace_1063391
  have hstable : (prefixWord ++ tailWord_1063391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063391).length < 2 ^ (prefixWord ++ tailWord_1063391).sum := by decide
  have hdescent : baseEnd_1063391 < baseStart_1063391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063453 : List Nat := [1, 4, 2, 2, 1, 2, 2, 4, 3]
def baseStart_1063453 : Nat := 118140960795 + 1063453 * 2 ^ 59
def prefixEnd_1063453 : Nat := 4983230072969 + 3 ^ 40 * 1063453 * 2
def baseEnd_1063453 : Nat := 242694463318192430643011

theorem tailTrace_1063453 : CollatzResearch.WordTrace tailWord_1063453 prefixEnd_1063453 242694463318192430643011 := by
  unfold tailWord_1063453
  simp only [CollatzResearch.WordTrace]
  refine ⟨38787317416298879157739013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25858211610865919438492675 38787317416298879157739013)
  ·
    refine ⟨7272622015556039842076065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38787317416298879157739013 7272622015556039842076065)
    ·
      refine ⟨5454466511667029881557049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7272622015556039842076065 5454466511667029881557049)
      ·
        refine ⟨4090849883750272411167787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5454466511667029881557049 4090849883750272411167787)
        ·
          refine ⟨6136274825625408616751681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4090849883750272411167787 6136274825625408616751681)
          ·
            refine ⟨4602206119219056462563761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6136274825625408616751681 4602206119219056462563761)
            ·
              refine ⟨3451654589414292346922821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4602206119219056462563761 3451654589414292346922821)
              ·
                refine ⟨647185235515179815048029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3451654589414292346922821 647185235515179815048029)
                ·
                  refine ⟨242694463318192430643011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647185235515179815048029 242694463318192430643011)
                  ·
                    rfl

theorem cell21_1063453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_1063453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063453 prefixEnd_1063453 := by exact prefixLift 1063453
  have htrace : WordTrace (prefixWord ++ tailWord_1063453) baseStart_1063453 baseEnd_1063453 := by
    simpa [prefixWord, tailWord_1063453, baseEnd_1063453] using wordTrace_append hprefix tailTrace_1063453
  have hstable : (prefixWord ++ tailWord_1063453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063453).length < 2 ^ (prefixWord ++ tailWord_1063453).sum := by decide
  have hdescent : baseEnd_1063453 < baseStart_1063453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063512 : List Nat := [2, 1, 2, 2, 1, 2, 2, 6, 3]
def baseStart_1063512 : Nat := 118140960795 + 1063512 * 2 ^ 59
def prefixEnd_1063512 : Nat := 4983230072969 + 3 ^ 40 * 1063512 * 2
def baseEnd_1063512 : Nat := 242707927922021439159557

theorem tailTrace_1063512 : CollatzResearch.WordTrace tailWord_1063512 prefixEnd_1063512 242707927922021439159557 := by
  unfold tailWord_1063512
  simp only [CollatzResearch.WordTrace]
  refine ⟨19394734661542566117068395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25859646215390088156091193 19394734661542566117068395)
  ·
    refine ⟨29092101992313849175602593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19394734661542566117068395 29092101992313849175602593)
    ·
      refine ⟨21819076494235386881701945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29092101992313849175602593 21819076494235386881701945)
      ·
        refine ⟨16364307370676540161276459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21819076494235386881701945 16364307370676540161276459)
        ·
          refine ⟨24546461056014810241914689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16364307370676540161276459 24546461056014810241914689)
          ·
            refine ⟨18409845792011107681436017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24546461056014810241914689 18409845792011107681436017)
            ·
              refine ⟨13807384344008330761077013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18409845792011107681436017 13807384344008330761077013)
              ·
                refine ⟨647221141125390504425485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13807384344008330761077013 647221141125390504425485)
                ·
                  refine ⟨242707927922021439159557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647221141125390504425485 242707927922021439159557)
                  ·
                    rfl

theorem cell21_1063512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 3].length) (baseStart_1063512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063512 prefixEnd_1063512 := by exact prefixLift 1063512
  have htrace : WordTrace (prefixWord ++ tailWord_1063512) baseStart_1063512 baseEnd_1063512 := by
    simpa [prefixWord, tailWord_1063512, baseEnd_1063512] using wordTrace_append hprefix tailTrace_1063512
  have hstable : (prefixWord ++ tailWord_1063512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063512).length < 2 ^ (prefixWord ++ tailWord_1063512).sum := by decide
  have hdescent : baseEnd_1063512 < baseStart_1063512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063518 : List Nat := [4, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1063518 : Nat := 118140960795 + 1063518 * 2 ^ 59
def prefixEnd_1063518 : Nat := 4983230072969 + 3 ^ 40 * 1063518 * 2
def baseEnd_1063518 : Nat := 242709297203766762059545

theorem tailTrace_1063518 : CollatzResearch.WordTrace tailWord_1063518 prefixEnd_1063518 242709297203766762059545 := by
  unfold tailWord_1063518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4848711020132924407356901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25859792107375596839236805 4848711020132924407356901)
  ·
    refine ⟨909133316274923326379419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4848711020132924407356901 909133316274923326379419)
    ·
      refine ⟨1363699974412384989569129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 909133316274923326379419 1363699974412384989569129)
      ·
        refine ⟨1022774980809288742176847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1363699974412384989569129 1022774980809288742176847)
        ·
          refine ⟨1534162471213933113265271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022774980809288742176847 1534162471213933113265271)
          ·
            refine ⟨2301243706820899669897907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534162471213933113265271 2301243706820899669897907)
            ·
              refine ⟨3451865560231349504846861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301243706820899669897907 3451865560231349504846861)
              ·
                refine ⟨1294449585086756064317573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3451865560231349504846861 1294449585086756064317573)
                ·
                  refine ⟨242709297203766762059545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1294449585086756064317573 242709297203766762059545)
                  ·
                    rfl

theorem cell21_1063518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1063518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063518 prefixEnd_1063518 := by exact prefixLift 1063518
  have htrace : WordTrace (prefixWord ++ tailWord_1063518) baseStart_1063518 baseEnd_1063518 := by
    simpa [prefixWord, tailWord_1063518, baseEnd_1063518] using wordTrace_append hprefix tailTrace_1063518
  have hstable : (prefixWord ++ tailWord_1063518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063518).length < 2 ^ (prefixWord ++ tailWord_1063518).sum := by decide
  have hdescent : baseEnd_1063518 < baseStart_1063518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063591 : List Nat := [1, 1, 6, 3, 1, 1, 3, 5]
def baseStart_1063591 : Nat := 118140960795 + 1063591 * 2 ^ 59
def prefixEnd_1063591 : Nat := 4983230072969 + 3 ^ 40 * 1063591 * 2
def baseEnd_1063591 : Nat := 80908652266111619114243

theorem tailTrace_1063591 : CollatzResearch.WordTrace tailWord_1063591 prefixEnd_1063591 80908652266111619114243 := by
  unfold tailWord_1063591
  simp only [CollatzResearch.WordTrace]
  refine ⟨38792350689798928726262627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25861567126532619150841751 38792350689798928726262627)
  ·
    refine ⟨58188526034698393089393941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38792350689798928726262627 58188526034698393089393941)
    ·
      refine ⟨2727587157876487176065341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58188526034698393089393941 2727587157876487176065341)
      ·
        refine ⟨1022845184203682691024503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2727587157876487176065341 1022845184203682691024503)
        ·
          refine ⟨1534267776305524036536755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022845184203682691024503 1534267776305524036536755)
          ·
            refine ⟨2301401664458286054805133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534267776305524036536755 2301401664458286054805133)
            ·
              refine ⟨863025624171857270551925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2301401664458286054805133 863025624171857270551925)
              ·
                refine ⟨80908652266111619114243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 863025624171857270551925 80908652266111619114243)
                ·
                  rfl

theorem cell21_1063591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 5].length) (baseStart_1063591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063591 prefixEnd_1063591 := by exact prefixLift 1063591
  have htrace : WordTrace (prefixWord ++ tailWord_1063591) baseStart_1063591 baseEnd_1063591 := by
    simpa [prefixWord, tailWord_1063591, baseEnd_1063591] using wordTrace_append hprefix tailTrace_1063591
  have hstable : (prefixWord ++ tailWord_1063591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063591).length < 2 ^ (prefixWord ++ tailWord_1063591).sum := by decide
  have hdescent : baseEnd_1063591 < baseStart_1063591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063605 : List Nat := [1, 3, 3, 3, 1, 1, 1, 5, 3]
def baseStart_1063605 : Nat := 118140960795 + 1063605 * 2 ^ 59
def prefixEnd_1063605 : Nat := 4983230072969 + 3 ^ 40 * 1063605 * 2
def baseEnd_1063605 : Nat := 242729151789073944109367

theorem tailTrace_1063605 : CollatzResearch.WordTrace tailWord_1063605 prefixEnd_1063605 242729151789073944109367 := by
  unfold tailWord_1063605
  simp only [CollatzResearch.WordTrace]
  refine ⟨38792861311748209117272269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25861907541165472744848179 38792861311748209117272269)
  ·
    refine ⟨14547322991905578418977101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38792861311748209117272269 14547322991905578418977101)
    ·
      refine ⟨5455246121964591907116413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14547322991905578418977101 5455246121964591907116413)
      ·
        refine ⟨2045717295736721965168655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5455246121964591907116413 2045717295736721965168655)
        ·
          refine ⟨3068575943605082947752983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2045717295736721965168655 3068575943605082947752983)
          ·
            refine ⟨4602863915407624421629475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3068575943605082947752983 4602863915407624421629475)
            ·
              refine ⟨6904295873111436632444213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4602863915407624421629475 6904295873111436632444213)
              ·
                refine ⟨647277738104197184291645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6904295873111436632444213 647277738104197184291645)
                ·
                  refine ⟨242729151789073944109367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647277738104197184291645 242729151789073944109367)
                  ·
                    rfl

theorem cell21_1063605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_1063605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063605 prefixEnd_1063605 := by exact prefixLift 1063605
  have htrace : WordTrace (prefixWord ++ tailWord_1063605) baseStart_1063605 baseEnd_1063605 := by
    simpa [prefixWord, tailWord_1063605, baseEnd_1063605] using wordTrace_append hprefix tailTrace_1063605
  have hstable : (prefixWord ++ tailWord_1063605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063605).length < 2 ^ (prefixWord ++ tailWord_1063605).sum := by decide
  have hdescent : baseEnd_1063605 < baseStart_1063605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063616 : List Nat := [2, 1, 1, 2, 4, 3, 8]
def baseStart_1063616 : Nat := 118140960795 + 1063616 * 2 ^ 59
def prefixEnd_1063616 : Nat := 4983230072969 + 3 ^ 40 * 1063616 * 2
def baseEnd_1063616 : Nat := 26970184682104485491779

theorem tailTrace_1063616 : CollatzResearch.WordTrace tailWord_1063616 prefixEnd_1063616 26970184682104485491779 := by
  unfold tailWord_1063616
  simp only [CollatzResearch.WordTrace]
  refine ⟨19396631257354178997961351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25862175009805571997281801 19396631257354178997961351)
  ·
    refine ⟨29094946886031268496942027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19396631257354178997961351 29094946886031268496942027)
    ·
      refine ⟨43642420329046902745413041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29094946886031268496942027 43642420329046902745413041)
      ·
        refine ⟨32731815246785177059059781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43642420329046902745413041 32731815246785177059059781)
        ·
          refine ⟨6137215358772220698573709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32731815246785177059059781 6137215358772220698573709)
          ·
            refine ⟨2301455759539582761965141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6137215358772220698573709 2301455759539582761965141)
            ·
              refine ⟨26970184682104485491779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2301455759539582761965141 26970184682104485491779)
              ·
                rfl

theorem cell21_1063616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 8].length) (baseStart_1063616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063616 prefixEnd_1063616 := by exact prefixLift 1063616
  have htrace : WordTrace (prefixWord ++ tailWord_1063616) baseStart_1063616 baseEnd_1063616 := by
    simpa [prefixWord, tailWord_1063616, baseEnd_1063616] using wordTrace_append hprefix tailTrace_1063616
  have hstable : (prefixWord ++ tailWord_1063616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063616).length < 2 ^ (prefixWord ++ tailWord_1063616).sum := by decide
  have hdescent : baseEnd_1063616 < baseStart_1063616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063647 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 5]
def baseStart_1063647 : Nat := 118140960795 + 1063647 * 2 ^ 59
def prefixEnd_1063647 : Nat := 4983230072969 + 3 ^ 40 * 1063647 * 2
def baseEnd_1063647 : Nat := 242738736761291204409281

theorem tailTrace_1063647 : CollatzResearch.WordTrace tailWord_1063647 prefixEnd_1063647 242738736761291204409281 := by
  unfold tailWord_1063647
  simp only [CollatzResearch.WordTrace]
  refine ⟨38794393177596050290301195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25862928785064033526867463 38794393177596050290301195)
  ·
    refine ⟨58191589766394075435451793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38794393177596050290301195 58191589766394075435451793)
    ·
      refine ⟨43643692324795556576588845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58191589766394075435451793 43643692324795556576588845)
      ·
        refine ⟨16366384621798333716220817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43643692324795556576588845 16366384621798333716220817)
        ·
          refine ⟨12274788466348750287165613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16366384621798333716220817 12274788466348750287165613)
          ·
            refine ⟨4603045674880781357687105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12274788466348750287165613 4603045674880781357687105)
            ·
              refine ⟨3452284256160586018265329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4603045674880781357687105 3452284256160586018265329)
              ·
                refine ⟨2589213192120439513698997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3452284256160586018265329 2589213192120439513698997)
                ·
                  refine ⟨242738736761291204409281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2589213192120439513698997 242738736761291204409281)
                  ·
                    rfl

theorem cell21_1063647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 5].length) (baseStart_1063647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063647 prefixEnd_1063647 := by exact prefixLift 1063647
  have htrace : WordTrace (prefixWord ++ tailWord_1063647) baseStart_1063647 baseEnd_1063647 := by
    simpa [prefixWord, tailWord_1063647, baseEnd_1063647] using wordTrace_append hprefix tailTrace_1063647
  have hstable : (prefixWord ++ tailWord_1063647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063647).length < 2 ^ (prefixWord ++ tailWord_1063647).sum := by decide
  have hdescent : baseEnd_1063647 < baseStart_1063647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063732 : List Nat := [2, 5, 1, 1, 4, 1, 2, 2, 3]
def baseStart_1063732 : Nat := 118140960795 + 1063732 * 2 ^ 59
def prefixEnd_1063732 : Nat := 4983230072969 + 3 ^ 40 * 1063732 * 2
def baseEnd_1063732 : Nat := 242758134919349945492441

theorem tailTrace_1063732 : CollatzResearch.WordTrace tailWord_1063732 prefixEnd_1063732 242758134919349945492441 := by
  unfold tailWord_1063732
  simp only [CollatzResearch.WordTrace]
  refine ⟨19398746691144054903572725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25864995588192073204763633 19398746691144054903572725)
  ·
    refine ⟨1818632502294755147209943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19398746691144054903572725 1818632502294755147209943)
    ·
      refine ⟨2727948753442132720814915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1818632502294755147209943 2727948753442132720814915)
      ·
        refine ⟨4091923130163199081222373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2727948753442132720814915 4091923130163199081222373)
        ·
          refine ⟨767235586905599827729195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4091923130163199081222373 767235586905599827729195)
          ·
            refine ⟨1150853380358399741593793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767235586905599827729195 1150853380358399741593793)
            ·
              refine ⟨863140035268799806195345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150853380358399741593793 863140035268799806195345)
              ·
                refine ⟨647355026451599854646509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863140035268799806195345 647355026451599854646509)
                ·
                  refine ⟨242758134919349945492441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647355026451599854646509 242758134919349945492441)
                  ·
                    rfl

theorem cell21_1063732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_1063732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063732 prefixEnd_1063732 := by exact prefixLift 1063732
  have htrace : WordTrace (prefixWord ++ tailWord_1063732) baseStart_1063732 baseEnd_1063732 := by
    simpa [prefixWord, tailWord_1063732, baseEnd_1063732] using wordTrace_append hprefix tailTrace_1063732
  have hstable : (prefixWord ++ tailWord_1063732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063732).length < 2 ^ (prefixWord ++ tailWord_1063732).sum := by decide
  have hdescent : baseEnd_1063732 < baseStart_1063732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063757 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1063757 : Nat := 118140960795 + 1063757 * 2 ^ 59
def prefixEnd_1063757 : Nat := 4983230072969 + 3 ^ 40 * 1063757 * 2
def baseEnd_1063757 : Nat := 242763840259955457575723

theorem tailTrace_1063757 : CollatzResearch.WordTrace tailWord_1063757 prefixEnd_1063757 242763840259955457575723 := by
  unfold tailWord_1063757
  simp only [CollatzResearch.WordTrace]
  refine ⟨38798405207197539076805525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25865603471465026051203683 38798405207197539076805525)
  ·
    refine ⟨1818675244087384644225259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38798405207197539076805525 1818675244087384644225259)
    ·
      refine ⟨2728012866131076966337889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1818675244087384644225259 2728012866131076966337889)
      ·
        refine ⟨2046009649598307724753417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2728012866131076966337889 2046009649598307724753417)
        ·
          refine ⟨1534507237198730793565063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2046009649598307724753417 1534507237198730793565063)
          ·
            refine ⟨2301760855798096190347595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534507237198730793565063 2301760855798096190347595)
            ·
              refine ⟨3452641283697144285521393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301760855798096190347595 3452641283697144285521393)
              ·
                refine ⟨2589480962772858214141045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3452641283697144285521393 2589480962772858214141045)
                ·
                  refine ⟨242763840259955457575723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2589480962772858214141045 242763840259955457575723)
                  ·
                    rfl

theorem cell21_1063757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1063757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063757 prefixEnd_1063757 := by exact prefixLift 1063757
  have htrace : WordTrace (prefixWord ++ tailWord_1063757) baseStart_1063757 baseEnd_1063757 := by
    simpa [prefixWord, tailWord_1063757, baseEnd_1063757] using wordTrace_append hprefix tailTrace_1063757
  have hstable : (prefixWord ++ tailWord_1063757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063757).length < 2 ^ (prefixWord ++ tailWord_1063757).sum := by decide
  have hdescent : baseEnd_1063757 < baseStart_1063757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063903 : List Nat := [1, 1, 2, 3, 14]
def baseStart_1063903 : Nat := 118140960795 + 1063903 * 2 ^ 59
def prefixEnd_1063903 : Nat := 4983230072969 + 3 ^ 40 * 1063903 * 2
def baseEnd_1063903 : Nat := 2997495795667798125211

theorem tailTrace_1063903 : CollatzResearch.WordTrace tailWord_1063903 prefixEnd_1063903 2997495795667798125211 := by
  unfold tailWord_1063903
  simp only [CollatzResearch.WordTrace]
  refine ⟨38803730264668606011620363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25869153509779070674413575 38803730264668606011620363)
  ·
    refine ⟨58205595397002909017430545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38803730264668606011620363 58205595397002909017430545)
    ·
      refine ⟨43654196547752181763072909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58205595397002909017430545 43654196547752181763072909)
      ·
        refine ⟨16370323705407068161152341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43654196547752181763072909 16370323705407068161152341)
        ·
          refine ⟨2997495795667798125211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 16370323705407068161152341 2997495795667798125211)
          ·
            rfl

theorem cell21_1063903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 14].length) (baseStart_1063903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063903 prefixEnd_1063903 := by exact prefixLift 1063903
  have htrace : WordTrace (prefixWord ++ tailWord_1063903) baseStart_1063903 baseEnd_1063903 := by
    simpa [prefixWord, tailWord_1063903, baseEnd_1063903] using wordTrace_append hprefix tailTrace_1063903
  have hstable : (prefixWord ++ tailWord_1063903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063903).length < 2 ^ (prefixWord ++ tailWord_1063903).sum := by decide
  have hdescent : baseEnd_1063903 < baseStart_1063903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063937 : List Nat := [1, 2, 4, 1, 2, 3, 3, 5]
def baseStart_1063937 : Nat := 118140960795 + 1063937 * 2 ^ 59
def prefixEnd_1063937 : Nat := 4983230072969 + 3 ^ 40 * 1063937 * 2
def baseEnd_1063937 : Nat := 80934972904105048191785

theorem tailTrace_1063937 : CollatzResearch.WordTrace tailWord_1063937 prefixEnd_1063937 80934972904105048191785 := by
  unfold tailWord_1063937
  simp only [CollatzResearch.WordTrace]
  refine ⟨38804970346545429818358065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25869980231030286545572043 38804970346545429818358065)
  ·
    refine ⟨29103727759909072363768549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38804970346545429818358065 29103727759909072363768549)
    ·
      refine ⟨5456948954982951068206603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29103727759909072363768549 5456948954982951068206603)
      ·
        refine ⟨8185423432474426602309905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5456948954982951068206603 8185423432474426602309905)
        ·
          refine ⟨6139067574355819951732429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8185423432474426602309905 6139067574355819951732429)
          ·
            refine ⟨2302150340383432481899661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6139067574355819951732429 2302150340383432481899661)
            ·
              refine ⟨863306377643787180712373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2302150340383432481899661 863306377643787180712373)
              ·
                refine ⟨80934972904105048191785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 863306377643787180712373 80934972904105048191785)
                ·
                  rfl

theorem cell21_1063937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 5].length) (baseStart_1063937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063937 prefixEnd_1063937 := by exact prefixLift 1063937
  have htrace : WordTrace (prefixWord ++ tailWord_1063937) baseStart_1063937 baseEnd_1063937 := by
    simpa [prefixWord, tailWord_1063937, baseEnd_1063937] using wordTrace_append hprefix tailTrace_1063937
  have hstable : (prefixWord ++ tailWord_1063937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063937).length < 2 ^ (prefixWord ++ tailWord_1063937).sum := by decide
  have hdescent : baseEnd_1063937 < baseStart_1063937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063979 : List Nat := [1, 1, 1, 1, 2, 1, 6, 8]
def baseStart_1063979 : Nat := 118140960795 + 1063979 * 2 ^ 59
def prefixEnd_1063979 : Nat := 4983230072969 + 3 ^ 40 * 1063979 * 2
def baseEnd_1063979 : Nat := 80938167894844134958423

theorem tailTrace_1063979 : CollatzResearch.WordTrace tailWord_1063979 prefixEnd_1063979 80938167894844134958423 := by
  unfold tailWord_1063979
  simp only [CollatzResearch.WordTrace]
  refine ⟨38806502212393270991386991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25871001474928847327591327 38806502212393270991386991)
  ·
    refine ⟨58209753318589906487080487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38806502212393270991386991 58209753318589906487080487)
    ·
      refine ⟨87314629977884859730620731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58209753318589906487080487 87314629977884859730620731)
      ·
        refine ⟨130971944966827289595931097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87314629977884859730620731 130971944966827289595931097)
        ·
          refine ⟨98228958725120467196948323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130971944966827289595931097 98228958725120467196948323)
          ·
            refine ⟨147343438087680700795422485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98228958725120467196948323 147343438087680700795422485)
            ·
              refine ⟨6906723660360032849785429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 147343438087680700795422485 6906723660360032849785429)
              ·
                refine ⟨80938167894844134958423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6906723660360032849785429 80938167894844134958423)
                ·
                  rfl

theorem cell21_1063979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 8].length) (baseStart_1063979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063979 prefixEnd_1063979 := by exact prefixLift 1063979
  have htrace : WordTrace (prefixWord ++ tailWord_1063979) baseStart_1063979 baseEnd_1063979 := by
    simpa [prefixWord, tailWord_1063979, baseEnd_1063979] using wordTrace_append hprefix tailTrace_1063979
  have hstable : (prefixWord ++ tailWord_1063979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063979).length < 2 ^ (prefixWord ++ tailWord_1063979).sum := by decide
  have hdescent : baseEnd_1063979 < baseStart_1063979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063996 : List Nat := [2, 2, 2, 2, 2, 3, 1, 7]
def baseStart_1063996 : Nat := 118140960795 + 1063996 * 2 ^ 59
def prefixEnd_1063996 : Nat := 4983230072969 + 3 ^ 40 * 1063996 * 2
def baseEnd_1063996 : Nat := 80939461105381384363967

theorem tailTrace_1063996 : CollatzResearch.WordTrace tailWord_1063996 prefixEnd_1063996 80939461105381384363967 := by
  unfold tailWord_1063996
  simp only [CollatzResearch.WordTrace]
  refine ⟨19403561126665841447377921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25871414835554455263170561 19403561126665841447377921)
  ·
    refine ⟨14552670844999381085533441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19403561126665841447377921 14552670844999381085533441)
    ·
      refine ⟨10914503133749535814150081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14552670844999381085533441 10914503133749535814150081)
      ·
        refine ⟨8185877350312151860612561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10914503133749535814150081 8185877350312151860612561)
        ·
          refine ⟨6139408012734113895459421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8185877350312151860612561 6139408012734113895459421)
          ·
            refine ⟨2302278004775292710797283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6139408012734113895459421 2302278004775292710797283)
            ·
              refine ⟨3453417007162939066195925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302278004775292710797283 3453417007162939066195925)
              ·
                refine ⟨80939461105381384363967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3453417007162939066195925 80939461105381384363967)
                ·
                  rfl

theorem cell21_1063996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_1063996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1063996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1063996 prefixEnd_1063996 := by exact prefixLift 1063996
  have htrace : WordTrace (prefixWord ++ tailWord_1063996) baseStart_1063996 baseEnd_1063996 := by
    simpa [prefixWord, tailWord_1063996, baseEnd_1063996] using wordTrace_append hprefix tailTrace_1063996
  have hstable : (prefixWord ++ tailWord_1063996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063996).length < 2 ^ (prefixWord ++ tailWord_1063996).sum := by decide
  have hdescent : baseEnd_1063996 < baseStart_1063996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064010 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_1064010 : Nat := 118140960795 + 1064010 * 2 ^ 59
def prefixEnd_1064010 : Nat := 4983230072969 + 3 ^ 40 * 1064010 * 2
def baseEnd_1064010 : Nat := 242821578306883239858539

theorem tailTrace_1064010 : CollatzResearch.WordTrace tailWord_1064010 prefixEnd_1064010 242821578306883239858539 := by
  unfold tailWord_1064010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9701908218820240821441371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25871755250187308857176989 9701908218820240821441371)
  ·
    refine ⟨14552862328230361232162057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9701908218820240821441371 14552862328230361232162057)
    ·
      refine ⟨10914646746172770924121543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14552862328230361232162057 10914646746172770924121543)
      ·
        refine ⟨16371970119259156386182315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10914646746172770924121543 16371970119259156386182315)
        ·
          refine ⟨24557955178888734579273473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16371970119259156386182315 24557955178888734579273473)
          ·
            refine ⟨18418466384166550934455105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24557955178888734579273473 18418466384166550934455105)
            ·
              refine ⟨13813849788124913200841329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18418466384166550934455105 13813849788124913200841329)
              ·
                refine ⟨10360387341093684900630997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13813849788124913200841329 10360387341093684900630997)
                ·
                  refine ⟨242821578306883239858539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10360387341093684900630997 242821578306883239858539)
                  ·
                    rfl

theorem cell21_1064010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_1064010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064010 prefixEnd_1064010 := by exact prefixLift 1064010
  have htrace : WordTrace (prefixWord ++ tailWord_1064010) baseStart_1064010 baseEnd_1064010 := by
    simpa [prefixWord, tailWord_1064010, baseEnd_1064010] using wordTrace_append hprefix tailTrace_1064010
  have hstable : (prefixWord ++ tailWord_1064010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064010).length < 2 ^ (prefixWord ++ tailWord_1064010).sum := by decide
  have hdescent : baseEnd_1064010 < baseStart_1064010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064013 : List Nat := [1, 6, 1, 1, 1, 4, 7]
def baseStart_1064013 : Nat := 118140960795 + 1064013 * 2 ^ 59
def prefixEnd_1064013 : Nat := 4983230072969 + 3 ^ 40 * 1064013 * 2
def baseEnd_1064013 : Nat := 26980251438639544589837

theorem tailTrace_1064013 : CollatzResearch.WordTrace tailWord_1064013 prefixEnd_1064013 26980251438639544589837 := by
  unfold tailWord_1064013
  simp only [CollatzResearch.WordTrace]
  refine ⟨38807742294270094798124693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25871828196180063198749795 38807742294270094798124693)
  ·
    refine ⟨1819112920043910693662095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38807742294270094798124693 1819112920043910693662095)
    ·
      refine ⟨2728669380065866040493143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1819112920043910693662095 2728669380065866040493143)
      ·
        refine ⟨4093004070098799060739715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2728669380065866040493143 4093004070098799060739715)
        ·
          refine ⟨6139506105148198591109573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4093004070098799060739715 6139506105148198591109573)
          ·
            refine ⟨1151157394715287235833045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6139506105148198591109573 1151157394715287235833045)
            ·
              refine ⟨26980251438639544589837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1151157394715287235833045 26980251438639544589837)
              ·
                rfl

theorem cell21_1064013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 7].length) (baseStart_1064013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064013 prefixEnd_1064013 := by exact prefixLift 1064013
  have htrace : WordTrace (prefixWord ++ tailWord_1064013) baseStart_1064013 baseEnd_1064013 := by
    simpa [prefixWord, tailWord_1064013, baseEnd_1064013] using wordTrace_append hprefix tailTrace_1064013
  have hstable : (prefixWord ++ tailWord_1064013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064013).length < 2 ^ (prefixWord ++ tailWord_1064013).sum := by decide
  have hdescent : baseEnd_1064013 < baseStart_1064013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064030 : List Nat := [4, 4, 1, 1, 1, 1, 1, 8]
def baseStart_1064030 : Nat := 118140960795 + 1064030 * 2 ^ 59
def prefixEnd_1064030 : Nat := 4983230072969 + 3 ^ 40 * 1064030 * 2
def baseEnd_1064030 : Nat := 80942047526455883175055

theorem tailTrace_1064030 : CollatzResearch.WordTrace tailWord_1064030 prefixEnd_1064030 80942047526455883175055 := by
  unfold tailWord_1064030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4851045291901063337686693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25872241556805671134329029 4851045291901063337686693)
  ·
    refine ⟨909570992231449375816255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4851045291901063337686693 909570992231449375816255)
    ·
      refine ⟨1364356488347174063724383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 909570992231449375816255 1364356488347174063724383)
      ·
        refine ⟨2046534732520761095586575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1364356488347174063724383 2046534732520761095586575)
        ·
          refine ⟨3069802098781141643379863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2046534732520761095586575 3069802098781141643379863)
          ·
            refine ⟨4604703148171712465069795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3069802098781141643379863 4604703148171712465069795)
            ·
              refine ⟨6907054722257568697604693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4604703148171712465069795 6907054722257568697604693)
              ·
                refine ⟨80942047526455883175055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6907054722257568697604693 80942047526455883175055)
                ·
                  rfl

theorem cell21_1064030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_1064030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064030 prefixEnd_1064030 := by exact prefixLift 1064030
  have htrace : WordTrace (prefixWord ++ tailWord_1064030) baseStart_1064030 baseEnd_1064030 := by
    simpa [prefixWord, tailWord_1064030, baseEnd_1064030] using wordTrace_append hprefix tailTrace_1064030
  have hstable : (prefixWord ++ tailWord_1064030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064030).length < 2 ^ (prefixWord ++ tailWord_1064030).sum := by decide
  have hdescent : baseEnd_1064030 < baseStart_1064030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064055 : List Nat := [1, 1, 3, 1, 1, 4, 1, 9]
def baseStart_1064055 : Nat := 118140960795 + 1064055 * 2 ^ 59
def prefixEnd_1064055 : Nat := 4983230072969 + 3 ^ 40 * 1064055 * 2
def baseEnd_1064055 : Nat := 80943949306657720536149

theorem tailTrace_1064055 : CollatzResearch.WordTrace tailWord_1064055 prefixEnd_1064055 80943949306657720536149 := by
  unfold tailWord_1064055
  simp only [CollatzResearch.WordTrace]
  refine ⟨38809274160117935971153619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25872849440078623980769079 38809274160117935971153619)
  ·
    refine ⟨58213911240176903956730429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38809274160117935971153619 58213911240176903956730429)
    ·
      refine ⟨21830216715066338983773911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58213911240176903956730429 21830216715066338983773911)
      ·
        refine ⟨32745325072599508475660867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21830216715066338983773911 32745325072599508475660867)
        ·
          refine ⟨49117987608899262713491301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32745325072599508475660867 49117987608899262713491301)
          ·
            refine ⟨9209622676668611758779619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49117987608899262713491301 9209622676668611758779619)
            ·
              refine ⟨13814434015002917638169429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9209622676668611758779619 13814434015002917638169429)
              ·
                refine ⟨80943949306657720536149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13814434015002917638169429 80943949306657720536149)
                ·
                  rfl

theorem cell21_1064055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 9].length) (baseStart_1064055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064055 prefixEnd_1064055 := by exact prefixLift 1064055
  have htrace : WordTrace (prefixWord ++ tailWord_1064055) baseStart_1064055 baseEnd_1064055 := by
    simpa [prefixWord, tailWord_1064055, baseEnd_1064055] using wordTrace_append hprefix tailTrace_1064055
  have hstable : (prefixWord ++ tailWord_1064055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064055).length < 2 ^ (prefixWord ++ tailWord_1064055).sum := by decide
  have hdescent : baseEnd_1064055 < baseStart_1064055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064072 : List Nat := [2, 1, 3, 4, 2, 9]
def baseStart_1064072 : Nat := 118140960795 + 1064072 * 2 ^ 59
def prefixEnd_1064072 : Nat := 4983230072969 + 3 ^ 40 * 1064072 * 2
def baseEnd_1064072 : Nat := 8993915835243885549077

theorem tailTrace_1064072 : CollatzResearch.WordTrace tailWord_1064072 prefixEnd_1064072 8993915835243885549077 := by
  unfold tailWord_1064072
  simp only [CollatzResearch.WordTrace]
  refine ⟨19404947100528173937261235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25873262800704231916348313 19404947100528173937261235)
  ·
    refine ⟨29107420650792260905891853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19404947100528173937261235 29107420650792260905891853)
    ·
      refine ⟨10915282744047097839709445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29107420650792260905891853 10915282744047097839709445)
      ·
        refine ⟨2046615514508830844945521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10915282744047097839709445 2046615514508830844945521)
        ·
          refine ⟨1534961635881623133709141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2046615514508830844945521 1534961635881623133709141)
          ·
            refine ⟨8993915835243885549077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1534961635881623133709141 8993915835243885549077)
            ·
              rfl

theorem cell21_1064072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 9].length) (baseStart_1064072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064072 prefixEnd_1064072 := by exact prefixLift 1064072
  have htrace : WordTrace (prefixWord ++ tailWord_1064072) baseStart_1064072 baseEnd_1064072 := by
    simpa [prefixWord, tailWord_1064072, baseEnd_1064072] using wordTrace_append hprefix tailTrace_1064072
  have hstable : (prefixWord ++ tailWord_1064072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064072).length < 2 ^ (prefixWord ++ tailWord_1064072).sum := by decide
  have hdescent : baseEnd_1064072 < baseStart_1064072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064078 : List Nat := [4, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_1064078 : Nat := 118140960795 + 1064078 * 2 ^ 59
def prefixEnd_1064078 : Nat := 4983230072969 + 3 ^ 40 * 1064078 * 2
def baseEnd_1064078 : Nat := 242837096833330232725067

theorem tailTrace_1064078 : CollatzResearch.WordTrace tailWord_1064078 prefixEnd_1064078 242837096833330232725067 := by
  unfold tailWord_1064078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4851264129879326362405111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25873408692689740599493925 4851264129879326362405111)
  ·
    refine ⟨7276896194818989543607667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4851264129879326362405111 7276896194818989543607667)
    ·
      refine ⟨10915344292228484315411501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7276896194818989543607667 10915344292228484315411501)
      ·
        refine ⟨4093254109585681618279313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10915344292228484315411501 4093254109585681618279313)
        ·
          refine ⟨3069940582189261213709485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4093254109585681618279313 3069940582189261213709485)
          ·
            refine ⟨1151227718320972955141057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3069940582189261213709485 1151227718320972955141057)
            ·
              refine ⟨863420788740729716355793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151227718320972955141057 863420788740729716355793)
              ·
                refine ⟨647565591555547287266845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863420788740729716355793 647565591555547287266845)
                ·
                  refine ⟨242837096833330232725067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647565591555547287266845 242837096833330232725067)
                  ·
                    rfl

theorem cell21_1064078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_1064078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064078 prefixEnd_1064078 := by exact prefixLift 1064078
  have htrace : WordTrace (prefixWord ++ tailWord_1064078) baseStart_1064078 baseEnd_1064078 := by
    simpa [prefixWord, tailWord_1064078, baseEnd_1064078] using wordTrace_append hprefix tailTrace_1064078
  have hstable : (prefixWord ++ tailWord_1064078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064078).length < 2 ^ (prefixWord ++ tailWord_1064078).sum := by decide
  have hdescent : baseEnd_1064078 < baseStart_1064078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064103 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 7]
def baseStart_1064103 : Nat := 118140960795 + 1064103 * 2 ^ 59
def prefixEnd_1064103 : Nat := 4983230072969 + 3 ^ 40 * 1064103 * 2
def baseEnd_1064103 : Nat := 242842802173935744808349

theorem tailTrace_1064103 : CollatzResearch.WordTrace tailWord_1064103 prefixEnd_1064103 242842802173935744808349 := by
  unfold tailWord_1064103
  simp only [CollatzResearch.WordTrace]
  refine ⟨38811024863944040168900963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25874016575962693445933975 38811024863944040168900963)
  ·
    refine ⟨58216537295916060253351445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38811024863944040168900963 58216537295916060253351445)
    ·
      refine ⟨2728900185746065324375849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58216537295916060253351445 2728900185746065324375849)
      ·
        refine ⟨2046675139309548993281887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2728900185746065324375849 2046675139309548993281887)
        ·
          refine ⟨3070012708964323489922831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2046675139309548993281887 3070012708964323489922831)
          ·
            refine ⟨4605019063446485234884247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3070012708964323489922831 4605019063446485234884247)
            ·
              refine ⟨6907528595169727852326371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4605019063446485234884247 6907528595169727852326371)
              ·
                refine ⟨10361292892754591778489557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6907528595169727852326371 10361292892754591778489557)
                ·
                  refine ⟨242842802173935744808349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10361292892754591778489557 242842802173935744808349)
                  ·
                    rfl

theorem cell21_1064103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 7].length) (baseStart_1064103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064103 prefixEnd_1064103 := by exact prefixLift 1064103
  have htrace : WordTrace (prefixWord ++ tailWord_1064103) baseStart_1064103 baseEnd_1064103 := by
    simpa [prefixWord, tailWord_1064103, baseEnd_1064103] using wordTrace_append hprefix tailTrace_1064103
  have hstable : (prefixWord ++ tailWord_1064103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064103).length < 2 ^ (prefixWord ++ tailWord_1064103).sum := by decide
  have hdescent : baseEnd_1064103 < baseStart_1064103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064106 : List Nat := [3, 1, 5, 1, 1, 2, 3, 5]
def baseStart_1064106 : Nat := 118140960795 + 1064106 * 2 ^ 59
def prefixEnd_1064106 : Nat := 4983230072969 + 3 ^ 40 * 1064106 * 2
def baseEnd_1064106 : Nat := 80947828938269468752781

theorem tailTrace_1064106 : CollatzResearch.WordTrace tailWord_1064106 prefixEnd_1064106 80947828938269468752781 := by
  unfold tailWord_1064106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9702783570733292920315043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25874089521955447787506781 9702783570733292920315043)
  ·
    refine ⟨14554175356099939380472565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9702783570733292920315043 14554175356099939380472565)
    ·
      refine ⟨1364453939634369316919303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14554175356099939380472565 1364453939634369316919303)
      ·
        refine ⟨2046680909451553975378955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1364453939634369316919303 2046680909451553975378955)
        ·
          refine ⟨3070021364177330963068433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2046680909451553975378955 3070021364177330963068433)
          ·
            refine ⟨2302516023132998222301325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3070021364177330963068433 2302516023132998222301325)
            ·
              refine ⟨863443508674874333362997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2302516023132998222301325 863443508674874333362997)
              ·
                refine ⟨80947828938269468752781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 863443508674874333362997 80947828938269468752781)
                ·
                  rfl

theorem cell21_1064106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_1064106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064106 prefixEnd_1064106 := by exact prefixLift 1064106
  have htrace : WordTrace (prefixWord ++ tailWord_1064106) baseStart_1064106 baseEnd_1064106 := by
    simpa [prefixWord, tailWord_1064106, baseEnd_1064106] using wordTrace_append hprefix tailTrace_1064106
  have hstable : (prefixWord ++ tailWord_1064106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064106).length < 2 ^ (prefixWord ++ tailWord_1064106).sum := by decide
  have hdescent : baseEnd_1064106 < baseStart_1064106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064193 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 6]
def baseStart_1064193 : Nat := 118140960795 + 1064193 * 2 ^ 59
def prefixEnd_1064193 : Nat := 4983230072969 + 3 ^ 40 * 1064193 * 2
def baseEnd_1064193 : Nat := 242863341400115588308165

theorem tailTrace_1064193 : CollatzResearch.WordTrace tailWord_1064193 prefixEnd_1064193 242863341400115588308165 := by
  unfold tailWord_1064193
  simp only [CollatzResearch.WordTrace]
  refine ⟨38814307433617985539677233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25876204955745323693118155 38814307433617985539677233)
  ·
    refine ⟨29110730575213489154757925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38814307433617985539677233 29110730575213489154757925)
    ·
      refine ⟨5458261982852529216517111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29110730575213489154757925 5458261982852529216517111)
      ·
        refine ⟨8187392974278793824775667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5458261982852529216517111 8187392974278793824775667)
        ·
          refine ⟨12281089461418190737163501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8187392974278793824775667 12281089461418190737163501)
          ·
            refine ⟨4605408548031821526436313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12281089461418190737163501 4605408548031821526436313)
            ·
              refine ⟨3454056411023866144827235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4605408548031821526436313 3454056411023866144827235)
              ·
                refine ⟨5181084616535799217240853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454056411023866144827235 5181084616535799217240853)
                ·
                  refine ⟨242863341400115588308165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5181084616535799217240853 242863341400115588308165)
                  ·
                    rfl

theorem cell21_1064193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_1064193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064193 prefixEnd_1064193 := by exact prefixLift 1064193
  have htrace : WordTrace (prefixWord ++ tailWord_1064193) baseStart_1064193 baseEnd_1064193 := by
    simpa [prefixWord, tailWord_1064193, baseEnd_1064193] using wordTrace_append hprefix tailTrace_1064193
  have hstable : (prefixWord ++ tailWord_1064193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064193).length < 2 ^ (prefixWord ++ tailWord_1064193).sum := by decide
  have hdescent : baseEnd_1064193 < baseStart_1064193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064196 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 5]
def baseStart_1064196 : Nat := 118140960795 + 1064196 * 2 ^ 59
def prefixEnd_1064196 : Nat := 4983230072969 + 3 ^ 40 * 1064196 * 2
def baseEnd_1064196 : Nat := 242864026040988249758159

theorem tailTrace_1064196 : CollatzResearch.WordTrace tailWord_1064196 prefixEnd_1064196 242864026040988249758159 := by
  unfold tailWord_1064196
  simp only [CollatzResearch.WordTrace]
  refine ⟨19407208426303558526018221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25876277901738078034690961 19407208426303558526018221)
  ·
    refine ⟨7277703159863834447256833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19407208426303558526018221 7277703159863834447256833)
    ·
      refine ⟨5458277369897875835442625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7277703159863834447256833 5458277369897875835442625)
      ·
        refine ⟨4093708027423406876581969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5458277369897875835442625 4093708027423406876581969)
        ·
          refine ⟨3070281020567555157436477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4093708027423406876581969 3070281020567555157436477)
          ·
            refine ⟨1151355382712833184038679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3070281020567555157436477 1151355382712833184038679)
            ·
              refine ⟨1727033074069249776058019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151355382712833184038679 1727033074069249776058019)
              ·
                refine ⟨2590549611103874664087029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727033074069249776058019 2590549611103874664087029)
                ·
                  refine ⟨242864026040988249758159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2590549611103874664087029 242864026040988249758159)
                  ·
                    rfl

theorem cell21_1064196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_1064196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064196 prefixEnd_1064196 := by exact prefixLift 1064196
  have htrace : WordTrace (prefixWord ++ tailWord_1064196) baseStart_1064196 baseEnd_1064196 := by
    simpa [prefixWord, tailWord_1064196, baseEnd_1064196] using wordTrace_append hprefix tailTrace_1064196
  have hstable : (prefixWord ++ tailWord_1064196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064196).length < 2 ^ (prefixWord ++ tailWord_1064196).sum := by decide
  have hdescent : baseEnd_1064196 < baseStart_1064196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064334 : List Nat := [4, 1, 1, 4, 2, 2, 2, 5]
def baseStart_1064334 : Nat := 118140960795 + 1064334 * 2 ^ 59
def prefixEnd_1064334 : Nat := 4983230072969 + 3 ^ 40 * 1064334 * 2
def baseEnd_1064334 : Nat := 80965173173710225485959

theorem tailTrace_1064334 : CollatzResearch.WordTrace tailWord_1064334 prefixEnd_1064334 80965173173710225485959 := by
  unfold tailWord_1064334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4852431265763395827570007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25879633417404777747040037 4852431265763395827570007)
  ·
    refine ⟨7278646898645093741355011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4852431265763395827570007 7278646898645093741355011)
    ·
      refine ⟨10917970347967640612032517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7278646898645093741355011 10917970347967640612032517)
      ·
        refine ⟨2047119440243932614756097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10917970347967640612032517 2047119440243932614756097)
        ·
          refine ⟨1535339580182949461067073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2047119440243932614756097 1535339580182949461067073)
          ·
            refine ⟨1151504685137212095800305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1535339580182949461067073 1151504685137212095800305)
            ·
              refine ⟨863628513852909071850229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151504685137212095800305 863628513852909071850229)
              ·
                refine ⟨80965173173710225485959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 863628513852909071850229 80965173173710225485959)
                ·
                  rfl

theorem cell21_1064334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_1064334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064334 prefixEnd_1064334 := by exact prefixLift 1064334
  have htrace : WordTrace (prefixWord ++ tailWord_1064334) baseStart_1064334 baseEnd_1064334 := by
    simpa [prefixWord, tailWord_1064334, baseEnd_1064334] using wordTrace_append hprefix tailTrace_1064334
  have hstable : (prefixWord ++ tailWord_1064334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064334).length < 2 ^ (prefixWord ++ tailWord_1064334).sum := by decide
  have hdescent : baseEnd_1064334 < baseStart_1064334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064438 : List Nat := [5, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1064438 : Nat := 118140960795 + 1064438 * 2 ^ 59
def prefixEnd_1064438 : Nat := 4983230072969 + 3 ^ 40 * 1064438 * 2
def baseEnd_1064438 : Nat := 242919253738049606724331

theorem tailTrace_1064438 : CollatzResearch.WordTrace tailWord_1064438 prefixEnd_1064438 242919253738049606724331 := by
  unfold tailWord_1064438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2426452707358149523896623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25882162211820261588230645 2426452707358149523896623)
  ·
    refine ⟨3639679061037224285844935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2426452707358149523896623 3639679061037224285844935)
    ·
      refine ⟨5459518591555836428767403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3639679061037224285844935 5459518591555836428767403)
      ·
        refine ⟨8189277887333754643151105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5459518591555836428767403 8189277887333754643151105)
        ·
          refine ⟨6141958415500315982363329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8189277887333754643151105 6141958415500315982363329)
          ·
            refine ⟨4606468811625236986772497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6141958415500315982363329 4606468811625236986772497)
            ·
              refine ⟨3454851608718927740079373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4606468811625236986772497 3454851608718927740079373)
              ·
                refine ⟨1295569353269597902529765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3454851608718927740079373 1295569353269597902529765)
                ·
                  refine ⟨242919253738049606724331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1295569353269597902529765 242919253738049606724331)
                  ·
                    rfl

theorem cell21_1064438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1064438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064438 prefixEnd_1064438 := by exact prefixLift 1064438
  have htrace : WordTrace (prefixWord ++ tailWord_1064438) baseStart_1064438 baseEnd_1064438 := by
    simpa [prefixWord, tailWord_1064438, baseEnd_1064438] using wordTrace_append hprefix tailTrace_1064438
  have hstable : (prefixWord ++ tailWord_1064438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064438).length < 2 ^ (prefixWord ++ tailWord_1064438).sum := by decide
  have hdescent : baseEnd_1064438 < baseStart_1064438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064483 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 5]
def baseStart_1064483 : Nat := 118140960795 + 1064483 * 2 ^ 59
def prefixEnd_1064483 : Nat := 4983230072969 + 3 ^ 40 * 1064483 * 2
def baseEnd_1064483 : Nat := 242929523351139528474239

theorem tailTrace_1064483 : CollatzResearch.WordTrace tailWord_1064483 prefixEnd_1064483 242929523351139528474239 := by
  unfold tailWord_1064483
  simp only [CollatzResearch.WordTrace]
  refine ⟨38824884602567365067734103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25883256401711576711822735 38824884602567365067734103)
  ·
    refine ⟨58237326903851047601601155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38824884602567365067734103 58237326903851047601601155)
    ·
      refine ⟨87355990355776571402401733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58237326903851047601601155 87355990355776571402401733)
      ·
        refine ⟨16379248191708107137950325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87355990355776571402401733 16379248191708107137950325)
        ·
          refine ⟨1535554517972635044182843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16379248191708107137950325 1535554517972635044182843)
          ·
            refine ⟨2303331776958952566274265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535554517972635044182843 2303331776958952566274265)
            ·
              refine ⟨1727498832719214424705699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2303331776958952566274265 1727498832719214424705699)
              ·
                refine ⟨2591248249078821637058549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727498832719214424705699 2591248249078821637058549)
                ·
                  refine ⟨242929523351139528474239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2591248249078821637058549 242929523351139528474239)
                  ·
                    rfl

theorem cell21_1064483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 5].length) (baseStart_1064483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064483 prefixEnd_1064483 := by exact prefixLift 1064483
  have htrace : WordTrace (prefixWord ++ tailWord_1064483) baseStart_1064483 baseEnd_1064483 := by
    simpa [prefixWord, tailWord_1064483, baseEnd_1064483] using wordTrace_append hprefix tailTrace_1064483
  have hstable : (prefixWord ++ tailWord_1064483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064483).length < 2 ^ (prefixWord ++ tailWord_1064483).sum := by decide
  have hdescent : baseEnd_1064483 < baseStart_1064483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064511 : List Nat := [1, 1, 2, 2, 3, 4, 1, 7]
def baseStart_1064511 : Nat := 118140960795 + 1064511 * 2 ^ 59
def prefixEnd_1064511 : Nat := 4983230072969 + 3 ^ 40 * 1064511 * 2
def baseEnd_1064511 : Nat := 80978637777539234002505

theorem tailTrace_1064511 : CollatzResearch.WordTrace tailWord_1064511 prefixEnd_1064511 80978637777539234002505 := by
  unfold tailWord_1064511
  simp only [CollatzResearch.WordTrace]
  refine ⟨38825905846465925849753387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25883937230977283899835591 38825905846465925849753387)
  ·
    refine ⟨58238858769698888774630081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38825905846465925849753387 58238858769698888774630081)
    ·
      refine ⟨43679144077274166580972561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58238858769698888774630081 43679144077274166580972561)
      ·
        refine ⟨32759358057955624935729421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43679144077274166580972561 32759358057955624935729421)
        ·
          refine ⟨12284759271733359350898533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32759358057955624935729421 12284759271733359350898533)
          ·
            refine ⟨2303392363450004878293475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12284759271733359350898533 2303392363450004878293475)
            ·
              refine ⟨3455088545175007317440213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303392363450004878293475 3455088545175007317440213)
              ·
                refine ⟨80978637777539234002505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3455088545175007317440213 80978637777539234002505)
                ·
                  rfl

theorem cell21_1064511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 7].length) (baseStart_1064511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064511 prefixEnd_1064511 := by exact prefixLift 1064511
  have htrace : WordTrace (prefixWord ++ tailWord_1064511) baseStart_1064511 baseEnd_1064511 := by
    simpa [prefixWord, tailWord_1064511, baseEnd_1064511] using wordTrace_append hprefix tailTrace_1064511
  have hstable : (prefixWord ++ tailWord_1064511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064511).length < 2 ^ (prefixWord ++ tailWord_1064511).sum := by decide
  have hdescent : baseEnd_1064511 < baseStart_1064511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064534 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1064534 : Nat := 118140960795 + 1064534 * 2 ^ 59
def prefixEnd_1064534 : Nat := 4983230072969 + 3 ^ 40 * 1064534 * 2
def baseEnd_1064534 : Nat := 242941162245974773124135

theorem tailTrace_1064534 : CollatzResearch.WordTrace tailWord_1064534 prefixEnd_1064534 242941162245974773124135 := by
  unfold tailWord_1064534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2426671545336412548615041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25884496483588400518560437 2426671545336412548615041)
  ·
    refine ⟨1820003659002309411461281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2426671545336412548615041 1820003659002309411461281)
    ·
      refine ⟨1365002744251732058595961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1820003659002309411461281 1365002744251732058595961)
      ·
        refine ⟨1023752058188799043946971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1365002744251732058595961 1023752058188799043946971)
        ·
          refine ⟨1535628087283198565920457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023752058188799043946971 1535628087283198565920457)
          ·
            refine ⟨1151721065462398924440343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1535628087283198565920457 1151721065462398924440343)
            ·
              refine ⟨1727581598193598386660515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151721065462398924440343 1727581598193598386660515)
              ·
                refine ⟨2591372397290397579990773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727581598193598386660515 2591372397290397579990773)
                ·
                  refine ⟨242941162245974773124135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2591372397290397579990773 242941162245974773124135)
                  ·
                    rfl

theorem cell21_1064534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1064534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064534 prefixEnd_1064534 := by exact prefixLift 1064534
  have htrace : WordTrace (prefixWord ++ tailWord_1064534) baseStart_1064534 baseEnd_1064534 := by
    simpa [prefixWord, tailWord_1064534, baseEnd_1064534] using wordTrace_append hprefix tailTrace_1064534
  have hstable : (prefixWord ++ tailWord_1064534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064534).length < 2 ^ (prefixWord ++ tailWord_1064534).sum := by decide
  have hdescent : baseEnd_1064534 < baseStart_1064534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064590 : List Nat := [4, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_1064590 : Nat := 118140960795 + 1064590 * 2 ^ 59
def prefixEnd_1064590 : Nat := 4983230072969 + 3 ^ 40 * 1064590 * 2
def baseEnd_1064590 : Nat := 242953942208931120190687

theorem tailTrace_1064590 : CollatzResearch.WordTrace tailWord_1064590 prefixEnd_1064590 242953942208931120190687 := by
  unfold tailWord_1064590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4853598401647465292734903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25885858142119814894586149 4853598401647465292734903)
  ·
    refine ⟨7280397602471197939102355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4853598401647465292734903 7280397602471197939102355)
    ·
      refine ⟨10920596403706796908653533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7280397602471197939102355 10920596403706796908653533)
      ·
        refine ⟨4095223651390048840745075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10920596403706796908653533 4095223651390048840745075)
        ·
          refine ⟨6142835477085073261117613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4095223651390048840745075 6142835477085073261117613)
          ·
            refine ⟨2303563303906902472919105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6142835477085073261117613 2303563303906902472919105)
            ·
              refine ⟨1727672477930176854689329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2303563303906902472919105 1727672477930176854689329)
              ·
                refine ⟨1295754358447632641016997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1727672477930176854689329 1295754358447632641016997)
                ·
                  refine ⟨242953942208931120190687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1295754358447632641016997 242953942208931120190687)
                  ·
                    rfl

theorem cell21_1064590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_1064590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064590 prefixEnd_1064590 := by exact prefixLift 1064590
  have htrace : WordTrace (prefixWord ++ tailWord_1064590) baseStart_1064590 baseEnd_1064590 := by
    simpa [prefixWord, tailWord_1064590, baseEnd_1064590] using wordTrace_append hprefix tailTrace_1064590
  have hstable : (prefixWord ++ tailWord_1064590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064590).length < 2 ^ (prefixWord ++ tailWord_1064590).sum := by decide
  have hdescent : baseEnd_1064590 < baseStart_1064590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064666 : List Nat := [3, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_1064666 : Nat := 118140960795 + 1064666 * 2 ^ 59
def prefixEnd_1064666 : Nat := 4983230072969 + 3 ^ 40 * 1064666 * 2
def baseEnd_1064666 : Nat := 242971286444371876923865

theorem tailTrace_1064666 : CollatzResearch.WordTrace tailWord_1064666 prefixEnd_1064666 242971286444371876923865 := by
  unfold tailWord_1064666
  simp only [CollatzResearch.WordTrace]
  refine ⟨9707889790226096830411463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25887706107269591547763901 9707889790226096830411463)
  ·
    refine ⟨14561834685339145245617195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9707889790226096830411463 14561834685339145245617195)
    ·
      refine ⟨21842752028008717868425793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14561834685339145245617195 21842752028008717868425793)
      ·
        refine ⟨16382064021006538401319345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21842752028008717868425793 16382064021006538401319345)
        ·
          refine ⟨12286548015754903800989509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16382064021006538401319345 12286548015754903800989509)
          ·
            refine ⟨2303727752954044462685533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12286548015754903800989509 2303727752954044462685533)
            ·
              refine ⟨863897907357766673507075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2303727752954044462685533 863897907357766673507075)
              ·
                refine ⟨1295846861036650010260613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863897907357766673507075 1295846861036650010260613)
                ·
                  refine ⟨242971286444371876923865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1295846861036650010260613 242971286444371876923865)
                  ·
                    rfl

theorem cell21_1064666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_1064666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064666 prefixEnd_1064666 := by exact prefixLift 1064666
  have htrace : WordTrace (prefixWord ++ tailWord_1064666) baseStart_1064666 baseEnd_1064666 := by
    simpa [prefixWord, tailWord_1064666, baseEnd_1064666] using wordTrace_append hprefix tailTrace_1064666
  have hstable : (prefixWord ++ tailWord_1064666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064666).length < 2 ^ (prefixWord ++ tailWord_1064666).sum := by decide
  have hdescent : baseEnd_1064666 < baseStart_1064666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064680 : List Nat := [2, 1, 4, 1, 3, 1, 4, 5]
def baseStart_1064680 : Nat := 118140960795 + 1064680 * 2 ^ 59
def prefixEnd_1064680 : Nat := 4983230072969 + 3 ^ 40 * 1064680 * 2
def baseEnd_1064680 : Nat := 80991493811703654563501

theorem tailTrace_1064680 : CollatzResearch.WordTrace tailWord_1064680 prefixEnd_1064680 80991493811703654563501 := by
  unfold tailWord_1064680
  simp only [CollatzResearch.WordTrace]
  refine ⟨19416034891426833856327747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25888046521902445141770329 19416034891426833856327747)
  ·
    refine ⟨29124052337140250784491621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19416034891426833856327747 29124052337140250784491621)
    ·
      refine ⟨5460759813213797022092179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29124052337140250784491621 5460759813213797022092179)
      ·
        refine ⟨8191139719820695533138269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5460759813213797022092179 8191139719820695533138269)
        ·
          refine ⟨3071677394932760824926851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8191139719820695533138269 3071677394932760824926851)
          ·
            refine ⟨4607516092399141237390277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3071677394932760824926851 4607516092399141237390277)
            ·
              refine ⟨863909267324838982010677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4607516092399141237390277 863909267324838982010677)
              ·
                refine ⟨80991493811703654563501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 863909267324838982010677 80991493811703654563501)
                ·
                  rfl

theorem cell21_1064680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 5].length) (baseStart_1064680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064680 prefixEnd_1064680 := by exact prefixLift 1064680
  have htrace : WordTrace (prefixWord ++ tailWord_1064680) baseStart_1064680 baseEnd_1064680 := by
    simpa [prefixWord, tailWord_1064680, baseEnd_1064680] using wordTrace_append hprefix tailTrace_1064680
  have hstable : (prefixWord ++ tailWord_1064680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064680).length < 2 ^ (prefixWord ++ tailWord_1064680).sum := by decide
  have hdescent : baseEnd_1064680 < baseStart_1064680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064717 : List Nat := [1, 7, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1064717 : Nat := 118140960795 + 1064717 * 2 ^ 59
def prefixEnd_1064717 : Nat := 4983230072969 + 3 ^ 40 * 1064717 * 2
def baseEnd_1064717 : Nat := 242982925339207121573761

theorem tailTrace_1064717 : CollatzResearch.WordTrace tailWord_1064717 prefixEnd_1064717 242982925339207121573761 := by
  unfold tailWord_1064717
  simp only [CollatzResearch.WordTrace]
  refine ⟨38833419283719623031752405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25888946189146415354501603 38833419283719623031752405)
  ·
    refine ⟨910158264462178664806697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 38833419283719623031752405 910158264462178664806697)
    ·
      refine ⟨682618698346633998605023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 910158264462178664806697 682618698346633998605023)
      ·
        refine ⟨1023928047519950997907535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682618698346633998605023 1023928047519950997907535)
        ·
          refine ⟨1535892071279926496861303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023928047519950997907535 1535892071279926496861303)
          ·
            refine ⟨2303838106919889745291955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535892071279926496861303 2303838106919889745291955)
            ·
              refine ⟨3455757160379834617937933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303838106919889745291955 3455757160379834617937933)
              ·
                refine ⟨1295908935142437981726725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3455757160379834617937933 1295908935142437981726725)
                ·
                  refine ⟨242982925339207121573761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1295908935142437981726725 242982925339207121573761)
                  ·
                    rfl

theorem cell21_1064717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1064717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064717 prefixEnd_1064717 := by exact prefixLift 1064717
  have htrace : WordTrace (prefixWord ++ tailWord_1064717) baseStart_1064717 baseEnd_1064717 := by
    simpa [prefixWord, tailWord_1064717, baseEnd_1064717] using wordTrace_append hprefix tailTrace_1064717
  have hstable : (prefixWord ++ tailWord_1064717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064717).length < 2 ^ (prefixWord ++ tailWord_1064717).sum := by decide
  have hdescent : baseEnd_1064717 < baseStart_1064717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064725 : List Nat := [1, 3, 2, 1, 2, 4, 1, 3, 4]
def baseStart_1064725 : Nat := 118140960795 + 1064725 * 2 ^ 59
def prefixEnd_1064725 : Nat := 4983230072969 + 3 ^ 40 * 1064725 * 2
def baseEnd_1064725 : Nat := 242984751048200885440411

theorem tailTrace_1064725 : CollatzResearch.WordTrace tailWord_1064725 prefixEnd_1064725 242984751048200885440411 := by
  unfold tailWord_1064725
  simp only [CollatzResearch.WordTrace]
  refine ⟨38833711067690640398043629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25889140711793760265362419 38833711067690640398043629)
  ·
    refine ⟨14562641650383990149266361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38833711067690640398043629 14562641650383990149266361)
    ·
      refine ⟨10921981237787992611949771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14562641650383990149266361 10921981237787992611949771)
      ·
        refine ⟨16382971856681988917924657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10921981237787992611949771 16382971856681988917924657)
        ·
          refine ⟨12287228892511491688443493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16382971856681988917924657 12287228892511491688443493)
          ·
            refine ⟨2303855417345904691583155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12287228892511491688443493 2303855417345904691583155)
            ·
              refine ⟨3455783126018857037374733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303855417345904691583155 3455783126018857037374733)
              ·
                refine ⟨1295918672257071389015525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3455783126018857037374733 1295918672257071389015525)
                ·
                  refine ⟨242984751048200885440411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1295918672257071389015525 242984751048200885440411)
                  ·
                    rfl

theorem cell21_1064725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_1064725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064725 prefixEnd_1064725 := by exact prefixLift 1064725
  have htrace : WordTrace (prefixWord ++ tailWord_1064725) baseStart_1064725 baseEnd_1064725 := by
    simpa [prefixWord, tailWord_1064725, baseEnd_1064725] using wordTrace_append hprefix tailTrace_1064725
  have hstable : (prefixWord ++ tailWord_1064725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064725).length < 2 ^ (prefixWord ++ tailWord_1064725).sum := by decide
  have hdescent : baseEnd_1064725 < baseStart_1064725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064804 : List Nat := [2, 3, 1, 1, 5, 1, 2, 3, 3]
def baseStart_1064804 : Nat := 118140960795 + 1064804 * 2 ^ 59
def prefixEnd_1064804 : Nat := 4983230072969 + 3 ^ 40 * 1064804 * 2
def baseEnd_1064804 : Nat := 243002779924514303623583

theorem tailTrace_1064804 : CollatzResearch.WordTrace tailWord_1064804 prefixEnd_1064804 243002779924514303623583 := by
  unfold tailWord_1064804
  simp only [CollatzResearch.WordTrace]
  refine ⟨19418296217202218445084733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25891061622936291260112977 19418296217202218445084733)
  ·
    refine ⟨7281861081450831916906775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19418296217202218445084733 7281861081450831916906775)
    ·
      refine ⟨10922791622176247875360163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7281861081450831916906775 10922791622176247875360163)
      ·
        refine ⟨16384187433264371813040245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10922791622176247875360163 16384187433264371813040245)
        ·
          refine ⟨1536017571868534857472523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16384187433264371813040245 1536017571868534857472523)
          ·
            refine ⟨2304026357802802286208785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1536017571868534857472523 2304026357802802286208785)
            ·
              refine ⟨1728019768352101714656589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2304026357802802286208785 1728019768352101714656589)
              ·
                refine ⟨648007413132038142996221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1728019768352101714656589 648007413132038142996221)
                ·
                  refine ⟨243002779924514303623583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 648007413132038142996221 243002779924514303623583)
                  ·
                    rfl

theorem cell21_1064804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_1064804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064804 prefixEnd_1064804 := by exact prefixLift 1064804
  have htrace : WordTrace (prefixWord ++ tailWord_1064804) baseStart_1064804 baseEnd_1064804 := by
    simpa [prefixWord, tailWord_1064804, baseEnd_1064804] using wordTrace_append hprefix tailTrace_1064804
  have hstable : (prefixWord ++ tailWord_1064804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064804).length < 2 ^ (prefixWord ++ tailWord_1064804).sum := by decide
  have hdescent : baseEnd_1064804 < baseStart_1064804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064894 : List Nat := [4, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_1064894 : Nat := 118140960795 + 1064894 * 2 ^ 59
def prefixEnd_1064894 : Nat := 4983230072969 + 3 ^ 40 * 1064894 * 2
def baseEnd_1064894 : Nat := 243023319150694147123399

theorem tailTrace_1064894 : CollatzResearch.WordTrace tailWord_1064894 prefixEnd_1064894 243023319150694147123399 := by
  unfold tailWord_1064894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4854984375509797782618217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25893250002718921507297157 4854984375509797782618217)
  ·
    refine ⟨3641238281632348336963663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4854984375509797782618217 3641238281632348336963663)
    ·
      refine ⟨5461857422448522505445495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3641238281632348336963663 5461857422448522505445495)
      ·
        refine ⟨8192786133672783758168243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5461857422448522505445495 8192786133672783758168243)
        ·
          refine ⟨12289179200509175637252365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8192786133672783758168243 12289179200509175637252365)
          ·
            refine ⟨4608442200190940863969637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12289179200509175637252365 4608442200190940863969637)
            ·
              refine ⟨864082912535801411994307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4608442200190940863969637 864082912535801411994307)
              ·
                refine ⟨1296124368803702117991461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864082912535801411994307 1296124368803702117991461)
                ·
                  refine ⟨243023319150694147123399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1296124368803702117991461 243023319150694147123399)
                  ·
                    rfl

theorem cell21_1064894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_1064894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1064894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1064894 prefixEnd_1064894 := by exact prefixLift 1064894
  have htrace : WordTrace (prefixWord ++ tailWord_1064894) baseStart_1064894 baseEnd_1064894 := by
    simpa [prefixWord, tailWord_1064894, baseEnd_1064894] using wordTrace_append hprefix tailTrace_1064894
  have hstable : (prefixWord ++ tailWord_1064894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064894).length < 2 ^ (prefixWord ++ tailWord_1064894).sum := by decide
  have hdescent : baseEnd_1064894 < baseStart_1064894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065046 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1065046 : Nat := 118140960795 + 1065046 * 2 ^ 59
def prefixEnd_1065046 : Nat := 4983230072969 + 3 ^ 40 * 1065046 * 2
def baseEnd_1065046 : Nat := 243058007621575660589755

theorem tailTrace_1065046 : CollatzResearch.WordTrace tailWord_1065046 prefixEnd_1065046 243058007621575660589755 := by
  unfold tailWord_1065046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2427838681220482013779937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25896945933018474813652661 2427838681220482013779937)
  ·
    refine ⟨1820879010915361510334953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2427838681220482013779937 1820879010915361510334953)
    ·
      refine ⟨1365659258186521132751215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1820879010915361510334953 1365659258186521132751215)
      ·
        refine ⟨2048488887279781699126823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1365659258186521132751215 2048488887279781699126823)
        ·
          refine ⟨3072733330919672548690235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2048488887279781699126823 3072733330919672548690235)
          ·
            refine ⟨4609099996379508823035353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072733330919672548690235 4609099996379508823035353)
            ·
              refine ⟨3456824997284631617276515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4609099996379508823035353 3456824997284631617276515)
              ·
                refine ⟨5185237495926947425914773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3456824997284631617276515 5185237495926947425914773)
                ·
                  refine ⟨243058007621575660589755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5185237495926947425914773 243058007621575660589755)
                  ·
                    rfl

theorem cell21_1065046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1065046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065046 prefixEnd_1065046 := by exact prefixLift 1065046
  have htrace : WordTrace (prefixWord ++ tailWord_1065046) baseStart_1065046 baseEnd_1065046 := by
    simpa [prefixWord, tailWord_1065046, baseEnd_1065046] using wordTrace_append hprefix tailTrace_1065046
  have hstable : (prefixWord ++ tailWord_1065046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065046).length < 2 ^ (prefixWord ++ tailWord_1065046).sum := by decide
  have hdescent : baseEnd_1065046 < baseStart_1065046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065102 : List Nat := [4, 1, 1, 3, 12]
def baseStart_1065102 : Nat := 118140960795 + 1065102 * 2 ^ 59
def prefixEnd_1065102 : Nat := 4983230072969 + 3 ^ 40 * 1065102 * 2
def baseEnd_1065102 : Nat := 3000873920796691452547

theorem tailTrace_1065102 : CollatzResearch.WordTrace tailWord_1065102 prefixEnd_1065102 3000873920796691452547 := by
  unfold tailWord_1065102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4855932673415604223064695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25898307591549889189678373 4855932673415604223064695)
  ·
    refine ⟨7283899010123406334597043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4855932673415604223064695 7283899010123406334597043)
    ·
      refine ⟨10925848515185109501895565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7283899010123406334597043 10925848515185109501895565)
      ·
        refine ⟨4097193193194416063210837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10925848515185109501895565 4097193193194416063210837)
        ·
          refine ⟨3000873920796691452547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4097193193194416063210837 3000873920796691452547)
          ·
            rfl

theorem cell21_1065102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 12].length) (baseStart_1065102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065102 prefixEnd_1065102 := by exact prefixLift 1065102
  have htrace : WordTrace (prefixWord ++ tailWord_1065102) baseStart_1065102 baseEnd_1065102 := by
    simpa [prefixWord, tailWord_1065102, baseEnd_1065102] using wordTrace_append hprefix tailTrace_1065102
  have hstable : (prefixWord ++ tailWord_1065102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065102).length < 2 ^ (prefixWord ++ tailWord_1065102).sum := by decide
  have hdescent : baseEnd_1065102 < baseStart_1065102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065119 : List Nat := [1, 1, 2, 6, 1, 1, 3, 6]
def baseStart_1065119 : Nat := 118140960795 + 1065119 * 2 ^ 59
def prefixEnd_1065119 : Nat := 4983230072969 + 3 ^ 40 * 1065119 * 2
def baseEnd_1065119 : Nat := 81024889072047918624313

theorem tailTrace_1065119 : CollatzResearch.WordTrace tailWord_1065119 prefixEnd_1065119 81024889072047918624313 := by
  unfold tailWord_1065119
  simp only [CollatzResearch.WordTrace]
  refine ⟨38848081428263245687886411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25898720952175497125257607 38848081428263245687886411)
  ·
    refine ⟨58272122142394868531829617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38848081428263245687886411 58272122142394868531829617)
    ·
      refine ⟨43704091606796151398872213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58272122142394868531829617 43704091606796151398872213)
      ·
        refine ⟨2048629294068569596822135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43704091606796151398872213 2048629294068569596822135)
        ·
          refine ⟨3072943941102854395233203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2048629294068569596822135 3072943941102854395233203)
          ·
            refine ⟨4609415911654281592849805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072943941102854395233203 4609415911654281592849805)
            ·
              refine ⟨1728530966870355597318677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4609415911654281592849805 1728530966870355597318677)
              ·
                refine ⟨81024889072047918624313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1728530966870355597318677 81024889072047918624313)
                ·
                  rfl

theorem cell21_1065119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 6].length) (baseStart_1065119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065119 prefixEnd_1065119 := by exact prefixLift 1065119
  have htrace : WordTrace (prefixWord ++ tailWord_1065119) baseStart_1065119 baseEnd_1065119 := by
    simpa [prefixWord, tailWord_1065119, baseEnd_1065119] using wordTrace_append hprefix tailTrace_1065119
  have hstable : (prefixWord ++ tailWord_1065119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065119).length < 2 ^ (prefixWord ++ tailWord_1065119).sum := by decide
  have hdescent : baseEnd_1065119 < baseStart_1065119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065147 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 6]
def baseStart_1065147 : Nat := 118140960795 + 1065147 * 2 ^ 59
def prefixEnd_1065147 : Nat := 4983230072969 + 3 ^ 40 * 1065147 * 2
def baseEnd_1065147 : Nat := 243081057197621929406215

theorem tailTrace_1065147 : CollatzResearch.WordTrace tailWord_1065147 prefixEnd_1065147 243081057197621929406215 := by
  unfold tailWord_1065147
  simp only [CollatzResearch.WordTrace]
  refine ⟨38849102672161806469905695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25899401781441204313270463 38849102672161806469905695)
  ·
    refine ⟨58273654008242709704858543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38849102672161806469905695 58273654008242709704858543)
    ·
      refine ⟨87410481012364064557287815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58273654008242709704858543 87410481012364064557287815)
      ·
        refine ⟨131115721518546096835931723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87410481012364064557287815 131115721518546096835931723)
        ·
          refine ⟨196673582277819145253897585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131115721518546096835931723 196673582277819145253897585)
          ·
            refine ⟨147505186708364358940423189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196673582277819145253897585 147505186708364358940423189)
            ·
              refine ⟨6914305626954579325332337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 147505186708364358940423189 6914305626954579325332337)
              ·
                refine ⟨5185729220215934493999253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6914305626954579325332337 5185729220215934493999253)
                ·
                  refine ⟨243081057197621929406215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5185729220215934493999253 243081057197621929406215)
                  ·
                    rfl

theorem cell21_1065147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_1065147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065147 prefixEnd_1065147 := by exact prefixLift 1065147
  have htrace : WordTrace (prefixWord ++ tailWord_1065147) baseStart_1065147 baseEnd_1065147 := by
    simpa [prefixWord, tailWord_1065147, baseEnd_1065147] using wordTrace_append hprefix tailTrace_1065147
  have hstable : (prefixWord ++ tailWord_1065147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065147).length < 2 ^ (prefixWord ++ tailWord_1065147).sum := by decide
  have hdescent : baseEnd_1065147 < baseStart_1065147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065226 : List Nat := [3, 1, 2, 2, 1, 1, 2, 6, 3]
def baseStart_1065226 : Nat := 118140960795 + 1065226 * 2 ^ 59
def prefixEnd_1065226 : Nat := 4983230072969 + 3 ^ 40 * 1065226 * 2
def baseEnd_1065226 : Nat := 243099086073935347589387

theorem tailTrace_1065226 : CollatzResearch.WordTrace tailWord_1065226 prefixEnd_1065226 243099086073935347589387 := by
  unfold tailWord_1065226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9712996009718900740507883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25901322692583735308021021 9712996009718900740507883)
  ·
    refine ⟨14569494014578351110761825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9712996009718900740507883 14569494014578351110761825)
    ·
      refine ⟨10927120510933763333071369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14569494014578351110761825 10927120510933763333071369)
      ·
        refine ⟨8195340383200322499803527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10927120510933763333071369 8195340383200322499803527)
        ·
          refine ⟨12293010574800483749705291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8195340383200322499803527 12293010574800483749705291)
          ·
            refine ⟨18439515862200725624557937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12293010574800483749705291 18439515862200725624557937)
            ·
              refine ⟨13829636896650544218418453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18439515862200725624557937 13829636896650544218418453)
              ·
                refine ⟨648264229530494260238365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13829636896650544218418453 648264229530494260238365)
                ·
                  refine ⟨243099086073935347589387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 648264229530494260238365 243099086073935347589387)
                  ·
                    rfl

theorem cell21_1065226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_1065226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065226 prefixEnd_1065226 := by exact prefixLift 1065226
  have htrace : WordTrace (prefixWord ++ tailWord_1065226) baseStart_1065226 baseEnd_1065226 := by
    simpa [prefixWord, tailWord_1065226, baseEnd_1065226] using wordTrace_append hprefix tailTrace_1065226
  have hstable : (prefixWord ++ tailWord_1065226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065226).length < 2 ^ (prefixWord ++ tailWord_1065226).sum := by decide
  have hdescent : baseEnd_1065226 < baseStart_1065226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065240 : List Nat := [2, 1, 2, 3, 1, 2, 3, 3, 4]
def baseStart_1065240 : Nat := 118140960795 + 1065240 * 2 ^ 59
def prefixEnd_1065240 : Nat := 4983230072969 + 3 ^ 40 * 1065240 * 2
def baseEnd_1065240 : Nat := 243102281064674434356025

theorem tailTrace_1065240 : CollatzResearch.WordTrace tailWord_1065240 prefixEnd_1065240 243102281064674434356025 := by
  unfold tailWord_1065240
  simp only [CollatzResearch.WordTrace]
  refine ⟨19426247330412441676520587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25901663107216588902027449 19426247330412441676520587)
  ·
    refine ⟨29139370995618662514780881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19426247330412441676520587 29139370995618662514780881)
    ·
      refine ⟨21854528246713996886085661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29139370995618662514780881 21854528246713996886085661)
      ·
        refine ⟨8195448092517748832282123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21854528246713996886085661 8195448092517748832282123)
        ·
          refine ⟨12293172138776623248423185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8195448092517748832282123 12293172138776623248423185)
          ·
            refine ⟨9219879104082467436317389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12293172138776623248423185 9219879104082467436317389)
            ·
              refine ⟨3457454664030925288619021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9219879104082467436317389 3457454664030925288619021)
              ·
                refine ⟨1296545499011596983232133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3457454664030925288619021 1296545499011596983232133)
                ·
                  refine ⟨243102281064674434356025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1296545499011596983232133 243102281064674434356025)
                  ·
                    rfl

theorem cell21_1065240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_1065240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065240 prefixEnd_1065240 := by exact prefixLift 1065240
  have htrace : WordTrace (prefixWord ++ tailWord_1065240) baseStart_1065240 baseEnd_1065240 := by
    simpa [prefixWord, tailWord_1065240, baseEnd_1065240] using wordTrace_append hprefix tailTrace_1065240
  have hstable : (prefixWord ++ tailWord_1065240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065240).length < 2 ^ (prefixWord ++ tailWord_1065240).sum := by decide
  have hdescent : baseEnd_1065240 < baseStart_1065240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065319 : List Nat := [1, 1, 5, 1, 3, 2, 2, 3, 3]
def baseStart_1065319 : Nat := 118140960795 + 1065319 * 2 ^ 59
def prefixEnd_1065319 : Nat := 4983230072969 + 3 ^ 40 * 1065319 * 2
def baseEnd_1065319 : Nat := 243120309940987852539197

theorem tailTrace_1065319 : CollatzResearch.WordTrace tailWord_1065319 prefixEnd_1065319 243120309940987852539197 := by
  unfold tailWord_1065319
  simp only [CollatzResearch.WordTrace]
  refine ⟨38855376027538679845167011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25903584018359119896778007 38855376027538679845167011)
  ·
    refine ⟨58283064041308019767750517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38855376027538679845167011 58283064041308019767750517)
    ·
      refine ⟨5464037253872626853226611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58283064041308019767750517 5464037253872626853226611)
      ·
        refine ⟨8196055880808940279839917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5464037253872626853226611 8196055880808940279839917)
        ·
          refine ⟨3073520955303352604939969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8196055880808940279839917 3073520955303352604939969)
          ·
            refine ⟨2305140716477514453704977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3073520955303352604939969 2305140716477514453704977)
            ·
              refine ⟨1728855537358135840278733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2305140716477514453704977 1728855537358135840278733)
              ·
                refine ⟨648320826509300940104525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1728855537358135840278733 648320826509300940104525)
                ·
                  refine ⟨243120309940987852539197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 648320826509300940104525 243120309940987852539197)
                  ·
                    rfl

theorem cell21_1065319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 3].length) (baseStart_1065319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065319 prefixEnd_1065319 := by exact prefixLift 1065319
  have htrace : WordTrace (prefixWord ++ tailWord_1065319) baseStart_1065319 baseEnd_1065319 := by
    simpa [prefixWord, tailWord_1065319, baseEnd_1065319] using wordTrace_append hprefix tailTrace_1065319
  have hstable : (prefixWord ++ tailWord_1065319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065319).length < 2 ^ (prefixWord ++ tailWord_1065319).sum := by decide
  have hdescent : baseEnd_1065319 < baseStart_1065319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065330 : List Nat := [3, 2, 1, 2, 1, 4, 8]
def baseStart_1065330 : Nat := 118140960795 + 1065330 * 2 ^ 59
def prefixEnd_1065330 : Nat := 4983230072969 + 3 ^ 40 * 1065330 * 2
def baseEnd_1065330 : Nat := 27013646698983808650649

theorem tailTrace_1065330 : CollatzResearch.WordTrace tailWord_1065330 prefixEnd_1065330 27013646698983808650649 := by
  unfold tailWord_1065330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9713944307624707180954361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25903851486999219149211629 9713944307624707180954361)
  ·
    refine ⟨7285458230718530385715771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9713944307624707180954361 7285458230718530385715771)
    ·
      refine ⟨10928187346077795578573657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7285458230718530385715771 10928187346077795578573657)
      ·
        refine ⟨8196140509558346683930243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10928187346077795578573657 8196140509558346683930243)
        ·
          refine ⟨12294210764337520025895365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8196140509558346683930243 12294210764337520025895365)
          ·
            refine ⟨2305164518313285004855381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12294210764337520025895365 2305164518313285004855381)
            ·
              refine ⟨27013646698983808650649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2305164518313285004855381 27013646698983808650649)
              ·
                rfl

theorem cell21_1065330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 8].length) (baseStart_1065330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065330 prefixEnd_1065330 := by exact prefixLift 1065330
  have htrace : WordTrace (prefixWord ++ tailWord_1065330) baseStart_1065330 baseEnd_1065330 := by
    simpa [prefixWord, tailWord_1065330, baseEnd_1065330] using wordTrace_append hprefix tailTrace_1065330
  have hstable : (prefixWord ++ tailWord_1065330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065330).length < 2 ^ (prefixWord ++ tailWord_1065330).sum := by decide
  have hdescent : baseEnd_1065330 < baseStart_1065330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065333 : List Nat := [1, 3, 4, 1, 2, 1, 3, 2, 4]
def baseStart_1065333 : Nat := 118140960795 + 1065333 * 2 ^ 59
def prefixEnd_1065333 : Nat := 4983230072969 + 3 ^ 40 * 1065333 * 2
def baseEnd_1065333 : Nat := 243123504931726939305835

theorem tailTrace_1065333 : CollatzResearch.WordTrace tailWord_1065333 prefixEnd_1065333 243123504931726939305835 := by
  unfold tailWord_1065333
  simp only [CollatzResearch.WordTrace]
  refine ⟨38855886649487960236176653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25903924432991973490784435 38855886649487960236176653)
  ·
    refine ⟨14570957493557985088566245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38855886649487960236176653 14570957493557985088566245)
    ·
      refine ⟨2732054530042122204106171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14570957493557985088566245 2732054530042122204106171)
      ·
        refine ⟨4098081795063183306159257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2732054530042122204106171 4098081795063183306159257)
        ·
          refine ⟨3073561346297387479619443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4098081795063183306159257 3073561346297387479619443)
          ·
            refine ⟨4610342019446081219429165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3073561346297387479619443 4610342019446081219429165)
            ·
              refine ⟨1728878257292280457285937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4610342019446081219429165 1728878257292280457285937)
              ·
                refine ⟨1296658692969210342964453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1728878257292280457285937 1296658692969210342964453)
                ·
                  refine ⟨243123504931726939305835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1296658692969210342964453 243123504931726939305835)
                  ·
                    rfl

theorem cell21_1065333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_1065333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065333 prefixEnd_1065333 := by exact prefixLift 1065333
  have htrace : WordTrace (prefixWord ++ tailWord_1065333) baseStart_1065333 baseEnd_1065333 := by
    simpa [prefixWord, tailWord_1065333, baseEnd_1065333] using wordTrace_append hprefix tailTrace_1065333
  have hstable : (prefixWord ++ tailWord_1065333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065333).length < 2 ^ (prefixWord ++ tailWord_1065333).sum := by decide
  have hdescent : baseEnd_1065333 < baseStart_1065333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065375 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 8]
def baseStart_1065375 : Nat := 118140960795 + 1065375 * 2 ^ 59
def prefixEnd_1065375 : Nat := 4983230072969 + 3 ^ 40 * 1065375 * 2
def baseEnd_1065375 : Nat := 243133089903944199605749

theorem tailTrace_1065375 : CollatzResearch.WordTrace tailWord_1065375 prefixEnd_1065375 243133089903944199605749 := by
  unfold tailWord_1065375
  simp only [CollatzResearch.WordTrace]
  refine ⟨38857418515335801409205579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25904945676890534272803719 38857418515335801409205579)
  ·
    refine ⟨58286127773003702113808369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38857418515335801409205579 58286127773003702113808369)
    ·
      refine ⟨43714595829752776585356277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58286127773003702113808369 43714595829752776585356277)
      ·
        refine ⟨4098243359039322804877151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43714595829752776585356277 4098243359039322804877151)
        ·
          refine ⟨6147365038558984207315727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4098243359039322804877151 6147365038558984207315727)
          ·
            refine ⟨9221047557838476310973591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6147365038558984207315727 9221047557838476310973591)
            ·
              refine ⟨13831571336757714466460387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9221047557838476310973591 13831571336757714466460387)
              ·
                refine ⟨20747357005136571699690581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13831571336757714466460387 20747357005136571699690581)
                ·
                  refine ⟨243133089903944199605749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20747357005136571699690581 243133089903944199605749)
                  ·
                    rfl

theorem cell21_1065375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_1065375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065375 prefixEnd_1065375 := by exact prefixLift 1065375
  have htrace : WordTrace (prefixWord ++ tailWord_1065375) baseStart_1065375 baseEnd_1065375 := by
    simpa [prefixWord, tailWord_1065375, baseEnd_1065375] using wordTrace_append hprefix tailTrace_1065375
  have hstable : (prefixWord ++ tailWord_1065375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065375).length < 2 ^ (prefixWord ++ tailWord_1065375).sum := by decide
  have hdescent : baseEnd_1065375 < baseStart_1065375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065406 : List Nat := [4, 2, 1, 1, 1, 1, 3, 8]
def baseStart_1065406 : Nat := 118140960795 + 1065406 * 2 ^ 59
def prefixEnd_1065406 : Nat := 4983230072969 + 3 ^ 40 * 1065406 * 2
def baseEnd_1065406 : Nat := 81046721508765011529673

theorem tailTrace_1065406 : CollatzResearch.WordTrace tailWord_1065406 prefixEnd_1065406 81046721508765011529673 := by
  unfold tailWord_1065406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4857318647277936712948009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25905699452148995802389381 4857318647277936712948009)
  ·
    refine ⟨3642988985458452534711007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4857318647277936712948009 3642988985458452534711007)
    ·
      refine ⟨5464483478187678802066511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3642988985458452534711007 5464483478187678802066511)
      ·
        refine ⟨8196725217281518203099767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5464483478187678802066511 8196725217281518203099767)
        ·
          refine ⟨12295087825922277304649651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8196725217281518203099767 12295087825922277304649651)
          ·
            refine ⟨18442631738883415956974477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12295087825922277304649651 18442631738883415956974477)
            ·
              refine ⟨6915986902081280983865429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18442631738883415956974477 6915986902081280983865429)
              ·
                refine ⟨81046721508765011529673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6915986902081280983865429 81046721508765011529673)
                ·
                  rfl

theorem cell21_1065406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_1065406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065406 prefixEnd_1065406 := by exact prefixLift 1065406
  have htrace : WordTrace (prefixWord ++ tailWord_1065406) baseStart_1065406 baseEnd_1065406 := by
    simpa [prefixWord, tailWord_1065406, baseEnd_1065406] using wordTrace_append hprefix tailTrace_1065406
  have hstable : (prefixWord ++ tailWord_1065406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065406).length < 2 ^ (prefixWord ++ tailWord_1065406).sum := by decide
  have hdescent : baseEnd_1065406 < baseStart_1065406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065564 : List Nat := [2, 2, 4, 1, 3, 1, 3, 2, 3]
def baseStart_1065564 : Nat := 118140960795 + 1065564 * 2 ^ 59
def prefixEnd_1065564 : Nat := 4983230072969 + 3 ^ 40 * 1065564 * 2
def baseEnd_1065564 : Nat := 243176222278921870955363

theorem tailTrace_1065564 : CollatzResearch.WordTrace tailWord_1065564 prefixEnd_1065564 243176222278921870955363 := by
  unfold tailWord_1065564
  simp only [CollatzResearch.WordTrace]
  refine ⟨19432155955825543343917873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25909541274434057791890497 19432155955825543343917873)
  ·
    refine ⟨14574116966869157507938405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19432155955825543343917873 14574116966869157507938405)
    ·
      refine ⟨2732646931287967032738451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14574116966869157507938405 2732646931287967032738451)
      ·
        refine ⟨4098970396931950549107677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2732646931287967032738451 4098970396931950549107677)
        ·
          refine ⟨1537113898849481455915379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4098970396931950549107677 1537113898849481455915379)
          ·
            refine ⟨2305670848274222183873069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537113898849481455915379 2305670848274222183873069)
            ·
              refine ⟨864626568102833318952401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2305670848274222183873069 864626568102833318952401)
              ·
                refine ⟨648469926077124989214301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864626568102833318952401 648469926077124989214301)
                ·
                  refine ⟨243176222278921870955363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 648469926077124989214301 243176222278921870955363)
                  ·
                    rfl

theorem cell21_1065564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_1065564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065564 prefixEnd_1065564 := by exact prefixLift 1065564
  have htrace : WordTrace (prefixWord ++ tailWord_1065564) baseStart_1065564 baseEnd_1065564 := by
    simpa [prefixWord, tailWord_1065564, baseEnd_1065564] using wordTrace_append hprefix tailTrace_1065564
  have hstable : (prefixWord ++ tailWord_1065564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065564).length < 2 ^ (prefixWord ++ tailWord_1065564).sum := by decide
  have hdescent : baseEnd_1065564 < baseStart_1065564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065682 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_1065682 : Nat := 118140960795 + 1065682 * 2 ^ 59
def prefixEnd_1065682 : Nat := 4983230072969 + 3 ^ 40 * 1065682 * 2
def baseEnd_1065682 : Nat := 243203151486579887988455

theorem tailTrace_1065682 : CollatzResearch.WordTrace tailWord_1065682 prefixEnd_1065682 243203151486579887988455 := by
  unfold tailWord_1065682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9717153931305898210157825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25912410483482395227087533 9717153931305898210157825)
  ·
    refine ⟨7287865448479423657618369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9717153931305898210157825 7287865448479423657618369)
    ·
      refine ⟨5465899086359567743213777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7287865448479423657618369 5465899086359567743213777)
      ·
        refine ⟨4099424314769675807410333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5465899086359567743213777 4099424314769675807410333)
        ·
          refine ⟨1537284118038628427778875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4099424314769675807410333 1537284118038628427778875)
          ·
            refine ⟨2305926177057942641668313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537284118038628427778875 2305926177057942641668313)
            ·
              refine ⟨1729444632793456981251235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2305926177057942641668313 1729444632793456981251235)
              ·
                refine ⟨2594166949190185471876853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1729444632793456981251235 2594166949190185471876853)
                ·
                  refine ⟨243203151486579887988455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2594166949190185471876853 243203151486579887988455)
                  ·
                    rfl

theorem cell21_1065682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_1065682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065682 prefixEnd_1065682 := by exact prefixLift 1065682
  have htrace : WordTrace (prefixWord ++ tailWord_1065682) baseStart_1065682 baseEnd_1065682 := by
    simpa [prefixWord, tailWord_1065682, baseEnd_1065682] using wordTrace_append hprefix tailTrace_1065682
  have hstable : (prefixWord ++ tailWord_1065682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065682).length < 2 ^ (prefixWord ++ tailWord_1065682).sum := by decide
  have hdescent : baseEnd_1065682 < baseStart_1065682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065710 : List Nat := [4, 1, 2, 1, 1, 4, 1, 7]
def baseStart_1065710 : Nat := 118140960795 + 1065710 * 2 ^ 59
def prefixEnd_1065710 : Nat := 4983230072969 + 3 ^ 40 * 1065710 * 2
def baseEnd_1065710 : Nat := 81069847156019353840577

theorem tailTrace_1065710 : CollatzResearch.WordTrace tailWord_1065710 prefixEnd_1065710 81069847156019353840577 := by
  unfold tailWord_1065710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4858704621140269202831323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25913091312748102415100389 4858704621140269202831323)
  ·
    refine ⟨7288056931710403804246985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4858704621140269202831323 7288056931710403804246985)
    ·
      refine ⟨5466042698782802853185239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7288056931710403804246985 5466042698782802853185239)
      ·
        refine ⟨8199064048174204279777859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5466042698782802853185239 8199064048174204279777859)
        ·
          refine ⟨12298596072261306419666789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8199064048174204279777859 12298596072261306419666789)
          ·
            refine ⟨2305986763548994953687523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12298596072261306419666789 2305986763548994953687523)
            ·
              refine ⟨3458980145323492430531285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305986763548994953687523 3458980145323492430531285)
              ·
                refine ⟨81069847156019353840577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3458980145323492430531285 81069847156019353840577)
                ·
                  rfl

theorem cell21_1065710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_1065710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065710 prefixEnd_1065710 := by exact prefixLift 1065710
  have htrace : WordTrace (prefixWord ++ tailWord_1065710) baseStart_1065710 baseEnd_1065710 := by
    simpa [prefixWord, tailWord_1065710, baseEnd_1065710] using wordTrace_append hprefix tailTrace_1065710
  have hstable : (prefixWord ++ tailWord_1065710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065710).length < 2 ^ (prefixWord ++ tailWord_1065710).sum := by decide
  have hdescent : baseEnd_1065710 < baseStart_1065710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065786 : List Nat := [3, 1, 1, 1, 7, 8]
def baseStart_1065786 : Nat := 118140960795 + 1065786 * 2 ^ 59
def prefixEnd_1065786 : Nat := 4983230072969 + 3 ^ 40 * 1065786 * 2
def baseEnd_1065786 : Nat := 9008403174203659935367

theorem tailTrace_1065786 : CollatzResearch.WordTrace tailWord_1065786 prefixEnd_1065786 9008403174203659935367 := by
  unfold tailWord_1065786
  simp only [CollatzResearch.WordTrace]
  refine ⟨9718102229211704650604303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25914939277897879068278141 9718102229211704650604303)
  ·
    refine ⟨14577153343817556975906455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9718102229211704650604303 14577153343817556975906455)
    ·
      refine ⟨21865730015726335463859683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14577153343817556975906455 21865730015726335463859683)
      ·
        refine ⟨32798595023589503195789525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21865730015726335463859683 32798595023589503195789525)
        ·
          refine ⟨768717070865378981151317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32798595023589503195789525 768717070865378981151317)
          ·
            refine ⟨9008403174203659935367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 768717070865378981151317 9008403174203659935367)
            ·
              rfl

theorem cell21_1065786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 8].length) (baseStart_1065786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065786 prefixEnd_1065786 := by exact prefixLift 1065786
  have htrace : WordTrace (prefixWord ++ tailWord_1065786) baseStart_1065786 baseEnd_1065786 := by
    simpa [prefixWord, tailWord_1065786, baseEnd_1065786] using wordTrace_append hprefix tailTrace_1065786
  have hstable : (prefixWord ++ tailWord_1065786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065786).length < 2 ^ (prefixWord ++ tailWord_1065786).sum := by decide
  have hdescent : baseEnd_1065786 < baseStart_1065786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065789 : List Nat := [1, 4, 1, 4, 2, 1, 2, 2, 4]
def baseStart_1065789 : Nat := 118140960795 + 1065789 * 2 ^ 59
def prefixEnd_1065789 : Nat := 4983230072969 + 3 ^ 40 * 1065789 * 2
def baseEnd_1065789 : Nat := 243227570344371479704903

theorem tailTrace_1065789 : CollatzResearch.WordTrace tailWord_1065789 prefixEnd_1065789 243227570344371479704903 := by
  unfold tailWord_1065789
  simp only [CollatzResearch.WordTrace]
  refine ⟨38872518335835950114776421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25915012223890633409850947 38872518335835950114776421)
  ·
    refine ⟨7288597187969240646520579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38872518335835950114776421 7288597187969240646520579)
    ·
      refine ⟨10932895781953860969780869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7288597187969240646520579 10932895781953860969780869)
      ·
        refine ⟨2049917959116348931833913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10932895781953860969780869 2049917959116348931833913)
        ·
          refine ⟨1537438469337261698875435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2049917959116348931833913 1537438469337261698875435)
          ·
            refine ⟨2306157704005892548313153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537438469337261698875435 2306157704005892548313153)
            ·
              refine ⟨1729618278004419411234865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2306157704005892548313153 1729618278004419411234865)
              ·
                refine ⟨1297213708503314558426149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729618278004419411234865 1297213708503314558426149)
                ·
                  refine ⟨243227570344371479704903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1297213708503314558426149 243227570344371479704903)
                  ·
                    rfl

theorem cell21_1065789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_1065789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065789 prefixEnd_1065789 := by exact prefixLift 1065789
  have htrace : WordTrace (prefixWord ++ tailWord_1065789) baseStart_1065789 baseEnd_1065789 := by
    simpa [prefixWord, tailWord_1065789, baseEnd_1065789] using wordTrace_append hprefix tailTrace_1065789
  have hstable : (prefixWord ++ tailWord_1065789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065789).length < 2 ^ (prefixWord ++ tailWord_1065789).sum := by decide
  have hdescent : baseEnd_1065789 < baseStart_1065789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065800 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 5]
def baseStart_1065800 : Nat := 118140960795 + 1065800 * 2 ^ 59
def prefixEnd_1065800 : Nat := 4983230072969 + 3 ^ 40 * 1065800 * 2
def baseEnd_1065800 : Nat := 243230080694237905021547

theorem tailTrace_1065800 : CollatzResearch.WordTrace tailWord_1065800 prefixEnd_1065800 243230080694237905021547 := by
  unfold tailWord_1065800
  simp only [CollatzResearch.WordTrace]
  refine ⟨19436459769398049496713427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25915279692530732662284569 19436459769398049496713427)
  ·
    refine ⟨29154689654097074245070141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19436459769398049496713427 29154689654097074245070141)
    ·
      refine ⟨10933008620286402841901303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29154689654097074245070141 10933008620286402841901303)
      ·
        refine ⟨16399512930429604262851955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10933008620286402841901303 16399512930429604262851955)
        ·
          refine ⟨24599269395644406394277933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16399512930429604262851955 24599269395644406394277933)
          ·
            refine ⟨9224726023366652397854225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24599269395644406394277933 9224726023366652397854225)
            ·
              refine ⟨6918544517524989298390669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9224726023366652397854225 6918544517524989298390669)
              ·
                refine ⟨2594454194071870986896501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6918544517524989298390669 2594454194071870986896501)
                ·
                  refine ⟨243230080694237905021547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2594454194071870986896501 243230080694237905021547)
                  ·
                    rfl

theorem cell21_1065800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_1065800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065800 prefixEnd_1065800 := by exact prefixLift 1065800
  have htrace : WordTrace (prefixWord ++ tailWord_1065800) baseStart_1065800 baseEnd_1065800 := by
    simpa [prefixWord, tailWord_1065800, baseEnd_1065800] using wordTrace_append hprefix tailTrace_1065800
  have hstable : (prefixWord ++ tailWord_1065800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065800).length < 2 ^ (prefixWord ++ tailWord_1065800).sum := by decide
  have hdescent : baseEnd_1065800 < baseStart_1065800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065938 : List Nat := [3, 2, 2, 3, 1, 1, 2, 7]
def baseStart_1065938 : Nat := 118140960795 + 1065938 * 2 ^ 59
def prefixEnd_1065938 : Nat := 4983230072969 + 3 ^ 40 * 1065938 * 2
def baseEnd_1065938 : Nat := 81087191391460110573755

theorem tailTrace_1065938 : CollatzResearch.WordTrace tailWord_1065938 prefixEnd_1065938 81087191391460110573755 := by
  unfold tailWord_1065938
  simp only [CollatzResearch.WordTrace]
  refine ⟨9719488203074037140487617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25918635208197432374633645 9719488203074037140487617)
  ·
    refine ⟨7289616152305527855365713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9719488203074037140487617 7289616152305527855365713)
    ·
      refine ⟨5467212114229145891524285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7289616152305527855365713 5467212114229145891524285)
      ·
        refine ⟨2050204542835929709321607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5467212114229145891524285 2050204542835929709321607)
        ·
          refine ⟨3075306814253894563982411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050204542835929709321607 3075306814253894563982411)
          ·
            refine ⟨4612960221380841845973617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075306814253894563982411 4612960221380841845973617)
            ·
              refine ⟨3459720166035631384480213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4612960221380841845973617 3459720166035631384480213)
              ·
                refine ⟨81087191391460110573755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3459720166035631384480213 81087191391460110573755)
                ·
                  rfl

theorem cell21_1065938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_1065938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1065938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1065938 prefixEnd_1065938 := by exact prefixLift 1065938
  have htrace : WordTrace (prefixWord ++ tailWord_1065938) baseStart_1065938 baseEnd_1065938 := by
    simpa [prefixWord, tailWord_1065938, baseEnd_1065938] using wordTrace_append hprefix tailTrace_1065938
  have hstable : (prefixWord ++ tailWord_1065938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065938).length < 2 ^ (prefixWord ++ tailWord_1065938).sum := by decide
  have hdescent : baseEnd_1065938 < baseStart_1065938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066028 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 5]
def baseStart_1066028 : Nat := 118140960795 + 1066028 * 2 ^ 59
def prefixEnd_1066028 : Nat := 4983230072969 + 3 ^ 40 * 1066028 * 2
def baseEnd_1066028 : Nat := 243282113400560175221081

theorem tailTrace_1066028 : CollatzResearch.WordTrace tailWord_1066028 prefixEnd_1066028 243282113400560175221081 := by
  unfold tailWord_1066028
  simp only [CollatzResearch.WordTrace]
  refine ⟨19440617690985046966363369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25920823587980062621817825 19440617690985046966363369)
  ·
    refine ⟨14580463268238785224772527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19440617690985046966363369 14580463268238785224772527)
    ·
      refine ⟨21870694902358177837158791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14580463268238785224772527 21870694902358177837158791)
      ·
        refine ⟨32806042353537266755738187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21870694902358177837158791 32806042353537266755738187)
        ·
          refine ⟨49209063530305900133607281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32806042353537266755738187 49209063530305900133607281)
          ·
            refine ⟨36906797647729425100205461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49209063530305900133607281 36906797647729425100205461)
            ·
              refine ⟨1730006139737316801572131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36906797647729425100205461 1730006139737316801572131)
              ·
                refine ⟨2595009209605975202358197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730006139737316801572131 2595009209605975202358197)
                ·
                  refine ⟨243282113400560175221081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2595009209605975202358197 243282113400560175221081)
                  ·
                    rfl

theorem cell21_1066028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_1066028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066028 prefixEnd_1066028 := by exact prefixLift 1066028
  have htrace : WordTrace (prefixWord ++ tailWord_1066028) baseStart_1066028 baseEnd_1066028 := by
    simpa [prefixWord, tailWord_1066028, baseEnd_1066028] using wordTrace_append hprefix tailTrace_1066028
  have hstable : (prefixWord ++ tailWord_1066028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066028).length < 2 ^ (prefixWord ++ tailWord_1066028).sum := by decide
  have hdescent : baseEnd_1066028 < baseStart_1066028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066090 : List Nat := [3, 1, 3, 2, 2, 2, 2, 6]
def baseStart_1066090 : Nat := 118140960795 + 1066090 * 2 ^ 59
def prefixEnd_1066090 : Nat := 4983230072969 + 3 ^ 40 * 1066090 * 2
def baseEnd_1066090 : Nat := 81098754215087281729207

theorem tailTrace_1066090 : CollatzResearch.WordTrace tailWord_1066090 prefixEnd_1066090 81098754215087281729207 := by
  unfold tailWord_1066090
  simp only [CollatzResearch.WordTrace]
  refine ⟨9720874176936369630370931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25922331138496985680989149 9720874176936369630370931)
  ·
    refine ⟨14581311265404554445556397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9720874176936369630370931 14581311265404554445556397)
    ·
      refine ⟨5467991724526707917083649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14581311265404554445556397 5467991724526707917083649)
      ·
        refine ⟨4100993793395030937812737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5467991724526707917083649 4100993793395030937812737)
        ·
          refine ⟨3075745345046273203359553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4100993793395030937812737 3075745345046273203359553)
          ·
            refine ⟨2306809008784704902519665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3075745345046273203359553 2306809008784704902519665)
            ·
              refine ⟨1730106756588528676889749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2306809008784704902519665 1730106756588528676889749)
              ·
                refine ⟨81098754215087281729207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1730106756588528676889749 81098754215087281729207)
                ·
                  rfl

theorem cell21_1066090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_1066090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066090 prefixEnd_1066090 := by exact prefixLift 1066090
  have htrace : WordTrace (prefixWord ++ tailWord_1066090) baseStart_1066090 baseEnd_1066090 := by
    simpa [prefixWord, tailWord_1066090, baseEnd_1066090] using wordTrace_append hprefix tailTrace_1066090
  have hstable : (prefixWord ++ tailWord_1066090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066090).length < 2 ^ (prefixWord ++ tailWord_1066090).sum := by decide
  have hdescent : baseEnd_1066090 < baseStart_1066090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066093 : List Nat := [1, 5, 1, 1, 2, 4, 2, 1, 4]
def baseStart_1066093 : Nat := 118140960795 + 1066093 * 2 ^ 59
def prefixEnd_1066093 : Nat := 4983230072969 + 3 ^ 40 * 1066093 * 2
def baseEnd_1066093 : Nat := 243296947286134506637615

theorem tailTrace_1066093 : CollatzResearch.WordTrace tailWord_1066093 prefixEnd_1066093 243296947286134506637615 := by
  unfold tailWord_1066093
  simp only [CollatzResearch.WordTrace]
  refine ⟨38883606126734610033842933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25922404084489740022561955 38883606126734610033842933)
  ·
    refine ⟨3645338074381369690672775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38883606126734610033842933 3645338074381369690672775)
    ·
      refine ⟨5468007111572054536009163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3645338074381369690672775 5468007111572054536009163)
      ·
        refine ⟨8202010667358081804013745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5468007111572054536009163 8202010667358081804013745)
        ·
          refine ⟨6151508000518561353010309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8202010667358081804013745 6151508000518561353010309)
          ·
            refine ⟨1153407750097230253689433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6151508000518561353010309 1153407750097230253689433)
            ·
              refine ⟨865055812572922690267075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1153407750097230253689433 865055812572922690267075)
              ·
                refine ⟨1297583718859384035400613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865055812572922690267075 1297583718859384035400613)
                ·
                  refine ⟨243296947286134506637615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1297583718859384035400613 243296947286134506637615)
                  ·
                    rfl

theorem cell21_1066093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_1066093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066093 prefixEnd_1066093 := by exact prefixLift 1066093
  have htrace : WordTrace (prefixWord ++ tailWord_1066093) baseStart_1066093 baseEnd_1066093 := by
    simpa [prefixWord, tailWord_1066093, baseEnd_1066093] using wordTrace_append hprefix tailTrace_1066093
  have hstable : (prefixWord ++ tailWord_1066093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066093).length < 2 ^ (prefixWord ++ tailWord_1066093).sum := by decide
  have hdescent : baseEnd_1066093 < baseStart_1066093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066135 : List Nat := [1, 1, 3, 3, 3, 1, 1, 4, 4]
def baseStart_1066135 : Nat := 118140960795 + 1066135 * 2 ^ 59
def prefixEnd_1066135 : Nat := 4983230072969 + 3 ^ 40 * 1066135 * 2
def baseEnd_1066135 : Nat := 243306532258351766937529

theorem tailTrace_1066135 : CollatzResearch.WordTrace tailWord_1066135 prefixEnd_1066135 243306532258351766937529 := by
  unfold tailWord_1066135
  simp only [CollatzResearch.WordTrace]
  refine ⟨38885137992582451206871859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25923425328388300804581239 38885137992582451206871859)
  ·
    refine ⟨58327706988873676810307789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38885137992582451206871859 58327706988873676810307789)
    ·
      refine ⟨21872890120827628803865421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58327706988873676810307789 21872890120827628803865421)
      ·
        refine ⟨8202333795310360801449533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21872890120827628803865421 8202333795310360801449533)
        ·
          refine ⟨3075875173241385300543575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8202333795310360801449533 3075875173241385300543575)
          ·
            refine ⟨4613812759862077950815363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075875173241385300543575 4613812759862077950815363)
            ·
              refine ⟨6920719139793116926223045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4613812759862077950815363 6920719139793116926223045)
              ·
                refine ⟨1297634838711209423666821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6920719139793116926223045 1297634838711209423666821)
                ·
                  refine ⟨243306532258351766937529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1297634838711209423666821 243306532258351766937529)
                  ·
                    rfl

theorem cell21_1066135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 4].length) (baseStart_1066135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066135 prefixEnd_1066135 := by exact prefixLift 1066135
  have htrace : WordTrace (prefixWord ++ tailWord_1066135) baseStart_1066135 baseEnd_1066135 := by
    simpa [prefixWord, tailWord_1066135, baseEnd_1066135] using wordTrace_append hprefix tailTrace_1066135
  have hstable : (prefixWord ++ tailWord_1066135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066135).length < 2 ^ (prefixWord ++ tailWord_1066135).sum := by decide
  have hdescent : baseEnd_1066135 < baseStart_1066135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066138 : List Nat := [3, 1, 1, 5, 1, 2, 1, 4, 3]
def baseStart_1066138 : Nat := 118140960795 + 1066138 * 2 ^ 59
def prefixEnd_1066138 : Nat := 4983230072969 + 3 ^ 40 * 1066138 * 2
def baseEnd_1066138 : Nat := 243307216899224428387523

theorem tailTrace_1066138 : CollatzResearch.WordTrace tailWord_1066138 prefixEnd_1066138 243307216899224428387523 := by
  unfold tailWord_1066138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9721311852892895679807767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25923498274381055146154045 9721311852892895679807767)
  ·
    refine ⟨14581967779339343519711651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9721311852892895679807767 14581967779339343519711651)
    ·
      refine ⟨21872951669009015279567477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14581967779339343519711651 21872951669009015279567477)
      ·
        refine ⟨2050589218969595182459451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21872951669009015279567477 2050589218969595182459451)
        ·
          refine ⟨3075883828454392773689177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050589218969595182459451 3075883828454392773689177)
          ·
            refine ⟨2306912871340794580266883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3075883828454392773689177 2306912871340794580266883)
            ·
              refine ⟨3460369307011191870400325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2306912871340794580266883 3460369307011191870400325)
              ·
                refine ⟨648819245064598475700061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3460369307011191870400325 648819245064598475700061)
                ·
                  refine ⟨243307216899224428387523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 648819245064598475700061 243307216899224428387523)
                  ·
                    rfl

theorem cell21_1066138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_1066138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066138 prefixEnd_1066138 := by exact prefixLift 1066138
  have htrace : WordTrace (prefixWord ++ tailWord_1066138) baseStart_1066138 baseEnd_1066138 := by
    simpa [prefixWord, tailWord_1066138, baseEnd_1066138] using wordTrace_append hprefix tailTrace_1066138
  have hstable : (prefixWord ++ tailWord_1066138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066138).length < 2 ^ (prefixWord ++ tailWord_1066138).sum := by decide
  have hdescent : baseEnd_1066138 < baseStart_1066138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066149 : List Nat := [1, 3, 1, 2, 1, 4, 3, 6]
def baseStart_1066149 : Nat := 118140960795 + 1066149 * 2 ^ 59
def prefixEnd_1066149 : Nat := 4983230072969 + 3 ^ 40 * 1066149 * 2
def baseEnd_1066149 : Nat := 81103242416363617901389

theorem tailTrace_1066149 : CollatzResearch.WordTrace tailWord_1066149 prefixEnd_1066149 81103242416363617901389 := by
  unfold tailWord_1066149
  simp only [CollatzResearch.WordTrace]
  refine ⟨38885648614531731597881501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25923765743021154398587667 38885648614531731597881501)
  ·
    refine ⟨14582118230449399349205563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38885648614531731597881501 14582118230449399349205563)
    ·
      refine ⟨21873177345674099023808345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14582118230449399349205563 21873177345674099023808345)
      ·
        refine ⟨16404883009255574267856259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21873177345674099023808345 16404883009255574267856259)
        ·
          refine ⟨24607324513883361401784389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16404883009255574267856259 24607324513883361401784389)
          ·
            refine ⟨4613873346353130262834573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24607324513883361401784389 4613873346353130262834573)
            ·
              refine ⟨1730202504882423848562965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4613873346353130262834573 1730202504882423848562965)
              ·
                refine ⟨81103242416363617901389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1730202504882423848562965 81103242416363617901389)
                ·
                  rfl

theorem cell21_1066149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 6].length) (baseStart_1066149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066149 prefixEnd_1066149 := by exact prefixLift 1066149
  have htrace : WordTrace (prefixWord ++ tailWord_1066149) baseStart_1066149 baseEnd_1066149 := by
    simpa [prefixWord, tailWord_1066149, baseEnd_1066149] using wordTrace_append hprefix tailTrace_1066149
  have hstable : (prefixWord ++ tailWord_1066149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066149).length < 2 ^ (prefixWord ++ tailWord_1066149).sum := by decide
  have hdescent : baseEnd_1066149 < baseStart_1066149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066163 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 7]
def baseStart_1066163 : Nat := 118140960795 + 1066163 * 2 ^ 59
def prefixEnd_1066163 : Nat := 4983230072969 + 3 ^ 40 * 1066163 * 2
def baseEnd_1066163 : Nat := 243312922239829940470805

theorem tailTrace_1066163 : CollatzResearch.WordTrace tailWord_1066163 prefixEnd_1066163 243312922239829940470805 := by
  unfold tailWord_1066163
  simp only [CollatzResearch.WordTrace]
  refine ⟨38886159236481011988891143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25924106157654007992594095 38886159236481011988891143)
  ·
    refine ⟨58329238854721517983336715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38886159236481011988891143 58329238854721517983336715)
    ·
      refine ⟨87493858282082276975005073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58329238854721517983336715 87493858282082276975005073)
      ·
        refine ⟨65620393711561707731253805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87493858282082276975005073 65620393711561707731253805)
        ·
          refine ⟨24607647641835640399220177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65620393711561707731253805 24607647641835640399220177)
          ·
            refine ⟨18455735731376730299415133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24607647641835640399220177 18455735731376730299415133)
            ·
              refine ⟨6920900899266273862280675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18455735731376730299415133 6920900899266273862280675)
              ·
                refine ⟨10381351348899410793421013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6920900899266273862280675 10381351348899410793421013)
                ·
                  refine ⟨243312922239829940470805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10381351348899410793421013 243312922239829940470805)
                  ·
                    rfl

theorem cell21_1066163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_1066163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066163 prefixEnd_1066163 := by exact prefixLift 1066163
  have htrace : WordTrace (prefixWord ++ tailWord_1066163) baseStart_1066163 baseEnd_1066163 := by
    simpa [prefixWord, tailWord_1066163, baseEnd_1066163] using wordTrace_append hprefix tailTrace_1066163
  have hstable : (prefixWord ++ tailWord_1066163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066163).length < 2 ^ (prefixWord ++ tailWord_1066163).sum := by decide
  have hdescent : baseEnd_1066163 < baseStart_1066163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066197 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 5]
def baseStart_1066197 : Nat := 118140960795 + 1066197 * 2 ^ 59
def prefixEnd_1066197 : Nat := 4983230072969 + 3 ^ 40 * 1066197 * 2
def baseEnd_1066197 : Nat := 243320681503053436904069

theorem tailTrace_1066197 : CollatzResearch.WordTrace tailWord_1066197 prefixEnd_1066197 243320681503053436904069 := by
  unfold tailWord_1066197
  simp only [CollatzResearch.WordTrace]
  refine ⟨38887399318357835795628845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25924932878905223863752563 38887399318357835795628845)
  ·
    refine ⟨14582774744384188423360817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38887399318357835795628845 14582774744384188423360817)
    ·
      refine ⟨10937081058288141317520613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14582774744384188423360817 10937081058288141317520613)
      ·
        refine ⟨2050702698429026497035115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10937081058288141317520613 2050702698429026497035115)
        ·
          refine ⟨3076054047643539745552673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050702698429026497035115 3076054047643539745552673)
          ·
            refine ⟨2307040535732654809164505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3076054047643539745552673 2307040535732654809164505)
            ·
              refine ⟨1730280401799491106873379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2307040535732654809164505 1730280401799491106873379)
              ·
                refine ⟨2595420602699236660310069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730280401799491106873379 2595420602699236660310069)
                ·
                  refine ⟨243320681503053436904069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2595420602699236660310069 243320681503053436904069)
                  ·
                    rfl

theorem cell21_1066197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_1066197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066197 prefixEnd_1066197 := by exact prefixLift 1066197
  have htrace : WordTrace (prefixWord ++ tailWord_1066197) baseStart_1066197 baseEnd_1066197 := by
    simpa [prefixWord, tailWord_1066197, baseEnd_1066197] using wordTrace_append hprefix tailTrace_1066197
  have hstable : (prefixWord ++ tailWord_1066197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066197).length < 2 ^ (prefixWord ++ tailWord_1066197).sum := by decide
  have hdescent : baseEnd_1066197 < baseStart_1066197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066301 : List Nat := [1, 4, 1, 5, 10]
def baseStart_1066301 : Nat := 118140960795 + 1066301 * 2 ^ 59
def prefixEnd_1066301 : Nat := 4983230072969 + 3 ^ 40 * 1066301 * 2
def baseEnd_1066301 : Nat := 3004252045925584779883

theorem tailTrace_1066301 : CollatzResearch.WordTrace tailWord_1066301 prefixEnd_1066301 3004252045925584779883 := by
  unfold tailWord_1066301
  simp only [CollatzResearch.WordTrace]
  refine ⟨38891192509981061557414757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25927461673320707704943171 38891192509981061557414757)
  ·
    refine ⟨7292098595621449042015267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38891192509981061557414757 7292098595621449042015267)
    ·
      refine ⟨10938147893432173563022901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7292098595621449042015267 10938147893432173563022901)
      ·
        refine ⟨1025451365009266271533397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10938147893432173563022901 1025451365009266271533397)
        ·
          refine ⟨3004252045925584779883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1025451365009266271533397 3004252045925584779883)
          ·
            rfl

theorem cell21_1066301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 10].length) (baseStart_1066301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066301 prefixEnd_1066301 := by exact prefixLift 1066301
  have htrace : WordTrace (prefixWord ++ tailWord_1066301) baseStart_1066301 baseEnd_1066301 := by
    simpa [prefixWord, tailWord_1066301, baseEnd_1066301] using wordTrace_append hprefix tailTrace_1066301
  have hstable : (prefixWord ++ tailWord_1066301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066301).length < 2 ^ (prefixWord ++ tailWord_1066301).sum := by decide
  have hdescent : baseEnd_1066301 < baseStart_1066301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066349 : List Nat := [1, 5, 1, 1, 1, 3, 1, 5, 3]
def baseStart_1066349 : Nat := 118140960795 + 1066349 * 2 ^ 59
def prefixEnd_1066349 : Nat := 4983230072969 + 3 ^ 40 * 1066349 * 2
def baseEnd_1066349 : Nat := 243355369973934950370425

theorem tailTrace_1066349 : CollatzResearch.WordTrace tailWord_1066349 prefixEnd_1066349 243355369973934950370425 := by
  unfold tailWord_1066349
  simp only [CollatzResearch.WordTrace]
  refine ⟨38892943213807165755162101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25928628809204777170108067 38892943213807165755162101)
  ·
    refine ⟨3646213426294421789546447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38892943213807165755162101 3646213426294421789546447)
    ·
      refine ⟨5469320139441632684319671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3646213426294421789546447 5469320139441632684319671)
      ·
        refine ⟨8203980209162449026479507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5469320139441632684319671 8203980209162449026479507)
        ·
          refine ⟨12305970313743673539719261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8203980209162449026479507 12305970313743673539719261)
          ·
            refine ⟨4614738867653877577394723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12305970313743673539719261 4614738867653877577394723)
            ·
              refine ⟨6922108301480816366092085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4614738867653877577394723 6922108301480816366092085)
              ·
                refine ⟨648947653263826534321133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6922108301480816366092085 648947653263826534321133)
                ·
                  refine ⟨243355369973934950370425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 648947653263826534321133 243355369973934950370425)
                  ·
                    rfl

theorem cell21_1066349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_1066349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066349 prefixEnd_1066349 := by exact prefixLift 1066349
  have htrace : WordTrace (prefixWord ++ tailWord_1066349) baseStart_1066349 baseEnd_1066349 := by
    simpa [prefixWord, tailWord_1066349, baseEnd_1066349] using wordTrace_append hprefix tailTrace_1066349
  have hstable : (prefixWord ++ tailWord_1066349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066349).length < 2 ^ (prefixWord ++ tailWord_1066349).sum := by decide
  have hdescent : baseEnd_1066349 < baseStart_1066349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066425 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 5]
def baseStart_1066425 : Nat := 118140960795 + 1066425 * 2 ^ 59
def prefixEnd_1066425 : Nat := 4983230072969 + 3 ^ 40 * 1066425 * 2
def baseEnd_1066425 : Nat := 243372714209375707103603

theorem tailTrace_1066425 : CollatzResearch.WordTrace tailWord_1066425 prefixEnd_1066425 243372714209375707103603 := by
  unfold tailWord_1066425
  simp only [CollatzResearch.WordTrace]
  refine ⟨38895715161531830734928729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25930476774354553823285819 38895715161531830734928729)
  ·
    refine ⟨29171786371148873051196547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38895715161531830734928729 29171786371148873051196547)
    ·
      refine ⟨43757679556723309576794821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29171786371148873051196547 43757679556723309576794821)
      ·
        refine ⟨8204564916885620545649029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43757679556723309576794821 8204564916885620545649029)
        ·
          refine ⟨1538355921916053852309193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8204564916885620545649029 1538355921916053852309193)
          ·
            refine ⟨1153766941437040389231895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1538355921916053852309193 1153766941437040389231895)
            ·
              refine ⟨1730650412155560583847843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153766941437040389231895 1730650412155560583847843)
              ·
                refine ⟨2595975618233340875771765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730650412155560583847843 2595975618233340875771765)
                ·
                  refine ⟨243372714209375707103603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2595975618233340875771765 243372714209375707103603)
                  ·
                    rfl

theorem cell21_1066425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_1066425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066425 prefixEnd_1066425 := by exact prefixLift 1066425
  have htrace : WordTrace (prefixWord ++ tailWord_1066425) baseStart_1066425 baseEnd_1066425 := by
    simpa [prefixWord, tailWord_1066425, baseEnd_1066425] using wordTrace_append hprefix tailTrace_1066425
  have hstable : (prefixWord ++ tailWord_1066425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066425).length < 2 ^ (prefixWord ++ tailWord_1066425).sum := by decide
  have hdescent : baseEnd_1066425 < baseStart_1066425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066608 : List Nat := [2, 1, 1, 1, 6, 3, 2, 1, 4]
def baseStart_1066608 : Nat := 118140960795 + 1066608 * 2 ^ 59
def prefixEnd_1066608 : Nat := 4983230072969 + 3 ^ 40 * 1066608 * 2
def baseEnd_1066608 : Nat := 243414477302608055553229

theorem tailTrace_1066608 : CollatzResearch.WordTrace tailWord_1066608 prefixEnd_1066608 243414477302608055553229 := by
  unfold tailWord_1066608
  simp only [CollatzResearch.WordTrace]
  refine ⟨19451194859934426494420239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25934926479912568659226985 19451194859934426494420239)
  ·
    refine ⟨29176792289901639741630359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19451194859934426494420239 29176792289901639741630359)
    ·
      refine ⟨43765188434852459612445539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29176792289901639741630359 43765188434852459612445539)
      ·
        refine ⟨65647782652278689418668309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43765188434852459612445539 65647782652278689418668309)
        ·
          refine ⟨3077239811825563566500077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65647782652278689418668309 3077239811825563566500077)
          ·
            refine ⟨1153964929434586337437529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3077239811825563566500077 1153964929434586337437529)
            ·
              refine ⟨865473697075939753078147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1153964929434586337437529 865473697075939753078147)
              ·
                refine ⟨1298210545613909629617221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865473697075939753078147 1298210545613909629617221)
                ·
                  refine ⟨243414477302608055553229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1298210545613909629617221 243414477302608055553229)
                  ·
                    rfl

theorem cell21_1066608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_1066608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066608 prefixEnd_1066608 := by exact prefixLift 1066608
  have htrace : WordTrace (prefixWord ++ tailWord_1066608) baseStart_1066608 baseEnd_1066608 := by
    simpa [prefixWord, tailWord_1066608, baseEnd_1066608] using wordTrace_append hprefix tailTrace_1066608
  have hstable : (prefixWord ++ tailWord_1066608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066608).length < 2 ^ (prefixWord ++ tailWord_1066608).sum := by decide
  have hdescent : baseEnd_1066608 < baseStart_1066608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066633 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 8]
def baseStart_1066633 : Nat := 118140960795 + 1066633 * 2 ^ 59
def prefixEnd_1066633 : Nat := 4983230072969 + 3 ^ 40 * 1066633 * 2
def baseEnd_1066633 : Nat := 243420182643213567636511

theorem tailTrace_1066633 : CollatzResearch.WordTrace tailWord_1066633 prefixEnd_1066633 243420182643213567636511 := by
  unfold tailWord_1066633
  simp only [CollatzResearch.WordTrace]
  refine ⟨38903301544778282258500553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25935534363185521505667035 38903301544778282258500553)
  ·
    refine ⟨29177476158583711693875415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38903301544778282258500553 29177476158583711693875415)
    ·
      refine ⟨43766214237875567540813123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29177476158583711693875415 43766214237875567540813123)
      ·
        refine ⟨65649321356813351311219685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43766214237875567540813123 65649321356813351311219685)
        ·
          refine ⟨12309247754402503370853691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65649321356813351311219685 12309247754402503370853691)
          ·
            refine ⟨18463871631603755056280537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12309247754402503370853691 18463871631603755056280537)
            ·
              refine ⟨13847903723702816292210403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18463871631603755056280537 13847903723702816292210403)
              ·
                refine ⟨20771855585554224438315605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13847903723702816292210403 20771855585554224438315605)
                ·
                  refine ⟨243420182643213567636511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20771855585554224438315605 243420182643213567636511)
                  ·
                    rfl

theorem cell21_1066633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_1066633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066633 prefixEnd_1066633 := by exact prefixLift 1066633
  have htrace : WordTrace (prefixWord ++ tailWord_1066633) baseStart_1066633 baseEnd_1066633 := by
    simpa [prefixWord, tailWord_1066633, baseEnd_1066633] using wordTrace_append hprefix tailTrace_1066633
  have hstable : (prefixWord ++ tailWord_1066633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066633).length < 2 ^ (prefixWord ++ tailWord_1066633).sum := by decide
  have hdescent : baseEnd_1066633 < baseStart_1066633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066636 : List Nat := [2, 2, 1, 2, 1, 1, 4, 5, 3]
def baseStart_1066636 : Nat := 118140960795 + 1066636 * 2 ^ 59
def prefixEnd_1066636 : Nat := 4983230072969 + 3 ^ 40 * 1066636 * 2
def baseEnd_1066636 : Nat := 243420867284086229086505

theorem tailTrace_1066636 : CollatzResearch.WordTrace tailWord_1066636 prefixEnd_1066636 243420867284086229086505 := by
  unfold tailWord_1066636
  simp only [CollatzResearch.WordTrace]
  refine ⟨19451705481883706885429881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25935607309178275847239841 19451705481883706885429881)
  ·
    refine ⟨14588779111412780164072411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19451705481883706885429881 14588779111412780164072411)
    ·
      refine ⟨21883168667119170246108617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14588779111412780164072411 21883168667119170246108617)
      ·
        refine ⟨16412376500339377684581463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21883168667119170246108617 16412376500339377684581463)
        ·
          refine ⟨24618564750509066526872195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16412376500339377684581463 24618564750509066526872195)
          ·
            refine ⟨36927847125763599790308293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24618564750509066526872195 36927847125763599790308293)
            ·
              refine ⟨6923971336080674960682805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36927847125763599790308293 6923971336080674960682805)
              ·
                refine ⟨649122312757563277564013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6923971336080674960682805 649122312757563277564013)
                ·
                  refine ⟨243420867284086229086505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649122312757563277564013 243420867284086229086505)
                  ·
                    rfl

theorem cell21_1066636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_1066636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066636 prefixEnd_1066636 := by exact prefixLift 1066636
  have htrace : WordTrace (prefixWord ++ tailWord_1066636) baseStart_1066636 baseEnd_1066636 := by
    simpa [prefixWord, tailWord_1066636, baseEnd_1066636] using wordTrace_append hprefix tailTrace_1066636
  have hstable : (prefixWord ++ tailWord_1066636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066636).length < 2 ^ (prefixWord ++ tailWord_1066636).sum := by decide
  have hdescent : baseEnd_1066636 < baseStart_1066636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066701 : List Nat := [1, 6, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1066701 : Nat := 118140960795 + 1066701 * 2 ^ 59
def prefixEnd_1066701 : Nat := 4983230072969 + 3 ^ 40 * 1066701 * 2
def baseEnd_1066701 : Nat := 243435701169660560503039

theorem tailTrace_1066701 : CollatzResearch.WordTrace tailWord_1066701 prefixEnd_1066701 243435701169660560503039 := by
  unfold tailWord_1066701
  simp only [CollatzResearch.WordTrace]
  refine ⟨38905781708531929871975957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25937187805687953247983971 38905781708531929871975957)
  ·
    refine ⟨1823708517587434212748873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38905781708531929871975957 1823708517587434212748873)
    ·
      refine ⟨1367781388190575659561655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1823708517587434212748873 1367781388190575659561655)
      ·
        refine ⟨2051672082285863489342483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1367781388190575659561655 2051672082285863489342483)
        ·
          refine ⟨3077508123428795234013725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2051672082285863489342483 3077508123428795234013725)
          ·
            refine ⟨1154065546285798212755147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3077508123428795234013725 1154065546285798212755147)
            ·
              refine ⟨1731098319428697319132721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154065546285798212755147 1731098319428697319132721)
              ·
                refine ⟨1298323739571522989349541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1731098319428697319132721 1298323739571522989349541)
                ·
                  refine ⟨243435701169660560503039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1298323739571522989349541 243435701169660560503039)
                  ·
                    rfl

theorem cell21_1066701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1066701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066701 prefixEnd_1066701 := by exact prefixLift 1066701
  have htrace : WordTrace (prefixWord ++ tailWord_1066701) baseStart_1066701 baseEnd_1066701 := by
    simpa [prefixWord, tailWord_1066701, baseEnd_1066701] using wordTrace_append hprefix tailTrace_1066701
  have hstable : (prefixWord ++ tailWord_1066701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066701).length < 2 ^ (prefixWord ++ tailWord_1066701).sum := by decide
  have hdescent : baseEnd_1066701 < baseStart_1066701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066712 : List Nat := [2, 1, 2, 2, 3, 1, 1, 6, 3]
def baseStart_1066712 : Nat := 118140960795 + 1066712 * 2 ^ 59
def prefixEnd_1066712 : Nat := 4983230072969 + 3 ^ 40 * 1066712 * 2
def baseEnd_1066712 : Nat := 243438211519526985819683

theorem tailTrace_1066712 : CollatzResearch.WordTrace tailWord_1066712 prefixEnd_1066712 243438211519526985819683 := by
  unfold tailWord_1066712
  simp only [CollatzResearch.WordTrace]
  refine ⟨19453091455746039375313195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25937455274328052500417593 19453091455746039375313195)
  ·
    refine ⟨29179637183619059062969793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19453091455746039375313195 29179637183619059062969793)
    ·
      refine ⟨21884727887714294297227345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29179637183619059062969793 21884727887714294297227345)
      ·
        refine ⟨16413545915785720722920509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21884727887714294297227345 16413545915785720722920509)
        ·
          refine ⟨6155079718419645271095191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16413545915785720722920509 6155079718419645271095191)
          ·
            refine ⟨9232619577629467906642787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6155079718419645271095191 9232619577629467906642787)
            ·
              refine ⟨13848929366444201859964181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9232619577629467906642787 13848929366444201859964181)
              ·
                refine ⟨649168564052071962185821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13848929366444201859964181 649168564052071962185821)
                ·
                  refine ⟨243438211519526985819683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649168564052071962185821 243438211519526985819683)
                  ·
                    rfl

theorem cell21_1066712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 3].length) (baseStart_1066712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066712 prefixEnd_1066712 := by exact prefixLift 1066712
  have htrace : WordTrace (prefixWord ++ tailWord_1066712) baseStart_1066712 baseEnd_1066712 := by
    simpa [prefixWord, tailWord_1066712, baseEnd_1066712] using wordTrace_append hprefix tailTrace_1066712
  have hstable : (prefixWord ++ tailWord_1066712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066712).length < 2 ^ (prefixWord ++ tailWord_1066712).sum := by decide
  have hdescent : baseEnd_1066712 < baseStart_1066712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066833 : List Nat := [1, 2, 2, 1, 5, 3, 1, 6]
def baseStart_1066833 : Nat := 118140960795 + 1066833 * 2 ^ 59
def prefixEnd_1066833 : Nat := 4983230072969 + 3 ^ 40 * 1066833 * 2
def baseEnd_1066833 : Nat := 81155275122685888100923

theorem tailTrace_1066833 : CollatzResearch.WordTrace tailWord_1066833 prefixEnd_1066833 81155275122685888100923 := by
  unfold tailWord_1066833
  simp only [CollatzResearch.WordTrace]
  refine ⟨38910596144053716415781153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25940397429369144277187435 38910596144053716415781153)
  ·
    refine ⟨29182947108040287311835865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38910596144053716415781153 29182947108040287311835865)
    ·
      refine ⟨21887210331030215483876899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29182947108040287311835865 21887210331030215483876899)
      ·
        refine ⟨32830815496545323225815349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21887210331030215483876899 32830815496545323225815349)
        ·
          refine ⟨3077888952801124052420189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32830815496545323225815349 3077888952801124052420189)
          ·
            refine ⟨1154208357300421519657571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3077888952801124052420189 1154208357300421519657571)
            ·
              refine ⟨1731312535950632279486357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154208357300421519657571 1731312535950632279486357)
              ·
                refine ⟨81155275122685888100923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1731312535950632279486357 81155275122685888100923)
                ·
                  rfl

theorem cell21_1066833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 6].length) (baseStart_1066833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066833 prefixEnd_1066833 := by exact prefixLift 1066833
  have htrace : WordTrace (prefixWord ++ tailWord_1066833) baseStart_1066833 baseEnd_1066833 := by
    simpa [prefixWord, tailWord_1066833, baseEnd_1066833] using wordTrace_append hprefix tailTrace_1066833
  have hstable : (prefixWord ++ tailWord_1066833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066833).length < 2 ^ (prefixWord ++ tailWord_1066833).sum := by decide
  have hdescent : baseEnd_1066833 < baseStart_1066833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066847 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 5]
def baseStart_1066847 : Nat := 118140960795 + 1066847 * 2 ^ 59
def prefixEnd_1066847 : Nat := 4983230072969 + 3 ^ 40 * 1066847 * 2
def baseEnd_1066847 : Nat := 243469020358796751069407

theorem tailTrace_1066847 : CollatzResearch.WordTrace tailWord_1066847 prefixEnd_1066847 243469020358796751069407 := by
  unfold tailWord_1066847
  simp only [CollatzResearch.WordTrace]
  refine ⟨38911106766002996806790795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25940737844001997871193863 38911106766002996806790795)
  ·
    refine ⟨58366660149004495210186193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38911106766002996806790795 58366660149004495210186193)
    ·
      refine ⟨43774995111753371407639645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58366660149004495210186193 43774995111753371407639645)
      ·
        refine ⟨16415623166907514277864867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43774995111753371407639645 16415623166907514277864867)
        ·
          refine ⟨24623434750361271416797301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16415623166907514277864867 24623434750361271416797301)
          ·
            refine ⟨2308447007846369195324747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24623434750361271416797301 2308447007846369195324747)
            ·
              refine ⟨3462670511769553792987121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308447007846369195324747 3462670511769553792987121)
              ·
                refine ⟨2597002883827165344740341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3462670511769553792987121 2597002883827165344740341)
                ·
                  refine ⟨243469020358796751069407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2597002883827165344740341 243469020358796751069407)
                  ·
                    rfl

theorem cell21_1066847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 5].length) (baseStart_1066847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066847 prefixEnd_1066847 := by exact prefixLift 1066847
  have htrace : WordTrace (prefixWord ++ tailWord_1066847) baseStart_1066847 baseEnd_1066847 := by
    simpa [prefixWord, tailWord_1066847, baseEnd_1066847] using wordTrace_append hprefix tailTrace_1066847
  have hstable : (prefixWord ++ tailWord_1066847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066847).length < 2 ^ (prefixWord ++ tailWord_1066847).sum := by decide
  have hdescent : baseEnd_1066847 < baseStart_1066847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066850 : List Nat := [3, 3, 2, 1, 2, 2, 3, 5]
def baseStart_1066850 : Nat := 118140960795 + 1066850 * 2 ^ 59
def prefixEnd_1066850 : Nat := 4983230072969 + 3 ^ 40 * 1066850 * 2
def baseEnd_1066850 : Nat := 81156568333223137506467

theorem tailTrace_1066850 : CollatzResearch.WordTrace tailWord_1066850 prefixEnd_1066850 81156568333223137506467 := by
  unfold tailWord_1066850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9727804046248032079787501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25940810789994752212766669 9727804046248032079787501)
  ·
    refine ⟨3647926517343012029920313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9727804046248032079787501 3647926517343012029920313)
    ·
      refine ⟨2735944888007259022440235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3647926517343012029920313 2735944888007259022440235)
      ·
        refine ⟨4103917332010888533660353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2735944888007259022440235 4103917332010888533660353)
        ·
          refine ⟨3077937999008166400245265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4103917332010888533660353 3077937999008166400245265)
          ·
            refine ⟨2308453499256124800183949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3077937999008166400245265 2308453499256124800183949)
            ·
              refine ⟨865670062221046800068981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2308453499256124800183949 865670062221046800068981)
              ·
                refine ⟨81156568333223137506467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 865670062221046800068981 81156568333223137506467)
                ·
                  rfl

theorem cell21_1066850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_1066850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066850 prefixEnd_1066850 := by exact prefixLift 1066850
  have htrace : WordTrace (prefixWord ++ tailWord_1066850) baseStart_1066850 baseEnd_1066850 := by
    simpa [prefixWord, tailWord_1066850, baseEnd_1066850] using wordTrace_append hprefix tailTrace_1066850
  have hstable : (prefixWord ++ tailWord_1066850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066850).length < 2 ^ (prefixWord ++ tailWord_1066850).sum := by decide
  have hdescent : baseEnd_1066850 < baseStart_1066850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066881 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 5]
def baseStart_1066881 : Nat := 118140960795 + 1066881 * 2 ^ 59
def prefixEnd_1066881 : Nat := 4983230072969 + 3 ^ 40 * 1066881 * 2
def baseEnd_1066881 : Nat := 243476779622020247502671

theorem tailTrace_1066881 : CollatzResearch.WordTrace tailWord_1066881 prefixEnd_1066881 243476779622020247502671 := by
  unfold tailWord_1066881
  simp only [CollatzResearch.WordTrace]
  refine ⟨38912346847879820613528497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25941564565253213742352331 38912346847879820613528497)
  ·
    refine ⟨29184260135909865460146373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38912346847879820613528497 29184260135909865460146373)
    ·
      refine ⟨5472048775483099773777445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29184260135909865460146373 5472048775483099773777445)
      ·
        refine ⟨1026009145403081207583271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5472048775483099773777445 1026009145403081207583271)
        ·
          refine ⟨1539013718104621811374907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026009145403081207583271 1539013718104621811374907)
          ·
            refine ⟨2308520577156932717062361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539013718104621811374907 2308520577156932717062361)
            ·
              refine ⟨1731390432867699537796771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2308520577156932717062361 1731390432867699537796771)
              ·
                refine ⟨2597085649301549306695157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731390432867699537796771 2597085649301549306695157)
                ·
                  refine ⟨243476779622020247502671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2597085649301549306695157 243476779622020247502671)
                  ·
                    rfl

theorem cell21_1066881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_1066881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066881 prefixEnd_1066881 := by exact prefixLift 1066881
  have htrace : WordTrace (prefixWord ++ tailWord_1066881) baseStart_1066881 baseEnd_1066881 := by
    simpa [prefixWord, tailWord_1066881, baseEnd_1066881] using wordTrace_append hprefix tailTrace_1066881
  have hstable : (prefixWord ++ tailWord_1066881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066881).length < 2 ^ (prefixWord ++ tailWord_1066881).sum := by decide
  have hdescent : baseEnd_1066881 < baseStart_1066881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066909 : List Nat := [1, 4, 2, 1, 2, 2, 4, 5]
def baseStart_1066909 : Nat := 118140960795 + 1066909 * 2 ^ 59
def prefixEnd_1066909 : Nat := 4983230072969 + 3 ^ 40 * 1066909 * 2
def baseEnd_1066909 : Nat := 81161056534499473678649

theorem tailTrace_1066909 : CollatzResearch.WordTrace tailWord_1066909 prefixEnd_1066909 81161056534499473678649 := by
  unfold tailWord_1066909
  simp only [CollatzResearch.WordTrace]
  refine ⟨38913368091778381395547781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25942245394518920930365187 38913368091778381395547781)
  ·
    refine ⟨7296256517208446511665209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38913368091778381395547781 7296256517208446511665209)
    ·
      refine ⟨5472192387906334883748907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7296256517208446511665209 5472192387906334883748907)
      ·
        refine ⟨8208288581859502325623361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5472192387906334883748907 8208288581859502325623361)
        ·
          refine ⟨6156216436394626744217521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8208288581859502325623361 6156216436394626744217521)
          ·
            refine ⟨4617162327295970058163141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6156216436394626744217521 4617162327295970058163141)
            ·
              refine ⟨865717936367994385905589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4617162327295970058163141 865717936367994385905589)
              ·
                refine ⟨81161056534499473678649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 865717936367994385905589 81161056534499473678649)
                ·
                  rfl

theorem cell21_1066909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 5].length) (baseStart_1066909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066909 prefixEnd_1066909 := by exact prefixLift 1066909
  have htrace : WordTrace (prefixWord ++ tailWord_1066909) baseStart_1066909 baseEnd_1066909 := by
    simpa [prefixWord, tailWord_1066909, baseEnd_1066909] using wordTrace_append hprefix tailTrace_1066909
  have hstable : (prefixWord ++ tailWord_1066909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066909).length < 2 ^ (prefixWord ++ tailWord_1066909).sum := by decide
  have hdescent : baseEnd_1066909 < baseStart_1066909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066937 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 6]
def baseStart_1066937 : Nat := 118140960795 + 1066937 * 2 ^ 59
def prefixEnd_1066937 : Nat := 4983230072969 + 3 ^ 40 * 1066937 * 2
def baseEnd_1066937 : Nat := 243489559584976594569223

theorem tailTrace_1066937 : CollatzResearch.WordTrace tailWord_1066937 prefixEnd_1066937 243489559584976594569223 := by
  unfold tailWord_1066937
  simp only [CollatzResearch.WordTrace]
  refine ⟨38914389335676942177567065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25942926223784628118378043 38914389335676942177567065)
  ·
    refine ⟨29185792001757706633175299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38914389335676942177567065 29185792001757706633175299)
    ·
      refine ⟨43778688002636559949762949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29185792001757706633175299 43778688002636559949762949)
      ·
        refine ⟨8208504000494354990580553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43778688002636559949762949 8208504000494354990580553)
        ·
          refine ⟨6156378000370766242935415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8208504000494354990580553 6156378000370766242935415)
          ·
            refine ⟨9234567000556149364403123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6156378000370766242935415 9234567000556149364403123)
            ·
              refine ⟨13851850500834224046604685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9234567000556149364403123 13851850500834224046604685)
              ·
                refine ⟨5194443937812834017476757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13851850500834224046604685 5194443937812834017476757)
                ·
                  refine ⟨243489559584976594569223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5194443937812834017476757 243489559584976594569223)
                  ·
                    rfl

theorem cell21_1066937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_1066937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1066937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1066937 prefixEnd_1066937 := by exact prefixLift 1066937
  have htrace : WordTrace (prefixWord ++ tailWord_1066937) baseStart_1066937 baseEnd_1066937 := by
    simpa [prefixWord, tailWord_1066937, baseEnd_1066937] using wordTrace_append hprefix tailTrace_1066937
  have hstable : (prefixWord ++ tailWord_1066937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066937).length < 2 ^ (prefixWord ++ tailWord_1066937).sum := by decide
  have hdescent : baseEnd_1066937 < baseStart_1066937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067027 : List Nat := [1, 1, 1, 2, 1, 4, 2, 9]
def baseStart_1067027 : Nat := 118140960795 + 1067027 * 2 ^ 59
def prefixEnd_1067027 : Nat := 4983230072969 + 3 ^ 40 * 1067027 * 2
def baseEnd_1067027 : Nat := 81170032937052146023013

theorem tailTrace_1067027 : CollatzResearch.WordTrace tailWord_1067027 prefixEnd_1067027 81170032937052146023013 := by
  unfold tailWord_1067027
  simp only [CollatzResearch.WordTrace]
  refine ⟨38917671905350887548343335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25945114603567258365562223 38917671905350887548343335)
  ·
    refine ⟨58376507858026331322515003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38917671905350887548343335 58376507858026331322515003)
    ·
      refine ⟨87564761787039496983772505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58376507858026331322515003 87564761787039496983772505)
      ·
        refine ⟨65673571340279622737829379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87564761787039496983772505 65673571340279622737829379)
        ·
          refine ⟨98510357010419434106744069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65673571340279622737829379 98510357010419434106744069)
          ·
            refine ⟨18470691939453643895014513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98510357010419434106744069 18470691939453643895014513)
            ·
              refine ⟨13853018954590232921260885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18470691939453643895014513 13853018954590232921260885)
              ·
                refine ⟨81170032937052146023013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13853018954590232921260885 81170032937052146023013)
                ·
                  rfl

theorem cell21_1067027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 9].length) (baseStart_1067027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067027 prefixEnd_1067027 := by exact prefixLift 1067027
  have htrace : WordTrace (prefixWord ++ tailWord_1067027) baseStart_1067027 baseEnd_1067027 := by
    simpa [prefixWord, tailWord_1067027, baseEnd_1067027] using wordTrace_append hprefix tailTrace_1067027
  have hstable : (prefixWord ++ tailWord_1067027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067027).length < 2 ^ (prefixWord ++ tailWord_1067027).sum := by decide
  have hdescent : baseEnd_1067027 < baseStart_1067027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067047 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 6]
def baseStart_1067047 : Nat := 118140960795 + 1067047 * 2 ^ 59
def prefixEnd_1067047 : Nat := 4983230072969 + 3 ^ 40 * 1067047 * 2
def baseEnd_1067047 : Nat := 243514663083640847735665

theorem tailTrace_1067047 : CollatzResearch.WordTrace tailWord_1067047 prefixEnd_1067047 243514663083640847735665 := by
  unfold tailWord_1067047
  simp only [CollatzResearch.WordTrace]
  refine ⟨38918401365278430964071395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25945600910185620642714263 38918401365278430964071395)
  ·
    refine ⟨58377602047917646446107093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38918401365278430964071395 58377602047917646446107093)
    ·
      refine ⟨1368225047998069838580635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 58377602047917646446107093 1368225047998069838580635)
      ·
        refine ⟨2052337571997104757870953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1368225047998069838580635 2052337571997104757870953)
        ·
          refine ⟨1539253178997828568403215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2052337571997104757870953 1539253178997828568403215)
          ·
            refine ⟨2308879768496742852604823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539253178997828568403215 2308879768496742852604823)
            ·
              refine ⟨3463319652745114278907235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308879768496742852604823 3463319652745114278907235)
              ·
                refine ⟨5194979479117671418360853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3463319652745114278907235 5194979479117671418360853)
                ·
                  refine ⟨243514663083640847735665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5194979479117671418360853 243514663083640847735665)
                  ·
                    rfl

theorem cell21_1067047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 6].length) (baseStart_1067047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067047 prefixEnd_1067047 := by exact prefixLift 1067047
  have htrace : WordTrace (prefixWord ++ tailWord_1067047) baseStart_1067047 baseEnd_1067047 := by
    simpa [prefixWord, tailWord_1067047, baseEnd_1067047] using wordTrace_append hprefix tailTrace_1067047
  have hstable : (prefixWord ++ tailWord_1067047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067047).length < 2 ^ (prefixWord ++ tailWord_1067047).sum := by decide
  have hdescent : baseEnd_1067047 < baseStart_1067047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067109 : List Nat := [1, 3, 1, 3, 2, 3, 3, 2, 3]
def baseStart_1067109 : Nat := 118140960795 + 1067109 * 2 ^ 59
def prefixEnd_1067109 : Nat := 4983230072969 + 3 ^ 40 * 1067109 * 2
def baseEnd_1067109 : Nat := 243528812328342517702205

theorem tailTrace_1067109 : CollatzResearch.WordTrace tailWord_1067109 prefixEnd_1067109 243528812328342517702205 := by
  unfold tailWord_1067109
  simp only [CollatzResearch.WordTrace]
  refine ⟨38920662691053815552828381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25947108460702543701885587 38920662691053815552828381)
  ·
    refine ⟨14595248509145180832310643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38920662691053815552828381 14595248509145180832310643)
    ·
      refine ⟨21892872763717771248465965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14595248509145180832310643 21892872763717771248465965)
      ·
        refine ⟨8209827286394164218174737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21892872763717771248465965 8209827286394164218174737)
        ·
          refine ⟨6157370464795623163631053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8209827286394164218174737 6157370464795623163631053)
          ·
            refine ⟨2309013924298358686361645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6157370464795623163631053 2309013924298358686361645)
            ·
              refine ⟨865880221611884507385617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2309013924298358686361645 865880221611884507385617)
              ·
                refine ⟨649410166208913380539213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 865880221611884507385617 649410166208913380539213)
                ·
                  refine ⟨243528812328342517702205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649410166208913380539213 243528812328342517702205)
                  ·
                    rfl

theorem cell21_1067109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_1067109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067109 prefixEnd_1067109 := by exact prefixLift 1067109
  have htrace : WordTrace (prefixWord ++ tailWord_1067109) baseStart_1067109 baseEnd_1067109 := by
    simpa [prefixWord, tailWord_1067109, baseEnd_1067109] using wordTrace_append hprefix tailTrace_1067109
  have hstable : (prefixWord ++ tailWord_1067109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067109).length < 2 ^ (prefixWord ++ tailWord_1067109).sum := by decide
  have hdescent : baseEnd_1067109 < baseStart_1067109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067120 : List Nat := [2, 1, 1, 1, 5, 3, 2, 6]
def baseStart_1067120 : Nat := 118140960795 + 1067120 * 2 ^ 59
def prefixEnd_1067120 : Nat := 4983230072969 + 3 ^ 40 * 1067120 * 2
def baseEnd_1067120 : Nat := 81177107559402981006283

theorem tailTrace_1067120 : CollatzResearch.WordTrace tailWord_1067120 prefixEnd_1067120 81177107559402981006283 := by
  unfold tailWord_1067120
  simp only [CollatzResearch.WordTrace]
  refine ⟨19460531947006982215739407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25947375929342642954319209 19460531947006982215739407)
  ·
    refine ⟨29190797920510473323609111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19460531947006982215739407 29190797920510473323609111)
    ·
      refine ⟨43786196880765709985413667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29190797920510473323609111 43786196880765709985413667)
      ·
        refine ⟨65679295321148564978120501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43786196880765709985413667 65679295321148564978120501)
        ·
          refine ⟨6157433936357677966698797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65679295321148564978120501 6157433936357677966698797)
          ·
            refine ⟨2309037726134129237512049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6157433936357677966698797 2309037726134129237512049)
            ·
              refine ⟨1731778294600596928134037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2309037726134129237512049 1731778294600596928134037)
              ·
                refine ⟨81177107559402981006283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1731778294600596928134037 81177107559402981006283)
                ·
                  rfl

theorem cell21_1067120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_1067120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067120 prefixEnd_1067120 := by exact prefixLift 1067120
  have htrace : WordTrace (prefixWord ++ tailWord_1067120) baseStart_1067120 baseEnd_1067120 := by
    simpa [prefixWord, tailWord_1067120, baseEnd_1067120] using wordTrace_append hprefix tailTrace_1067120
  have hstable : (prefixWord ++ tailWord_1067120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067120).length < 2 ^ (prefixWord ++ tailWord_1067120).sum := by decide
  have hdescent : baseEnd_1067120 < baseStart_1067120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067168 : List Nat := [2, 1, 1, 4, 2, 3, 1, 4, 3]
def baseStart_1067168 : Nat := 118140960795 + 1067168 * 2 ^ 59
def prefixEnd_1067168 : Nat := 4983230072969 + 3 ^ 40 * 1067168 * 2
def baseEnd_1067168 : Nat := 243542276932171526218751

theorem tailTrace_1067168 : CollatzResearch.WordTrace tailWord_1067168 prefixEnd_1067168 243542276932171526218751 := by
  unfold tailWord_1067168
  simp only [CollatzResearch.WordTrace]
  refine ⟨19461407298920034314613079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25948543065226712419484105 19461407298920034314613079)
  ·
    refine ⟨29192110948380051471919619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19461407298920034314613079 29192110948380051471919619)
    ·
      refine ⟨43788166422570077207879429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29192110948380051471919619 43788166422570077207879429)
      ·
        refine ⟨8210281204231889476477393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43788166422570077207879429 8210281204231889476477393)
        ·
          refine ⟨6157710903173917107358045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8210281204231889476477393 6157710903173917107358045)
          ·
            refine ⟨2309141588690218915259267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6157710903173917107358045 2309141588690218915259267)
            ·
              refine ⟨3463712383035328372888901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309141588690218915259267 3463712383035328372888901)
              ·
                refine ⟨649446071819124069916669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3463712383035328372888901 649446071819124069916669)
                ·
                  refine ⟨243542276932171526218751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649446071819124069916669 243542276932171526218751)
                  ·
                    rfl

theorem cell21_1067168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 3].length) (baseStart_1067168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067168 prefixEnd_1067168 := by exact prefixLift 1067168
  have htrace : WordTrace (prefixWord ++ tailWord_1067168) baseStart_1067168 baseEnd_1067168 := by
    simpa [prefixWord, tailWord_1067168, baseEnd_1067168] using wordTrace_append hprefix tailTrace_1067168
  have hstable : (prefixWord ++ tailWord_1067168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067168).length < 2 ^ (prefixWord ++ tailWord_1067168).sum := by decide
  have hdescent : baseEnd_1067168 < baseStart_1067168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067188 : List Nat := [2, 5, 3, 1, 1, 1, 3, 5]
def baseStart_1067188 : Nat := 118140960795 + 1067188 * 2 ^ 59
def prefixEnd_1067188 : Nat := 4983230072969 + 3 ^ 40 * 1067188 * 2
def baseEnd_1067188 : Nat := 81182280401551978628459

theorem tailTrace_1067188 : CollatzResearch.WordTrace tailWord_1067188 prefixEnd_1067188 81182280401551978628459 := by
  unfold tailWord_1067188
  simp only [CollatzResearch.WordTrace]
  refine ⟨19461772028883806022477109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25949029371845074696636145 19461772028883806022477109)
  ·
    refine ⟨1824541127707856814607229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19461772028883806022477109 1824541127707856814607229)
    ·
      refine ⟨684202922890446305477711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1824541127707856814607229 684202922890446305477711)
      ·
        refine ⟨1026304384335669458216567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684202922890446305477711 1026304384335669458216567)
        ·
          refine ⟨1539456576503504187324851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026304384335669458216567 1539456576503504187324851)
          ·
            refine ⟨2309184864755256280987277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539456576503504187324851 2309184864755256280987277)
            ·
              refine ⟨865944324283221105370229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2309184864755256280987277 865944324283221105370229)
              ·
                refine ⟨81182280401551978628459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 865944324283221105370229 81182280401551978628459)
                ·
                  rfl

theorem cell21_1067188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 5].length) (baseStart_1067188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067188 prefixEnd_1067188 := by exact prefixLift 1067188
  have htrace : WordTrace (prefixWord ++ tailWord_1067188) baseStart_1067188 baseEnd_1067188 := by
    simpa [prefixWord, tailWord_1067188, baseEnd_1067188] using wordTrace_append hprefix tailTrace_1067188
  have hstable : (prefixWord ++ tailWord_1067188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067188).length < 2 ^ (prefixWord ++ tailWord_1067188).sum := by decide
  have hdescent : baseEnd_1067188 < baseStart_1067188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067202 : List Nat := [3, 5, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1067202 : Nat := 118140960795 + 1067202 * 2 ^ 59
def prefixEnd_1067202 : Nat := 4983230072969 + 3 ^ 40 * 1067202 * 2
def baseEnd_1067202 : Nat := 243550036195395022652015

theorem tailTrace_1067202 : CollatzResearch.WordTrace tailWord_1067202 prefixEnd_1067202 243550036195395022652015 := by
  unfold tailWord_1067202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9731013669929223108990965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25949369786477928290642573 9731013669929223108990965)
  ·
    refine ⟨912282531555864666467903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9731013669929223108990965 912282531555864666467903)
    ·
      refine ⟨1368423797333796999701855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 912282531555864666467903 1368423797333796999701855)
      ·
        refine ⟨2052635696000695499552783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1368423797333796999701855 2052635696000695499552783)
        ·
          refine ⟨3078953544001043249329175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2052635696000695499552783 3078953544001043249329175)
          ·
            refine ⟨4618430316001564873993763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3078953544001043249329175 4618430316001564873993763)
            ·
              refine ⟨6927645474002347310990645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4618430316001564873993763 6927645474002347310990645)
              ·
                refine ⟨649466763187720060405373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6927645474002347310990645 649466763187720060405373)
                ·
                  refine ⟨243550036195395022652015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649466763187720060405373 243550036195395022652015)
                  ·
                    rfl

theorem cell21_1067202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1067202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067202 prefixEnd_1067202 := by exact prefixLift 1067202
  have htrace : WordTrace (prefixWord ++ tailWord_1067202) baseStart_1067202 baseEnd_1067202 := by
    simpa [prefixWord, tailWord_1067202, baseEnd_1067202] using wordTrace_append hprefix tailTrace_1067202
  have hstable : (prefixWord ++ tailWord_1067202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067202).length < 2 ^ (prefixWord ++ tailWord_1067202).sum := by decide
  have hdescent : baseEnd_1067202 < baseStart_1067202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067210 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_1067210 : Nat := 118140960795 + 1067210 * 2 ^ 59
def prefixEnd_1067210 : Nat := 4983230072969 + 3 ^ 40 * 1067210 * 2
def baseEnd_1067210 : Nat := 243551861904388786518665

theorem tailTrace_1067210 : CollatzResearch.WordTrace tailWord_1067210 prefixEnd_1067210 243551861904388786518665 := by
  unfold tailWord_1067210
  simp only [CollatzResearch.WordTrace]
  refine ⟨9731086615921977450563771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25949564309125273201503389 9731086615921977450563771)
  ·
    refine ⟨14596629923882966175845657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9731086615921977450563771 14596629923882966175845657)
    ·
      refine ⟨10947472442912224631884243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14596629923882966175845657 10947472442912224631884243)
      ·
        refine ⟨16421208664368336947826365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10947472442912224631884243 16421208664368336947826365)
        ·
          refine ⟨6157953249138126355434887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16421208664368336947826365 6157953249138126355434887)
          ·
            refine ⟨9236929873707189533152331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6157953249138126355434887 9236929873707189533152331)
            ·
              refine ⟨13855394810560784299728497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9236929873707189533152331 13855394810560784299728497)
              ·
                refine ⟨10391546107920588224796373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13855394810560784299728497 10391546107920588224796373)
                ·
                  refine ⟨243551861904388786518665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10391546107920588224796373 243551861904388786518665)
                  ·
                    rfl

theorem cell21_1067210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_1067210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067210 prefixEnd_1067210 := by exact prefixLift 1067210
  have htrace : WordTrace (prefixWord ++ tailWord_1067210) baseStart_1067210 baseEnd_1067210 := by
    simpa [prefixWord, tailWord_1067210, baseEnd_1067210] using wordTrace_append hprefix tailTrace_1067210
  have hstable : (prefixWord ++ tailWord_1067210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067210).length < 2 ^ (prefixWord ++ tailWord_1067210).sum := by decide
  have hdescent : baseEnd_1067210 < baseStart_1067210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067272 : List Nat := [2, 1, 3, 2, 3, 3, 7]
def baseStart_1067272 : Nat := 118140960795 + 1067272 * 2 ^ 59
def prefixEnd_1067272 : Nat := 4983230072969 + 3 ^ 40 * 1067272 * 2
def baseEnd_1067272 : Nat := 27062890127676717387245

theorem tailTrace_1067272 : CollatzResearch.WordTrace tailWord_1067272 prefixEnd_1067272 27062890127676717387245 := by
  unfold tailWord_1067272
  simp only [CollatzResearch.WordTrace]
  refine ⟨19463303894731647195506035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25951071859642196260674713 19463303894731647195506035)
  ·
    refine ⟨29194955842097470793259053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19463303894731647195506035 29194955842097470793259053)
    ·
      refine ⟨10948108440786551547472145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29194955842097470793259053 10948108440786551547472145)
      ·
        refine ⟨8211081330589913660604109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10948108440786551547472145 8211081330589913660604109)
        ·
          refine ⟨3079155498971217622726541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8211081330589913660604109 3079155498971217622726541)
          ·
            refine ⟨1154683312114206608522453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3079155498971217622726541 1154683312114206608522453)
            ·
              refine ⟨27062890127676717387245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1154683312114206608522453 27062890127676717387245)
              ·
                rfl

theorem cell21_1067272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 7].length) (baseStart_1067272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067272 prefixEnd_1067272 := by exact prefixLift 1067272
  have htrace : WordTrace (prefixWord ++ tailWord_1067272) baseStart_1067272 baseEnd_1067272 := by
    simpa [prefixWord, tailWord_1067272, baseEnd_1067272] using wordTrace_append hprefix tailTrace_1067272
  have hstable : (prefixWord ++ tailWord_1067272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067272).length < 2 ^ (prefixWord ++ tailWord_1067272).sum := by decide
  have hdescent : baseEnd_1067272 < baseStart_1067272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067348 : List Nat := [2, 4, 1, 1, 2, 2, 3, 6]
def baseStart_1067348 : Nat := 118140960795 + 1067348 * 2 ^ 59
def prefixEnd_1067348 : Nat := 4983230072969 + 3 ^ 40 * 1067348 * 2
def baseEnd_1067348 : Nat := 81194451794843737739461

theorem tailTrace_1067348 : CollatzResearch.WordTrace tailWord_1067348 prefixEnd_1067348 81194451794843737739461 := by
  unfold tailWord_1067348
  simp only [CollatzResearch.WordTrace]
  refine ⟨19464689868593979685389349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25952919824791972913852465 19464689868593979685389349)
  ·
    refine ⟨3649629350361371191010503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19464689868593979685389349 3649629350361371191010503)
    ·
      refine ⟨5474444025542056786515755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3649629350361371191010503 5474444025542056786515755)
      ·
        refine ⟨8211666038313085179773633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5474444025542056786515755 8211666038313085179773633)
        ·
          refine ⟨6158749528734813884830225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8211666038313085179773633 6158749528734813884830225)
          ·
            refine ⟨4619062146551110413622669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6158749528734813884830225 4619062146551110413622669)
            ·
              refine ⟨1732148304956666405108501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4619062146551110413622669 1732148304956666405108501)
              ·
                refine ⟨81194451794843737739461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1732148304956666405108501 81194451794843737739461)
                ·
                  rfl

theorem cell21_1067348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_1067348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067348 prefixEnd_1067348 := by exact prefixLift 1067348
  have htrace : WordTrace (prefixWord ++ tailWord_1067348) baseStart_1067348 baseEnd_1067348 := by
    simpa [prefixWord, tailWord_1067348, baseEnd_1067348] using wordTrace_append hprefix tailTrace_1067348
  have hstable : (prefixWord ++ tailWord_1067348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067348).length < 2 ^ (prefixWord ++ tailWord_1067348).sum := by decide
  have hdescent : baseEnd_1067348 < baseStart_1067348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067424 : List Nat := [2, 1, 1, 4, 1, 3, 4, 5]
def baseStart_1067424 : Nat := 118140960795 + 1067424 * 2 ^ 59
def prefixEnd_1067424 : Nat := 4983230072969 + 3 ^ 40 * 1067424 * 2
def baseEnd_1067424 : Nat := 81200233206657323317187

theorem tailTrace_1067424 : CollatzResearch.WordTrace tailWord_1067424 prefixEnd_1067424 81200233206657323317187 := by
  unfold tailWord_1067424
  simp only [CollatzResearch.WordTrace]
  refine ⟨19466075842456312175272663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25954767789941749567030217 19466075842456312175272663)
  ·
    refine ⟨29199113763684468262908995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19466075842456312175272663 29199113763684468262908995)
    ·
      refine ⟨43798670645526702394363493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29199113763684468262908995 43798670645526702394363493)
      ·
        refine ⟨8212250746036256698943155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43798670645526702394363493 8212250746036256698943155)
        ·
          refine ⟨12318376119054385048414733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8212250746036256698943155 12318376119054385048414733)
          ·
            refine ⟨4619391044645394393155525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12318376119054385048414733 4619391044645394393155525)
            ·
              refine ⟨866135820871011448716661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4619391044645394393155525 866135820871011448716661)
              ·
                refine ⟨81200233206657323317187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 866135820871011448716661 81200233206657323317187)
                ·
                  rfl

theorem cell21_1067424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 5].length) (baseStart_1067424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067424 prefixEnd_1067424 := by exact prefixLift 1067424
  have htrace : WordTrace (prefixWord ++ tailWord_1067424) baseStart_1067424 baseEnd_1067424 := by
    simpa [prefixWord, tailWord_1067424, baseEnd_1067424] using wordTrace_append hprefix tailTrace_1067424
  have hstable : (prefixWord ++ tailWord_1067424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067424).length < 2 ^ (prefixWord ++ tailWord_1067424).sum := by decide
  have hdescent : baseEnd_1067424 < baseStart_1067424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067497 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 9]
def baseStart_1067497 : Nat := 118140960795 + 1067497 * 2 ^ 59
def prefixEnd_1067497 : Nat := 4983230072969 + 3 ^ 40 * 1067497 * 2
def baseEnd_1067497 : Nat := 243617359214540065234745

theorem tailTrace_1067497 : CollatzResearch.WordTrace tailWord_1067497 prefixEnd_1067497 243617359214540065234745 := by
  unfold tailWord_1067497
  simp only [CollatzResearch.WordTrace]
  refine ⟨38934814213648157817952745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25956542809098771878635163 38934814213648157817952745)
  ·
    refine ⟨29201110660236118363464559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38934814213648157817952745 29201110660236118363464559)
    ·
      refine ⟨43801665990354177545196839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29201110660236118363464559 43801665990354177545196839)
      ·
        refine ⟨65702498985531266317795259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43801665990354177545196839 65702498985531266317795259)
        ·
          refine ⟨98553748478296899476692889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65702498985531266317795259 98553748478296899476692889)
          ·
            refine ⟨73915311358722674607519667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98553748478296899476692889 73915311358722674607519667)
            ·
              refine ⟨110872967038084011911279501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73915311358722674607519667 110872967038084011911279501)
              ·
                refine ⟨41577362639281504466729813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110872967038084011911279501 41577362639281504466729813)
                ·
                  refine ⟨243617359214540065234745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41577362639281504466729813 243617359214540065234745)
                  ·
                    rfl

theorem cell21_1067497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_1067497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067497 prefixEnd_1067497 := by exact prefixLift 1067497
  have htrace : WordTrace (prefixWord ++ tailWord_1067497) baseStart_1067497 baseEnd_1067497 := by
    simpa [prefixWord, tailWord_1067497, baseEnd_1067497] using wordTrace_append hprefix tailTrace_1067497
  have hstable : (prefixWord ++ tailWord_1067497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067497).length < 2 ^ (prefixWord ++ tailWord_1067497).sum := by decide
  have hdescent : baseEnd_1067497 < baseStart_1067497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067506 : List Nat := [3, 2, 1, 4, 2, 2, 2, 2, 3]
def baseStart_1067506 : Nat := 118140960795 + 1067506 * 2 ^ 59
def prefixEnd_1067506 : Nat := 4983230072969 + 3 ^ 40 * 1067506 * 2
def baseEnd_1067506 : Nat := 243619413137158049584727

theorem tailTrace_1067506 : CollatzResearch.WordTrace tailWord_1067506 prefixEnd_1067506 243619413137158049584727 := by
  unfold tailWord_1067506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9733785617653888088757593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25956761647077034903353581 9733785617653888088757593)
  ·
    refine ⟨7300339213240416066568195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9733785617653888088757593 7300339213240416066568195)
    ·
      refine ⟨10950508819860624099852293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7300339213240416066568195 10950508819860624099852293)
      ·
        refine ⟨2053220403723867018722305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10950508819860624099852293 2053220403723867018722305)
        ·
          refine ⟨1539915302792900264041729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2053220403723867018722305 1539915302792900264041729)
          ·
            refine ⟨1154936477094675198031297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1539915302792900264041729 1154936477094675198031297)
            ·
              refine ⟨866202357821006398523473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1154936477094675198031297 866202357821006398523473)
              ·
                refine ⟨649651768365754798892605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 866202357821006398523473 649651768365754798892605)
                ·
                  refine ⟨243619413137158049584727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649651768365754798892605 243619413137158049584727)
                  ·
                    rfl

theorem cell21_1067506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_1067506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067506 prefixEnd_1067506 := by exact prefixLift 1067506
  have htrace : WordTrace (prefixWord ++ tailWord_1067506) baseStart_1067506 baseEnd_1067506 := by
    simpa [prefixWord, tailWord_1067506, baseEnd_1067506] using wordTrace_append hprefix tailTrace_1067506
  have hstable : (prefixWord ++ tailWord_1067506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067506).length < 2 ^ (prefixWord ++ tailWord_1067506).sum := by decide
  have hdescent : baseEnd_1067506 < baseStart_1067506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067528 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 8]
def baseStart_1067528 : Nat := 118140960795 + 1067528 * 2 ^ 59
def prefixEnd_1067528 : Nat := 4983230072969 + 3 ^ 40 * 1067528 * 2
def baseEnd_1067528 : Nat := 243624433836890900218015

theorem tailTrace_1067528 : CollatzResearch.WordTrace tailWord_1067528 prefixEnd_1067528 243624433836890900218015 := by
  unfold tailWord_1067528
  simp only [CollatzResearch.WordTrace]
  refine ⟨19467972438267925056165619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25957296584357233408220825 19467972438267925056165619)
  ·
    refine ⟨29201958657401887584248429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19467972438267925056165619 29201958657401887584248429)
    ·
      refine ⟨10950734496525707844093161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29201958657401887584248429 10950734496525707844093161)
      ·
        refine ⟨8213050872394280883069871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10950734496525707844093161 8213050872394280883069871)
        ·
          refine ⟨12319576308591421324604807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8213050872394280883069871 12319576308591421324604807)
          ·
            refine ⟨18479364462887131986907211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12319576308591421324604807 18479364462887131986907211)
            ·
              refine ⟨27719046694330697980360817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18479364462887131986907211 27719046694330697980360817)
              ·
                refine ⟨20789285020748023485270613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27719046694330697980360817 20789285020748023485270613)
                ·
                  refine ⟨243624433836890900218015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20789285020748023485270613 243624433836890900218015)
                  ·
                    rfl

theorem cell21_1067528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_1067528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067528 prefixEnd_1067528 := by exact prefixLift 1067528
  have htrace : WordTrace (prefixWord ++ tailWord_1067528) baseStart_1067528 baseEnd_1067528 := by
    simpa [prefixWord, tailWord_1067528, baseEnd_1067528] using wordTrace_append hprefix tailTrace_1067528
  have hstable : (prefixWord ++ tailWord_1067528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067528).length < 2 ^ (prefixWord ++ tailWord_1067528).sum := by decide
  have hdescent : baseEnd_1067528 < baseStart_1067528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067548 : List Nat := [2, 2, 3, 1, 2, 3, 2, 3, 3]
def baseStart_1067548 : Nat := 118140960795 + 1067548 * 2 ^ 59
def prefixEnd_1067548 : Nat := 4983230072969 + 3 ^ 40 * 1067548 * 2
def baseEnd_1067548 : Nat := 243628998109375309884641

theorem tailTrace_1067548 : CollatzResearch.WordTrace tailWord_1067548 prefixEnd_1067548 243628998109375309884641 := by
  unfold tailWord_1067548
  simp only [CollatzResearch.WordTrace]
  refine ⟨19468337168231696764029649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25957782890975595685372865 19468337168231696764029649)
  ·
    refine ⟨14601252876173772573022237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19468337168231696764029649 14601252876173772573022237)
    ·
      refine ⟨5475469828565164714883339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14601252876173772573022237 5475469828565164714883339)
      ·
        refine ⟨8213204742847747072325009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5475469828565164714883339 8213204742847747072325009)
        ·
          refine ⟨6159903557135810304243757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8213204742847747072325009 6159903557135810304243757)
          ·
            refine ⟨2309963833925928864091409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6159903557135810304243757 2309963833925928864091409)
            ·
              refine ⟨1732472875444446648068557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2309963833925928864091409 1732472875444446648068557)
              ·
                refine ⟨649677328291667493025709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1732472875444446648068557 649677328291667493025709)
                ·
                  refine ⟨243628998109375309884641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649677328291667493025709 243628998109375309884641)
                  ·
                    rfl

theorem cell21_1067548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_1067548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067548 prefixEnd_1067548 := by exact prefixLift 1067548
  have htrace : WordTrace (prefixWord ++ tailWord_1067548) baseStart_1067548 baseEnd_1067548 := by
    simpa [prefixWord, tailWord_1067548, baseEnd_1067548] using wordTrace_append hprefix tailTrace_1067548
  have hstable : (prefixWord ++ tailWord_1067548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067548).length < 2 ^ (prefixWord ++ tailWord_1067548).sum := by decide
  have hdescent : baseEnd_1067548 < baseStart_1067548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067562 : List Nat := [3, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_1067562 : Nat := 118140960795 + 1067562 * 2 ^ 59
def prefixEnd_1067562 : Nat := 4983230072969 + 3 ^ 40 * 1067562 * 2
def baseEnd_1067562 : Nat := 243632193100114396651279

theorem tailTrace_1067562 : CollatzResearch.WordTrace tailWord_1067562 prefixEnd_1067562 243632193100114396651279 := by
  unfold tailWord_1067562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9734296239603168479767235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25958123305608449279379293 9734296239603168479767235)
  ·
    refine ⟨14601444359404752719650853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9734296239603168479767235 14601444359404752719650853)
    ·
      refine ⟨2737770817388391134934535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14601444359404752719650853 2737770817388391134934535)
      ·
        refine ⟨4106656226082586702401803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2737770817388391134934535 4106656226082586702401803)
        ·
          refine ⟨6159984339123880053602705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4106656226082586702401803 6159984339123880053602705)
          ·
            refine ⟨4619988254342910040202029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6159984339123880053602705 4619988254342910040202029)
            ·
              refine ⟨1732495595378591265075761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4619988254342910040202029 1732495595378591265075761)
              ·
                refine ⟨1299371696533943448806821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1732495595378591265075761 1299371696533943448806821)
                ·
                  refine ⟨243632193100114396651279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1299371696533943448806821 243632193100114396651279)
                  ·
                    rfl

theorem cell21_1067562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_1067562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067562 prefixEnd_1067562 := by exact prefixLift 1067562
  have htrace : WordTrace (prefixWord ++ tailWord_1067562) baseStart_1067562 baseEnd_1067562 := by
    simpa [prefixWord, tailWord_1067562, baseEnd_1067562] using wordTrace_append hprefix tailTrace_1067562
  have hstable : (prefixWord ++ tailWord_1067562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067562).length < 2 ^ (prefixWord ++ tailWord_1067562).sum := by decide
  have hdescent : baseEnd_1067562 < baseStart_1067562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067624 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 5]
def baseStart_1067624 : Nat := 118140960795 + 1067624 * 2 ^ 59
def prefixEnd_1067624 : Nat := 4983230072969 + 3 ^ 40 * 1067624 * 2
def baseEnd_1067624 : Nat := 243646342344816066617819

theorem tailTrace_1067624 : CollatzResearch.WordTrace tailWord_1067624 prefixEnd_1067624 243646342344816066617819 := by
  unfold tailWord_1067624
  simp only [CollatzResearch.WordTrace]
  refine ⟨19469723142094029253912963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25959630856125372338550617 19469723142094029253912963)
  ·
    refine ⟨29204584713141043880869445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19469723142094029253912963 29204584713141043880869445)
    ·
      refine ⟨5475859633713945727663021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29204584713141043880869445 5475859633713945727663021)
      ·
        refine ⟨2053447362642729647873633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5475859633713945727663021 2053447362642729647873633)
        ·
          refine ⟨1540085521982047235905225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2053447362642729647873633 1540085521982047235905225)
          ·
            refine ⟨1155064141486535426928919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1540085521982047235905225 1155064141486535426928919)
            ·
              refine ⟨1732596212229803140393379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155064141486535426928919 1732596212229803140393379)
              ·
                refine ⟨2598894318344704710590069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1732596212229803140393379 2598894318344704710590069)
                ·
                  refine ⟨243646342344816066617819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2598894318344704710590069 243646342344816066617819)
                  ·
                    rfl

theorem cell21_1067624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_1067624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067624 prefixEnd_1067624 := by exact prefixLift 1067624
  have htrace : WordTrace (prefixWord ++ tailWord_1067624) baseStart_1067624 baseEnd_1067624 := by
    simpa [prefixWord, tailWord_1067624, baseEnd_1067624] using wordTrace_append hprefix tailTrace_1067624
  have hstable : (prefixWord ++ tailWord_1067624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067624).length < 2 ^ (prefixWord ++ tailWord_1067624).sum := by decide
  have hdescent : baseEnd_1067624 < baseStart_1067624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067801 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 5]
def baseStart_1067801 : Nat := 118140960795 + 1067801 * 2 ^ 59
def prefixEnd_1067801 : Nat := 4983230072969 + 3 ^ 40 * 1067801 * 2
def baseEnd_1067801 : Nat := 243686736156303092167457

theorem tailTrace_1067801 : CollatzResearch.WordTrace tailWord_1067801 prefixEnd_1067801 243686736156303092167457 := by
  unfold tailWord_1067801
  simp only [CollatzResearch.WordTrace]
  refine ⟨38945902004546817737019257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25963934669697878491346171 38945902004546817737019257)
  ·
    refine ⟨29209426503410113302764443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38945902004546817737019257 29209426503410113302764443)
    ·
      refine ⟨43814139755115169954146665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29209426503410113302764443 43814139755115169954146665)
      ·
        refine ⟨32860604816336377465609999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43814139755115169954146665 32860604816336377465609999)
        ·
          refine ⟨49290907224504566198414999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32860604816336377465609999 49290907224504566198414999)
          ·
            refine ⟨73936360836756849297622499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49290907224504566198414999 73936360836756849297622499)
            ·
              refine ⟨110904541255135273946433749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73936360836756849297622499 110904541255135273946433749)
              ·
                refine ⟨2599325185667232983119541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 110904541255135273946433749 2599325185667232983119541)
                ·
                  refine ⟨243686736156303092167457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2599325185667232983119541 243686736156303092167457)
                  ·
                    rfl

theorem cell21_1067801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_1067801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067801 prefixEnd_1067801 := by exact prefixLift 1067801
  have htrace : WordTrace (prefixWord ++ tailWord_1067801) baseStart_1067801 baseEnd_1067801 := by
    simpa [prefixWord, tailWord_1067801, baseEnd_1067801] using wordTrace_append hprefix tailTrace_1067801
  have hstable : (prefixWord ++ tailWord_1067801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067801).length < 2 ^ (prefixWord ++ tailWord_1067801).sum := by decide
  have hdescent : baseEnd_1067801 < baseStart_1067801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067849 : List Nat := [1, 2, 1, 1, 2, 6, 2, 2, 4]
def baseStart_1067849 : Nat := 118140960795 + 1067849 * 2 ^ 59
def prefixEnd_1067849 : Nat := 4983230072969 + 3 ^ 40 * 1067849 * 2
def baseEnd_1067849 : Nat := 243697690410265675367359

theorem tailTrace_1067849 : CollatzResearch.WordTrace tailWord_1067849 prefixEnd_1067849 243697690410265675367359 := by
  unfold tailWord_1067849
  simp only [CollatzResearch.WordTrace]
  refine ⟨38947652708372921934766601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25965101805581947956511067 38947652708372921934766601)
  ·
    refine ⟨29210739531279691451074951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38947652708372921934766601 29210739531279691451074951)
    ·
      refine ⟨43816109296919537176612427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29210739531279691451074951 43816109296919537176612427)
      ·
        refine ⟨65724163945379305764918641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43816109296919537176612427 65724163945379305764918641)
        ·
          refine ⟨49293122959034479323688981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65724163945379305764918641 49293122959034479323688981)
          ·
            refine ⟨2310615138704741218297921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49293122959034479323688981 2310615138704741218297921)
            ·
              refine ⟨1732961354028555913723441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2310615138704741218297921 1732961354028555913723441)
              ·
                refine ⟨1299721015521416935292581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1732961354028555913723441 1299721015521416935292581)
                ·
                  refine ⟨243697690410265675367359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1299721015521416935292581 243697690410265675367359)
                  ·
                    rfl

theorem cell21_1067849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_1067849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067849 prefixEnd_1067849 := by exact prefixLift 1067849
  have htrace : WordTrace (prefixWord ++ tailWord_1067849) baseStart_1067849 baseEnd_1067849 := by
    simpa [prefixWord, tailWord_1067849, baseEnd_1067849] using wordTrace_append hprefix tailTrace_1067849
  have hstable : (prefixWord ++ tailWord_1067849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067849).length < 2 ^ (prefixWord ++ tailWord_1067849).sum := by decide
  have hdescent : baseEnd_1067849 < baseStart_1067849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067852 : List Nat := [2, 2, 1, 3, 3, 1, 4, 2, 3]
def baseStart_1067852 : Nat := 118140960795 + 1067852 * 2 ^ 59
def prefixEnd_1067852 : Nat := 4983230072969 + 3 ^ 40 * 1067852 * 2
def baseEnd_1067852 : Nat := 243698375051138336817353

theorem tailTrace_1067852 : CollatzResearch.WordTrace tailWord_1067852 prefixEnd_1067852 243698375051138336817353 := by
  unfold tailWord_1067852
  simp only [CollatzResearch.WordTrace]
  refine ⟨19473881063681026723562905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25965174751574702298083873 19473881063681026723562905)
  ·
    refine ⟨14605410797760770042672179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19473881063681026723562905 14605410797760770042672179)
    ·
      refine ⟨21908116196641155064008269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14605410797760770042672179 21908116196641155064008269)
      ·
        refine ⟨8215543573740433149003101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21908116196641155064008269 8215543573740433149003101)
        ·
          refine ⟨3080828840152662430876163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8215543573740433149003101 3080828840152662430876163)
          ·
            refine ⟨4621243260228993646314245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3080828840152662430876163 4621243260228993646314245)
            ·
              refine ⟨866483111292936308683921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4621243260228993646314245 866483111292936308683921)
              ·
                refine ⟨649862333469702231512941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 866483111292936308683921 649862333469702231512941)
                ·
                  refine ⟨243698375051138336817353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649862333469702231512941 243698375051138336817353)
                  ·
                    rfl

theorem cell21_1067852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_1067852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067852 prefixEnd_1067852 := by exact prefixLift 1067852
  have htrace : WordTrace (prefixWord ++ tailWord_1067852) baseStart_1067852 baseEnd_1067852 := by
    simpa [prefixWord, tailWord_1067852, baseEnd_1067852] using wordTrace_append hprefix tailTrace_1067852
  have hstable : (prefixWord ++ tailWord_1067852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067852).length < 2 ^ (prefixWord ++ tailWord_1067852).sum := by decide
  have hdescent : baseEnd_1067852 < baseStart_1067852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067863 : List Nat := [1, 1, 3, 2, 4, 1, 3, 6]
def baseStart_1067863 : Nat := 118140960795 + 1067863 * 2 ^ 59
def prefixEnd_1067863 : Nat := 4983230072969 + 3 ^ 40 * 1067863 * 2
def baseEnd_1067863 : Nat := 81233628467001587377999

theorem tailTrace_1067863 : CollatzResearch.WordTrace tailWord_1067863 prefixEnd_1067863 81233628467001587377999 := by
  unfold tailWord_1067863
  simp only [CollatzResearch.WordTrace]
  refine ⟨38948163330322202325776243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25965442220214801550517495 38948163330322202325776243)
  ·
    refine ⟨58422244995483303488664365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38948163330322202325776243 58422244995483303488664365)
    ·
      refine ⟨21908341873306238808249137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58422244995483303488664365 21908341873306238808249137)
      ·
        refine ⟨16431256404979679106186853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21908341873306238808249137 16431256404979679106186853)
        ·
          refine ⟨3080860575933689832410035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16431256404979679106186853 3080860575933689832410035)
          ·
            refine ⟨4621290863900534748615053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3080860575933689832410035 4621290863900534748615053)
            ·
              refine ⟨1732984073962700530730645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4621290863900534748615053 1732984073962700530730645)
              ·
                refine ⟨81233628467001587377999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1732984073962700530730645 81233628467001587377999)
                ·
                  rfl

theorem cell21_1067863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 6].length) (baseStart_1067863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067863 prefixEnd_1067863 := by exact prefixLift 1067863
  have htrace : WordTrace (prefixWord ++ tailWord_1067863) baseStart_1067863 baseEnd_1067863 := by
    simpa [prefixWord, tailWord_1067863, baseEnd_1067863] using wordTrace_append hprefix tailTrace_1067863
  have hstable : (prefixWord ++ tailWord_1067863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067863).length < 2 ^ (prefixWord ++ tailWord_1067863).sum := by decide
  have hdescent : baseEnd_1067863 < baseStart_1067863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067877 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 7]
def baseStart_1067877 : Nat := 118140960795 + 1067877 * 2 ^ 59
def prefixEnd_1067877 : Nat := 4983230072969 + 3 ^ 40 * 1067877 * 2
def baseEnd_1067877 : Nat := 243704080391743848900635

theorem tailTrace_1067877 : CollatzResearch.WordTrace tailWord_1067877 prefixEnd_1067877 243704080391743848900635 := by
  unfold tailWord_1067877
  simp only [CollatzResearch.WordTrace]
  refine ⟨38948673952271482716785885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25965782634847655144523923 38948673952271482716785885)
  ·
    refine ⟨14605752732101806018794707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38948673952271482716785885 14605752732101806018794707)
    ·
      refine ⟨21908629098152709028192061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14605752732101806018794707 21908629098152709028192061)
      ·
        refine ⟨8215735911807265885572023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21908629098152709028192061 8215735911807265885572023)
        ·
          refine ⟨12323603867710898828358035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8215735911807265885572023 12323603867710898828358035)
          ·
            refine ⟨18485405801566348242537053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12323603867710898828358035 18485405801566348242537053)
            ·
              refine ⟨6932027175587380590951395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18485405801566348242537053 6932027175587380590951395)
              ·
                refine ⟨10398040763381070886427093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6932027175587380590951395 10398040763381070886427093)
                ·
                  refine ⟨243704080391743848900635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10398040763381070886427093 243704080391743848900635)
                  ·
                    rfl

theorem cell21_1067877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_1067877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067877 prefixEnd_1067877 := by exact prefixLift 1067877
  have htrace : WordTrace (prefixWord ++ tailWord_1067877) baseStart_1067877 baseEnd_1067877 := by
    simpa [prefixWord, tailWord_1067877, baseEnd_1067877] using wordTrace_append hprefix tailTrace_1067877
  have hstable : (prefixWord ++ tailWord_1067877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067877).length < 2 ^ (prefixWord ++ tailWord_1067877).sum := by decide
  have hdescent : baseEnd_1067877 < baseStart_1067877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067880 : List Nat := [2, 1, 4, 2, 1, 3, 3, 5]
def baseStart_1067880 : Nat := 118140960795 + 1067880 * 2 ^ 59
def prefixEnd_1067880 : Nat := 4983230072969 + 3 ^ 40 * 1067880 * 2
def baseEnd_1067880 : Nat := 81234921677538836783543

theorem tailTrace_1067880 : CollatzResearch.WordTrace tailWord_1067880 prefixEnd_1067880 81234921677538836783543 := by
  unfold tailWord_1067880
  simp only [CollatzResearch.WordTrace]
  refine ⟨19474391685630307114572547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25965855580840409486096729 19474391685630307114572547)
  ·
    refine ⟨29211587528445460671858821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19474391685630307114572547 29211587528445460671858821)
    ·
      refine ⟨5477172661583523875973529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29211587528445460671858821 5477172661583523875973529)
      ·
        refine ⟨4107879496187642906980147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5477172661583523875973529 4107879496187642906980147)
        ·
          refine ⟨6161819244281464360470221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4107879496187642906980147 6161819244281464360470221)
          ·
            refine ⟨2310682216605549135176333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6161819244281464360470221 2310682216605549135176333)
            ·
              refine ⟨866505831227080925691125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2310682216605549135176333 866505831227080925691125)
              ·
                refine ⟨81234921677538836783543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 866505831227080925691125 81234921677538836783543)
                ·
                  rfl

theorem cell21_1067880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 5].length) (baseStart_1067880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067880 prefixEnd_1067880 := by exact prefixLift 1067880
  have htrace : WordTrace (prefixWord ++ tailWord_1067880) baseStart_1067880 baseEnd_1067880 := by
    simpa [prefixWord, tailWord_1067880, baseEnd_1067880] using wordTrace_append hprefix tailTrace_1067880
  have hstable : (prefixWord ++ tailWord_1067880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067880).length < 2 ^ (prefixWord ++ tailWord_1067880).sum := by decide
  have hdescent : baseEnd_1067880 < baseStart_1067880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067911 : List Nat := [1, 1, 4, 2, 3, 1, 2, 4, 3]
def baseStart_1067911 : Nat := 118140960795 + 1067911 * 2 ^ 59
def prefixEnd_1067911 : Nat := 4983230072969 + 3 ^ 40 * 1067911 * 2
def baseEnd_1067911 : Nat := 243711839654967345333899

theorem tailTrace_1067911 : CollatzResearch.WordTrace tailWord_1067911 prefixEnd_1067911 243711839654967345333899 := by
  unfold tailWord_1067911
  simp only [CollatzResearch.WordTrace]
  refine ⟨38949914034148306523523587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25966609356098871015682391 38949914034148306523523587)
  ·
    refine ⟨58424871051222459785285381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38949914034148306523523587 58424871051222459785285381)
    ·
      refine ⟨10954663322104211209741009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58424871051222459785285381 10954663322104211209741009)
      ·
        refine ⟨8215997491578158407305757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10954663322104211209741009 8215997491578158407305757)
        ·
          refine ⟨3080999059341809402739659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8215997491578158407305757 3080999059341809402739659)
          ·
            refine ⟨4621498589012714104109489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3080999059341809402739659 4621498589012714104109489)
            ·
              refine ⟨3466123941759535578082117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4621498589012714104109489 3466123941759535578082117)
              ·
                refine ⟨649898239079912920890397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3466123941759535578082117 649898239079912920890397)
                ·
                  refine ⟨243711839654967345333899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649898239079912920890397 243711839654967345333899)
                  ·
                    rfl

theorem cell21_1067911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 3].length) (baseStart_1067911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067911 prefixEnd_1067911 := by exact prefixLift 1067911
  have htrace : WordTrace (prefixWord ++ tailWord_1067911) baseStart_1067911 baseEnd_1067911 := by
    simpa [prefixWord, tailWord_1067911, baseEnd_1067911] using wordTrace_append hprefix tailTrace_1067911
  have hstable : (prefixWord ++ tailWord_1067911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067911).length < 2 ^ (prefixWord ++ tailWord_1067911).sum := by decide
  have hdescent : baseEnd_1067911 < baseStart_1067911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067939 : List Nat := [1, 1, 1, 4, 1, 2, 6, 5]
def baseStart_1067939 : Nat := 118140960795 + 1067939 * 2 ^ 59
def prefixEnd_1067939 : Nat := 4983230072969 + 3 ^ 40 * 1067939 * 2
def baseEnd_1067939 : Nat := 81239409878815172955725

theorem tailTrace_1067939 : CollatzResearch.WordTrace tailWord_1067939 prefixEnd_1067939 81239409878815172955725 := by
  unfold tailWord_1067939
  simp only [CollatzResearch.WordTrace]
  refine ⟨38950935278046867305542871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25967290185364578203695247 38950935278046867305542871)
  ·
    refine ⟨58426402917070300958314307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38950935278046867305542871 58426402917070300958314307)
    ·
      refine ⟨87639604375605451437471461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58426402917070300958314307 87639604375605451437471461)
      ·
        refine ⟨16432425820426022144525899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87639604375605451437471461 16432425820426022144525899)
        ·
          refine ⟨24648638730639033216788849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16432425820426022144525899 24648638730639033216788849)
          ·
            refine ⟨18486479047979274912591637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24648638730639033216788849 18486479047979274912591637)
            ·
              refine ⟨866553705374028511527733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18486479047979274912591637 866553705374028511527733)
              ·
                refine ⟨81239409878815172955725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 866553705374028511527733 81239409878815172955725)
                ·
                  rfl

theorem cell21_1067939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 5].length) (baseStart_1067939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067939 prefixEnd_1067939 := by exact prefixLift 1067939
  have htrace : WordTrace (prefixWord ++ tailWord_1067939) baseStart_1067939 baseEnd_1067939 := by
    simpa [prefixWord, tailWord_1067939, baseEnd_1067939] using wordTrace_append hprefix tailTrace_1067939
  have hstable : (prefixWord ++ tailWord_1067939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067939).length < 2 ^ (prefixWord ++ tailWord_1067939).sum := by decide
  have hdescent : baseEnd_1067939 < baseStart_1067939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067956 : List Nat := [2, 5, 2, 1, 1, 1, 9]
def baseStart_1067956 : Nat := 118140960795 + 1067956 * 2 ^ 59
def prefixEnd_1067956 : Nat := 4983230072969 + 3 ^ 40 * 1067956 * 2
def baseEnd_1067956 : Nat := 27080234363117474120423

theorem tailTrace_1067956 : CollatzResearch.WordTrace tailWord_1067956 prefixEnd_1067956 27080234363117474120423 := by
  unfold tailWord_1067956
  simp only [CollatzResearch.WordTrace]
  refine ⟨19475777659492639604455861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25967703545990186139274481 19475777659492639604455861)
  ·
    refine ⟨1825854155577434962917737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19475777659492639604455861 1825854155577434962917737)
    ·
      refine ⟨1369390616683076222188303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1825854155577434962917737 1369390616683076222188303)
      ·
        refine ⟨2054085925024614333282455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1369390616683076222188303 2054085925024614333282455)
        ·
          refine ⟨3081128887536921499923683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2054085925024614333282455 3081128887536921499923683)
          ·
            refine ⟨4621693331305382249885525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3081128887536921499923683 4621693331305382249885525)
            ·
              refine ⟨27080234363117474120423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4621693331305382249885525 27080234363117474120423)
              ·
                rfl

theorem cell21_1067956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 9].length) (baseStart_1067956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1067956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1067956 prefixEnd_1067956 := by exact prefixLift 1067956
  have htrace : WordTrace (prefixWord ++ tailWord_1067956) baseStart_1067956 baseEnd_1067956 := by
    simpa [prefixWord, tailWord_1067956, baseEnd_1067956] using wordTrace_append hprefix tailTrace_1067956
  have hstable : (prefixWord ++ tailWord_1067956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067956).length < 2 ^ (prefixWord ++ tailWord_1067956).sum := by decide
  have hdescent : baseEnd_1067956 < baseStart_1067956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068021 : List Nat := [1, 3, 5, 2, 1, 1, 1, 4, 3]
def baseStart_1068021 : Nat := 118140960795 + 1068021 * 2 ^ 59
def prefixEnd_1068021 : Nat := 4983230072969 + 3 ^ 40 * 1068021 * 2
def baseEnd_1068021 : Nat := 243736943153631598500341

theorem tailTrace_1068021 : CollatzResearch.WordTrace tailWord_1068021 prefixEnd_1068021 243736943153631598500341 := by
  unfold tailWord_1068021
  simp only [CollatzResearch.WordTrace]
  refine ⟨38953926063749795310027917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25969284042499863540018611 38953926063749795310027917)
  ·
    refine ⟨14607722273906173241260469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38953926063749795310027917 14607722273906173241260469)
    ·
      refine ⟨1369473963178703741368169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14607722273906173241260469 1369473963178703741368169)
      ·
        refine ⟨1027105472384027806026127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1369473963178703741368169 1027105472384027806026127)
        ·
          refine ⟨1540658208576041709039191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027105472384027806026127 1540658208576041709039191)
          ·
            refine ⟨2310987312864062563558787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540658208576041709039191 2310987312864062563558787)
            ·
              refine ⟨3466480969296093845338181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310987312864062563558787 3466480969296093845338181)
              ·
                refine ⟨649965181743017596000909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3466480969296093845338181 649965181743017596000909)
                ·
                  refine ⟨243736943153631598500341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649965181743017596000909 243736943153631598500341)
                  ·
                    rfl

theorem cell21_1068021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_1068021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068021 prefixEnd_1068021 := by exact prefixLift 1068021
  have htrace : WordTrace (prefixWord ++ tailWord_1068021) baseStart_1068021 baseEnd_1068021 := by
    simpa [prefixWord, tailWord_1068021, baseEnd_1068021] using wordTrace_append hprefix tailTrace_1068021
  have hstable : (prefixWord ++ tailWord_1068021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068021).length < 2 ^ (prefixWord ++ tailWord_1068021).sum := by decide
  have hdescent : baseEnd_1068021 < baseStart_1068021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068029 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 5]
def baseStart_1068029 : Nat := 118140960795 + 1068029 * 2 ^ 59
def prefixEnd_1068029 : Nat := 4983230072969 + 3 ^ 40 * 1068029 * 2
def baseEnd_1068029 : Nat := 243738768862625362366991

theorem tailTrace_1068029 : CollatzResearch.WordTrace tailWord_1068029 prefixEnd_1068029 243738768862625362366991 := by
  unfold tailWord_1068029
  simp only [CollatzResearch.WordTrace]
  refine ⟨38954217847720812676319141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25969478565147208450879427 38954217847720812676319141)
  ·
    refine ⟨7303915846447652376809839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38954217847720812676319141 7303915846447652376809839)
    ·
      refine ⟨10955873769671478565214759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7303915846447652376809839 10955873769671478565214759)
      ·
        refine ⟨16433810654507217847822139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10955873769671478565214759 16433810654507217847822139)
        ·
          refine ⟨24650715981760826771733209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16433810654507217847822139 24650715981760826771733209)
          ·
            refine ⟨18488036986320620078799907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24650715981760826771733209 18488036986320620078799907)
            ·
              refine ⟨27732055479480930118199861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18488036986320620078799907 27732055479480930118199861)
              ·
                refine ⟨2599880201201337198581237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27732055479480930118199861 2599880201201337198581237)
                ·
                  refine ⟨243738768862625362366991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2599880201201337198581237 243738768862625362366991)
                  ·
                    rfl

theorem cell21_1068029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_1068029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068029 prefixEnd_1068029 := by exact prefixLift 1068029
  have htrace : WordTrace (prefixWord ++ tailWord_1068029) baseStart_1068029 baseEnd_1068029 := by
    simpa [prefixWord, tailWord_1068029, baseEnd_1068029] using wordTrace_append hprefix tailTrace_1068029
  have hstable : (prefixWord ++ tailWord_1068029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068029).length < 2 ^ (prefixWord ++ tailWord_1068029).sum := by decide
  have hdescent : baseEnd_1068029 < baseStart_1068029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068046 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_1068046 : Nat := 118140960795 + 1068046 * 2 ^ 59
def prefixEnd_1068046 : Nat := 4983230072969 + 3 ^ 40 * 1068046 * 2
def baseEnd_1068046 : Nat := 243742648494237110583623

theorem tailTrace_1068046 : CollatzResearch.WordTrace tailWord_1068046 prefixEnd_1068046 243742648494237110583623 := by
  unfold tailWord_1068046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4869354736082403072460999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25969891925772816386458661 4869354736082403072460999)
  ·
    refine ⟨7304032104123604608691499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4869354736082403072460999 7304032104123604608691499)
    ·
      refine ⟨10956048156185406913037249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7304032104123604608691499 10956048156185406913037249)
      ·
        refine ⟨8217036117139055184777937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10956048156185406913037249 8217036117139055184777937)
        ·
          refine ⟨6162777087854291388583453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8217036117139055184777937 6162777087854291388583453)
          ·
            refine ⟨2311041407945359270718795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6162777087854291388583453 2311041407945359270718795)
            ·
              refine ⟨3466562111918038906078193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311041407945359270718795 3466562111918038906078193)
              ·
                refine ⟨2599921583938529179558645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3466562111918038906078193 2599921583938529179558645)
                ·
                  refine ⟨243742648494237110583623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2599921583938529179558645 243742648494237110583623)
                  ·
                    rfl

theorem cell21_1068046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_1068046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068046 prefixEnd_1068046 := by exact prefixLift 1068046
  have htrace : WordTrace (prefixWord ++ tailWord_1068046) baseStart_1068046 baseEnd_1068046 := by
    simpa [prefixWord, tailWord_1068046, baseEnd_1068046] using wordTrace_append hprefix tailTrace_1068046
  have hstable : (prefixWord ++ tailWord_1068046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068046).length < 2 ^ (prefixWord ++ tailWord_1068046).sum := by decide
  have hdescent : baseEnd_1068046 < baseStart_1068046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068063 : List Nat := [1, 1, 2, 4, 1, 4, 2, 3, 3]
def baseStart_1068063 : Nat := 118140960795 + 1068063 * 2 ^ 59
def prefixEnd_1068063 : Nat := 4983230072969 + 3 ^ 40 * 1068063 * 2
def baseEnd_1068063 : Nat := 243746528125848858800255

theorem tailTrace_1068063 : CollatzResearch.WordTrace tailWord_1068063 prefixEnd_1068063 243746528125848858800255 := by
  unfold tailWord_1068063
  simp only [CollatzResearch.WordTrace]
  refine ⟨38955457929597636483056843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25970305286398424322037895 38955457929597636483056843)
  ·
    refine ⟨58433186894396454724585265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38955457929597636483056843 58433186894396454724585265)
    ·
      refine ⟨43824890170797341043438949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58433186894396454724585265 43824890170797341043438949)
      ·
        refine ⟨8217166907024501445644803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43824890170797341043438949 8217166907024501445644803)
        ·
          refine ⟨12325750360536752168467205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8217166907024501445644803 12325750360536752168467205)
          ·
            refine ⟨2311078192600641031587601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12325750360536752168467205 2311078192600641031587601)
            ·
              refine ⟨1733308644450480773690701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2311078192600641031587601 1733308644450480773690701)
              ·
                refine ⟨649990741668930290134013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1733308644450480773690701 649990741668930290134013)
                ·
                  refine ⟨243746528125848858800255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649990741668930290134013 243746528125848858800255)
                  ·
                    rfl

theorem cell21_1068063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 3].length) (baseStart_1068063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068063 prefixEnd_1068063 := by exact prefixLift 1068063
  have htrace : WordTrace (prefixWord ++ tailWord_1068063) baseStart_1068063 baseEnd_1068063 := by
    simpa [prefixWord, tailWord_1068063, baseEnd_1068063] using wordTrace_append hprefix tailTrace_1068063
  have hstable : (prefixWord ++ tailWord_1068063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068063).length < 2 ^ (prefixWord ++ tailWord_1068063).sum := by decide
  have hdescent : baseEnd_1068063 < baseStart_1068063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068122 : List Nat := [3, 1, 1, 2, 1, 1, 2, 7, 3]
def baseStart_1068122 : Nat := 118140960795 + 1068122 * 2 ^ 59
def prefixEnd_1068122 : Nat := 4983230072969 + 3 ^ 40 * 1068122 * 2
def baseEnd_1068122 : Nat := 243759992729677867316801

theorem tailTrace_1068122 : CollatzResearch.WordTrace tailWord_1068122 prefixEnd_1068122 243759992729677867316801 := by
  unfold tailWord_1068122
  simp only [CollatzResearch.WordTrace]
  refine ⟨9739402459095972389863655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25971739890922593039636413 9739402459095972389863655)
  ·
    refine ⟨14609103688643958584795483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9739402459095972389863655 14609103688643958584795483)
    ·
      refine ⟨21913655532965937877193225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14609103688643958584795483 21913655532965937877193225)
      ·
        refine ⟨16435241649724453407894919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21913655532965937877193225 16435241649724453407894919)
        ·
          refine ⟨24652862474586680111842379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16435241649724453407894919 24652862474586680111842379)
          ·
            refine ⟨36979293711880020167763569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24652862474586680111842379 36979293711880020167763569)
            ·
              refine ⟨27734470283910015125822677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36979293711880020167763569 27734470283910015125822677)
              ·
                refine ⟨650026647279140979511469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27734470283910015125822677 650026647279140979511469)
                ·
                  refine ⟨243759992729677867316801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650026647279140979511469 243759992729677867316801)
                  ·
                    rfl

theorem cell21_1068122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_1068122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068122 prefixEnd_1068122 := by exact prefixLift 1068122
  have htrace : WordTrace (prefixWord ++ tailWord_1068122) baseStart_1068122 baseEnd_1068122 := by
    simpa [prefixWord, tailWord_1068122, baseEnd_1068122] using wordTrace_append hprefix tailTrace_1068122
  have hstable : (prefixWord ++ tailWord_1068122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068122).length < 2 ^ (prefixWord ++ tailWord_1068122).sum := by decide
  have hdescent : baseEnd_1068122 < baseStart_1068122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068125 : List Nat := [1, 4, 4, 1, 3, 1, 7]
def baseStart_1068125 : Nat := 118140960795 + 1068125 * 2 ^ 59
def prefixEnd_1068125 : Nat := 4983230072969 + 3 ^ 40 * 1068125 * 2
def baseEnd_1068125 : Nat := 27084519707838947640755

theorem tailTrace_1068125 : CollatzResearch.WordTrace tailWord_1068125 prefixEnd_1068125 27084519707838947640755 := by
  unfold tailWord_1068125
  simp only [CollatzResearch.WordTrace]
  refine ⟨38957719255373021071813829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25971812836915347381209219 38957719255373021071813829)
  ·
    refine ⟨7304572360382441450965093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38957719255373021071813829 7304572360382441450965093)
    ·
      refine ⟨1369607317571707772055955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7304572360382441450965093 1369607317571707772055955)
      ·
        refine ⟨2054410976357561658083933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1369607317571707772055955 2054410976357561658083933)
        ·
          refine ⟨770404116134085621781475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2054410976357561658083933 770404116134085621781475)
          ·
            refine ⟨1155606174201128432672213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770404116134085621781475 1155606174201128432672213)
            ·
              refine ⟨27084519707838947640755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1155606174201128432672213 27084519707838947640755)
              ·
                rfl

theorem cell21_1068125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 7].length) (baseStart_1068125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068125 prefixEnd_1068125 := by exact prefixLift 1068125
  have htrace : WordTrace (prefixWord ++ tailWord_1068125) baseStart_1068125 baseEnd_1068125 := by
    simpa [prefixWord, tailWord_1068125, baseEnd_1068125] using wordTrace_append hprefix tailTrace_1068125
  have hstable : (prefixWord ++ tailWord_1068125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068125).length < 2 ^ (prefixWord ++ tailWord_1068125).sum := by decide
  have hdescent : baseEnd_1068125 < baseStart_1068125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068153 : List Nat := [1, 2, 1, 3, 5, 1, 1, 3, 4]
def baseStart_1068153 : Nat := 118140960795 + 1068153 * 2 ^ 59
def prefixEnd_1068153 : Nat := 4983230072969 + 3 ^ 40 * 1068153 * 2
def baseEnd_1068153 : Nat := 243767067352028702300071

theorem tailTrace_1068153 : CollatzResearch.WordTrace tailWord_1068153 prefixEnd_1068153 243767067352028702300071 := by
  unfold tailWord_1068153
  simp only [CollatzResearch.WordTrace]
  refine ⟨38958740499271581853833113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25972493666181054569222075 38958740499271581853833113)
  ·
    refine ⟨29219055374453686390374835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38958740499271581853833113 29219055374453686390374835)
    ·
      refine ⟨43828583061680529585562253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29219055374453686390374835 43828583061680529585562253)
      ·
        refine ⟨16435718648130198594585845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43828583061680529585562253 16435718648130198594585845)
        ·
          refine ⟨1540848623262206118242423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16435718648130198594585845 1540848623262206118242423)
          ·
            refine ⟨2311272934893309177363635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540848623262206118242423 2311272934893309177363635)
            ·
              refine ⟨3466909402339963766045453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311272934893309177363635 3466909402339963766045453)
              ·
                refine ⟨1300091025877486412267045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3466909402339963766045453 1300091025877486412267045)
                ·
                  refine ⟨243767067352028702300071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1300091025877486412267045 243767067352028702300071)
                  ·
                    rfl

theorem cell21_1068153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_1068153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068153 prefixEnd_1068153 := by exact prefixLift 1068153
  have htrace : WordTrace (prefixWord ++ tailWord_1068153) baseStart_1068153 baseEnd_1068153 := by
    simpa [prefixWord, tailWord_1068153, baseEnd_1068153] using wordTrace_append hprefix tailTrace_1068153
  have hstable : (prefixWord ++ tailWord_1068153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068153).length < 2 ^ (prefixWord ++ tailWord_1068153).sum := by decide
  have hdescent : baseEnd_1068153 < baseStart_1068153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068195 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 6]
def baseStart_1068195 : Nat := 118140960795 + 1068195 * 2 ^ 59
def prefixEnd_1068195 : Nat := 4983230072969 + 3 ^ 40 * 1068195 * 2
def baseEnd_1068195 : Nat := 243776652324245962599985

theorem tailTrace_1068195 : CollatzResearch.WordTrace tailWord_1068195 prefixEnd_1068195 243776652324245962599985 := by
  unfold tailWord_1068195
  simp only [CollatzResearch.WordTrace]
  refine ⟨38960272365119423026862039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25973514910079615351241359 38960272365119423026862039)
  ·
    refine ⟨58440408547679134540293059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38960272365119423026862039 58440408547679134540293059)
    ·
      refine ⟨87660612821518701810439589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58440408547679134540293059 87660612821518701810439589)
      ·
        refine ⟨16436364904034756589457423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87660612821518701810439589 16436364904034756589457423)
        ·
          refine ⟨24654547356052134884186135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16436364904034756589457423 24654547356052134884186135)
          ·
            refine ⟨36981821034078202326279203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24654547356052134884186135 36981821034078202326279203)
            ·
              refine ⟨55472731551117303489418805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36981821034078202326279203 55472731551117303489418805)
              ·
                refine ⟨5200568582917247202133013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55472731551117303489418805 5200568582917247202133013)
                ·
                  refine ⟨243776652324245962599985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5200568582917247202133013 243776652324245962599985)
                  ·
                    rfl

theorem cell21_1068195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_1068195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068195 prefixEnd_1068195 := by exact prefixLift 1068195
  have htrace : WordTrace (prefixWord ++ tailWord_1068195) baseStart_1068195 baseEnd_1068195 := by
    simpa [prefixWord, tailWord_1068195, baseEnd_1068195] using wordTrace_append hprefix tailTrace_1068195
  have hstable : (prefixWord ++ tailWord_1068195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068195).length < 2 ^ (prefixWord ++ tailWord_1068195).sum := by decide
  have hdescent : baseEnd_1068195 < baseStart_1068195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068246 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1068246 : Nat := 118140960795 + 1068246 * 2 ^ 59
def prefixEnd_1068246 : Nat := 4983230072969 + 3 ^ 40 * 1068246 * 2
def baseEnd_1068246 : Nat := 243788291219081207249881

theorem tailTrace_1068246 : CollatzResearch.WordTrace tailWord_1068246 prefixEnd_1068246 243788291219081207249881 := by
  unfold tailWord_1068246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2435133280495916171060537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25974754991956439157979061 2435133280495916171060537)
  ·
    refine ⟨1826349960371937128295403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2435133280495916171060537 1826349960371937128295403)
    ·
      refine ⟨2739524940557905692443105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1826349960371937128295403 2739524940557905692443105)
      ·
        refine ⟨2054643705418429269332329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2739524940557905692443105 2054643705418429269332329)
        ·
          refine ⟨1540982779063821951999247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054643705418429269332329 1540982779063821951999247)
          ·
            refine ⟨2311474168595732927998871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540982779063821951999247 2311474168595732927998871)
            ·
              refine ⟨3467211252893599391998307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311474168595732927998871 3467211252893599391998307)
              ·
                refine ⟨5200816879340399087997461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3467211252893599391998307 5200816879340399087997461)
                ·
                  refine ⟨243788291219081207249881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5200816879340399087997461 243788291219081207249881)
                  ·
                    rfl

theorem cell21_1068246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1068246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068246 prefixEnd_1068246 := by exact prefixLift 1068246
  have htrace : WordTrace (prefixWord ++ tailWord_1068246) baseStart_1068246 baseEnd_1068246 := by
    simpa [prefixWord, tailWord_1068246, baseEnd_1068246] using wordTrace_append hprefix tailTrace_1068246
  have hstable : (prefixWord ++ tailWord_1068246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068246).length < 2 ^ (prefixWord ++ tailWord_1068246).sum := by decide
  have hdescent : baseEnd_1068246 < baseStart_1068246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068257 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 5]
def baseStart_1068257 : Nat := 118140960795 + 1068257 * 2 ^ 59
def prefixEnd_1068257 : Nat := 4983230072969 + 3 ^ 40 * 1068257 * 2
def baseEnd_1068257 : Nat := 243790801568947632566525

theorem tailTrace_1068257 : CollatzResearch.WordTrace tailWord_1068257 prefixEnd_1068257 243790801568947632566525 := by
  unfold tailWord_1068257
  simp only [CollatzResearch.WordTrace]
  refine ⟨38962533690894807615619025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25975022460596538410412683 38962533690894807615619025)
  ·
    refine ⟨29221900268171105711714269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38962533690894807615619025 29221900268171105711714269)
    ·
      refine ⟨10958212600564164641892851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29221900268171105711714269 10958212600564164641892851)
      ·
        refine ⟨16437318900846246962839277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10958212600564164641892851 16437318900846246962839277)
        ·
          refine ⟨6163994587817342611064729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16437318900846246962839277 6163994587817342611064729)
          ·
            refine ⟨4622995940863006958298547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6163994587817342611064729 4622995940863006958298547)
            ·
              refine ⟨6934493911294510437447821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4622995940863006958298547 6934493911294510437447821)
              ·
                refine ⟨2600435216735441414042933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6934493911294510437447821 2600435216735441414042933)
                ·
                  refine ⟨243790801568947632566525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2600435216735441414042933 243790801568947632566525)
                  ·
                    rfl

theorem cell21_1068257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_1068257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068257 prefixEnd_1068257 := by exact prefixLift 1068257
  have htrace : WordTrace (prefixWord ++ tailWord_1068257) baseStart_1068257 baseEnd_1068257 := by
    simpa [prefixWord, tailWord_1068257, baseEnd_1068257] using wordTrace_append hprefix tailTrace_1068257
  have hstable : (prefixWord ++ tailWord_1068257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068257).length < 2 ^ (prefixWord ++ tailWord_1068257).sum := by decide
  have hdescent : baseEnd_1068257 < baseStart_1068257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068291 : List Nat := [1, 1, 1, 3, 2, 6, 1, 3, 3]
def baseStart_1068291 : Nat := 118140960795 + 1068291 * 2 ^ 59
def prefixEnd_1068291 : Nat := 4983230072969 + 3 ^ 40 * 1068291 * 2
def baseEnd_1068291 : Nat := 243798560832171128999789

theorem tailTrace_1068291 : CollatzResearch.WordTrace tailWord_1068291 prefixEnd_1068291 243798560832171128999789 := by
  unfold tailWord_1068291
  simp only [CollatzResearch.WordTrace]
  refine ⟨38963773772771631422356727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25975849181847754281571151 38963773772771631422356727)
  ·
    refine ⟨58445660659157447133535091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38963773772771631422356727 58445660659157447133535091)
    ·
      refine ⟨87668490988736170700302637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58445660659157447133535091 87668490988736170700302637)
      ·
        refine ⟨32875684120776064012613489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87668490988736170700302637 32875684120776064012613489)
        ·
          refine ⟨24656763090582048009460117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32875684120776064012613489 24656763090582048009460117)
          ·
            refine ⟨1155785769871033500443443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24656763090582048009460117 1155785769871033500443443)
            ·
              refine ⟨1733678654806550250665165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155785769871033500443443 1733678654806550250665165)
              ·
                refine ⟨650129495552456343999437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1733678654806550250665165 650129495552456343999437)
                ·
                  refine ⟨243798560832171128999789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650129495552456343999437 243798560832171128999789)
                  ·
                    rfl

theorem cell21_1068291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 3].length) (baseStart_1068291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068291 prefixEnd_1068291 := by exact prefixLift 1068291
  have htrace : WordTrace (prefixWord ++ tailWord_1068291) baseStart_1068291 baseEnd_1068291 := by
    simpa [prefixWord, tailWord_1068291, baseEnd_1068291] using wordTrace_append hprefix tailTrace_1068291
  have hstable : (prefixWord ++ tailWord_1068291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068291).length < 2 ^ (prefixWord ++ tailWord_1068291).sum := by decide
  have hdescent : baseEnd_1068291 < baseStart_1068291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
