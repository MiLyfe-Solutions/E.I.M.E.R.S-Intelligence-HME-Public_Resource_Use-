import V185TrunkScan22Chunk229

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2050624 : List Nat := [2, 1, 1, 2, 2, 2, 2, 10]
def baseStart_2050624 : Nat := 118140960795 + 2050624 * 2 ^ 59
def prefixEnd_2050624 : Nat := 4983230072969 + 3 ^ 40 * 2050624 * 2
def baseEnd_2050624 : Nat := 77996722492258530212545

theorem tailTrace_2050624 : CollatzResearch.WordTrace tailWord_2050624 prefixEnd_2050624 77996722492258530212545 := by
  unfold tailWord_2050624
  simp only [CollatzResearch.WordTrace]
  refine ⟨37396200861473470770987463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49861601148631294361316617 37396200861473470770987463)
  ·
    refine ⟨56094301292210206156481195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37396200861473470770987463 56094301292210206156481195)
    ·
      refine ⟨84141451938315309234721793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56094301292210206156481195 84141451938315309234721793)
      ·
        refine ⟨63106088953736481926041345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84141451938315309234721793 63106088953736481926041345)
        ·
          refine ⟨47329566715302361444531009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63106088953736481926041345 47329566715302361444531009)
          ·
            refine ⟨35497175036476771083398257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47329566715302361444531009 35497175036476771083398257)
            ·
              refine ⟨26622881277357578312548693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35497175036476771083398257 26622881277357578312548693)
              ·
                refine ⟨77996722492258530212545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26622881277357578312548693 77996722492258530212545)
                ·
                  rfl

theorem cell22_2050624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 10].length) (baseStart_2050624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050624 prefixEnd_2050624 := by exact prefixLift 2050624
  have htrace : WordTrace (prefixWord ++ tailWord_2050624) baseStart_2050624 baseEnd_2050624 := by
    simpa [prefixWord, tailWord_2050624, baseEnd_2050624] using wordTrace_append hprefix tailTrace_2050624
  have hstable : (prefixWord ++ tailWord_2050624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050624).length < 2 ^ (prefixWord ++ tailWord_2050624).sum := by decide
  have hdescent : baseEnd_2050624 < baseStart_2050624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050718 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2050718 : Nat := 118140960795 + 2050718 * 2 ^ 59
def prefixEnd_2050718 : Nat := 4983230072969 + 3 ^ 40 * 2050718 * 2
def baseEnd_2050718 : Nat := 702002680551341860062617

theorem tailTrace_2050718 : CollatzResearch.WordTrace tailWord_2050718 prefixEnd_2050718 702002680551341860062617 := by
  unfold tailWord_2050718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9349478773075799449487101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49863886789737597063931205 9349478773075799449487101)
  ·
    refine ⟨3506054539903424793557663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9349478773075799449487101 3506054539903424793557663)
    ·
      refine ⟨5259081809855137190336495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3506054539903424793557663 5259081809855137190336495)
      ·
        refine ⟨7888622714782705785504743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5259081809855137190336495 7888622714782705785504743)
        ·
          refine ⟨11832934072174058678257115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7888622714782705785504743 11832934072174058678257115)
          ·
            refine ⟨17749401108261088017385673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11832934072174058678257115 17749401108261088017385673)
            ·
              refine ⟨13312050831195816013039255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17749401108261088017385673 13312050831195816013039255)
              ·
                refine ⟨19968076246793724019558883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13312050831195816013039255 19968076246793724019558883)
                ·
                  refine ⟨29952114370190586029338325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19968076246793724019558883 29952114370190586029338325)
                  ·
                    refine ⟨702002680551341860062617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29952114370190586029338325 702002680551341860062617)
                    ·
                      rfl

theorem cell22_2050718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2050718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050718 prefixEnd_2050718 := by exact prefixLift 2050718
  have htrace : WordTrace (prefixWord ++ tailWord_2050718) baseStart_2050718 baseEnd_2050718 := by
    simpa [prefixWord, tailWord_2050718, baseEnd_2050718] using wordTrace_append hprefix tailTrace_2050718
  have hstable : (prefixWord ++ tailWord_2050718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050718).length < 2 ^ (prefixWord ++ tailWord_2050718).sum := by decide
  have hdescent : baseEnd_2050718 < baseStart_2050718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050780 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2050780 : Nat := 118140960795 + 2050780 * 2 ^ 59
def prefixEnd_2050780 : Nat := 4983230072969 + 3 ^ 40 * 2050780 * 2
def baseEnd_2050780 : Nat := 702023904418394365012427

theorem tailTrace_2050780 : CollatzResearch.WordTrace tailWord_2050780 prefixEnd_2050780 702023904418394365012427 := by
  unfold tailWord_2050780
  simp only [CollatzResearch.WordTrace]
  refine ⟨37399045755190890092326897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49865394340254520123102529 37399045755190890092326897)
  ·
    refine ⟨28049284316393167569245173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37399045755190890092326897 28049284316393167569245173)
    ·
      refine ⟨2629620404661859459616735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28049284316393167569245173 2629620404661859459616735)
      ·
        refine ⟨3944430606992789189425103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629620404661859459616735 3944430606992789189425103)
        ·
          refine ⟨5916645910489183784137655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944430606992789189425103 5916645910489183784137655)
          ·
            refine ⟨8874968865733775676206483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5916645910489183784137655 8874968865733775676206483)
            ·
              refine ⟨13312453298600663514309725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8874968865733775676206483 13312453298600663514309725)
              ·
                refine ⟨4992169986975248817866147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13312453298600663514309725 4992169986975248817866147)
                ·
                  refine ⟨7488254980462873226799221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4992169986975248817866147 7488254980462873226799221)
                  ·
                    refine ⟨702023904418394365012427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7488254980462873226799221 702023904418394365012427)
                    ·
                      rfl

theorem cell22_2050780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2050780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050780 prefixEnd_2050780 := by exact prefixLift 2050780
  have htrace : WordTrace (prefixWord ++ tailWord_2050780) baseStart_2050780 baseEnd_2050780 := by
    simpa [prefixWord, tailWord_2050780, baseEnd_2050780] using wordTrace_append hprefix tailTrace_2050780
  have hstable : (prefixWord ++ tailWord_2050780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050780).length < 2 ^ (prefixWord ++ tailWord_2050780).sum := by decide
  have hdescent : baseEnd_2050780 < baseStart_2050780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050808 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 5, 3]
def baseStart_2050808 : Nat := 118140960795 + 2050808 * 2 ^ 59
def prefixEnd_2050808 : Nat := 4983230072969 + 3 ^ 40 * 2050808 * 2
def baseEnd_2050808 : Nat := 702033489390611625312341

theorem tailTrace_2050808 : CollatzResearch.WordTrace tailWord_2050808 prefixEnd_2050808 702033489390611625312341 := by
  unfold tailWord_2050808
  simp only [CollatzResearch.WordTrace]
  refine ⟨37399556377140170483336539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49866075169520227311115385 37399556377140170483336539)
  ·
    refine ⟨56099334565710255725004809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37399556377140170483336539 56099334565710255725004809)
    ·
      refine ⟨42074500924282691793753607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56099334565710255725004809 42074500924282691793753607)
      ·
        refine ⟨63111751386424037690630411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42074500924282691793753607 63111751386424037690630411)
        ·
          refine ⟨94667627079636056535945617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63111751386424037690630411 94667627079636056535945617)
          ·
            refine ⟨71000720309727042401959213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94667627079636056535945617 71000720309727042401959213)
            ·
              refine ⟨26625270116147640900734705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71000720309727042401959213 26625270116147640900734705)
              ·
                refine ⟨19968952587110730675551029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26625270116147640900734705 19968952587110730675551029)
                ·
                  refine ⟨1872089305041631000832909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19968952587110730675551029 1872089305041631000832909)
                  ·
                    refine ⟨702033489390611625312341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1872089305041631000832909 702033489390611625312341)
                    ·
                      rfl

theorem cell22_2050808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_2050808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050808 prefixEnd_2050808 := by exact prefixLift 2050808
  have htrace : WordTrace (prefixWord ++ tailWord_2050808) baseStart_2050808 baseEnd_2050808 := by
    simpa [prefixWord, tailWord_2050808, baseEnd_2050808] using wordTrace_append hprefix tailTrace_2050808
  have hstable : (prefixWord ++ tailWord_2050808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050808).length < 2 ^ (prefixWord ++ tailWord_2050808).sum := by decide
  have hdescent : baseEnd_2050808 < baseStart_2050808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050814 : List Nat := [4, 2, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_2050814 : Nat := 118140960795 + 2050814 * 2 ^ 59
def prefixEnd_2050814 : Nat := 4983230072969 + 3 ^ 40 * 2050814 * 2
def baseEnd_2050814 : Nat := 702035543313229609662323

theorem tailTrace_2050814 : CollatzResearch.WordTrace tailWord_2050814 prefixEnd_2050814 702035543313229609662323 := by
  unfold tailWord_2050814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9349916449032325498923937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49866221061505735994260997 9349916449032325498923937)
  ·
    refine ⟨7012437336774244124192953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9349916449032325498923937 7012437336774244124192953)
    ·
      refine ⟨5259328002580683093144715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7012437336774244124192953 5259328002580683093144715)
      ·
        refine ⟨7888992003871024639717073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5259328002580683093144715 7888992003871024639717073)
        ·
          refine ⟨5916744002903268479787805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7888992003871024639717073 5916744002903268479787805)
          ·
            refine ⟨2218779001088725679920427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5916744002903268479787805 2218779001088725679920427)
            ·
              refine ⟨3328168501633088519880641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218779001088725679920427 3328168501633088519880641)
              ·
                refine ⟨2496126376224816389910481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3328168501633088519880641 2496126376224816389910481)
                ·
                  refine ⟨1872094782168612292432861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2496126376224816389910481 1872094782168612292432861)
                  ·
                    refine ⟨702035543313229609662323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1872094782168612292432861 702035543313229609662323)
                    ·
                      rfl

theorem cell22_2050814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_2050814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050814 prefixEnd_2050814 := by exact prefixLift 2050814
  have htrace : WordTrace (prefixWord ++ tailWord_2050814) baseStart_2050814 baseEnd_2050814 := by
    simpa [prefixWord, tailWord_2050814, baseEnd_2050814] using wordTrace_append hprefix tailTrace_2050814
  have hstable : (prefixWord ++ tailWord_2050814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050814).length < 2 ^ (prefixWord ++ tailWord_2050814).sum := by decide
  have hdescent : baseEnd_2050814 < baseStart_2050814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050915 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 1, 5]
def baseStart_2050915 : Nat := 118140960795 + 2050915 * 2 ^ 59
def prefixEnd_2050915 : Nat := 4983230072969 + 3 ^ 40 * 2050915 * 2
def baseEnd_2050915 : Nat := 702070117677299012887013

theorem tailTrace_2050915 : CollatzResearch.WordTrace tailWord_2050915 prefixEnd_2050915 702070117677299012887013 := by
  unfold tailWord_2050915
  simp only [CollatzResearch.WordTrace]
  refine ⟨74803015364892698240818199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49868676909928465493878799 74803015364892698240818199)
  ·
    refine ⟨112204523047339047361227299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74803015364892698240818199 112204523047339047361227299)
    ·
      refine ⟨168306784571008571041840949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112204523047339047361227299 168306784571008571041840949)
      ·
        refine ⟨15778761053532053535172589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168306784571008571041840949 15778761053532053535172589)
        ·
          refine ⟨5917035395074520075689721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15778761053532053535172589 5917035395074520075689721)
          ·
            refine ⟨4437776546305890056767291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5917035395074520075689721 4437776546305890056767291)
            ·
              refine ⟨6656664819458835085150937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437776546305890056767291 6656664819458835085150937)
              ·
                refine ⟨4992498614594126313863203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6656664819458835085150937 4992498614594126313863203)
                ·
                  refine ⟨7488747921891189470794805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4992498614594126313863203 7488747921891189470794805)
                  ·
                    refine ⟨702070117677299012887013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7488747921891189470794805 702070117677299012887013)
                    ·
                      rfl

theorem cell22_2050915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 5].length) (baseStart_2050915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050915 prefixEnd_2050915 := by exact prefixLift 2050915
  have htrace : WordTrace (prefixWord ++ tailWord_2050915) baseStart_2050915 baseEnd_2050915 := by
    simpa [prefixWord, tailWord_2050915, baseEnd_2050915] using wordTrace_append hprefix tailTrace_2050915
  have hstable : (prefixWord ++ tailWord_2050915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050915).length < 2 ^ (prefixWord ++ tailWord_2050915).sum := by decide
  have hdescent : baseEnd_2050915 < baseStart_2050915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050930 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_2050930 : Nat := 118140960795 + 2050930 * 2 ^ 59
def prefixEnd_2050930 : Nat := 4983230072969 + 3 ^ 40 * 2050930 * 2
def baseEnd_2050930 : Nat := 702075252483843973761967

theorem tailTrace_2050930 : CollatzResearch.WordTrace tailWord_2050930 prefixEnd_2050930 702075252483843973761967 := by
  unfold tailWord_2050930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18700890614959588950653561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49869041639892237201742829 18700890614959588950653561)
  ·
    refine ⟨14025667961219691712990171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18700890614959588950653561 14025667961219691712990171)
    ·
      refine ⟨21038501941829537569485257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14025667961219691712990171 21038501941829537569485257)
      ·
        refine ⟨15778876456372153177113943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21038501941829537569485257 15778876456372153177113943)
        ·
          refine ⟨23668314684558229765670915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15778876456372153177113943 23668314684558229765670915)
          ·
            refine ⟨35502472026837344648506373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23668314684558229765670915 35502472026837344648506373)
            ·
              refine ⟨6656713505032002121594945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35502472026837344648506373 6656713505032002121594945)
              ·
                refine ⟨4992535128774001591196209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6656713505032002121594945 4992535128774001591196209)
                ·
                  refine ⟨3744401346580501193397157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4992535128774001591196209 3744401346580501193397157)
                  ·
                    refine ⟨702075252483843973761967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3744401346580501193397157 702075252483843973761967)
                    ·
                      rfl

theorem cell22_2050930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_2050930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050930 prefixEnd_2050930 := by exact prefixLift 2050930
  have htrace : WordTrace (prefixWord ++ tailWord_2050930) baseStart_2050930 baseEnd_2050930 := by
    simpa [prefixWord, tailWord_2050930, baseEnd_2050930] using wordTrace_append hprefix tailTrace_2050930
  have hstable : (prefixWord ++ tailWord_2050930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050930).length < 2 ^ (prefixWord ++ tailWord_2050930).sum := by decide
  have hdescent : baseEnd_2050930 < baseStart_2050930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050934 : List Nat := [5, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_2050934 : Nat := 118140960795 + 2050934 * 2 ^ 59
def prefixEnd_2050934 : Nat := 4983230072969 + 3 ^ 40 * 2050934 * 2
def baseEnd_2050934 : Nat := 234025540588529765553985

theorem tailTrace_2050934 : CollatzResearch.WordTrace tailWord_2050934 prefixEnd_2050934 234025540588529765553985 := by
  unfold tailWord_2050934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4675231771988991530359991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49869138901215909657173237 4675231771988991530359991)
  ·
    refine ⟨7012847657983487295539987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4675231771988991530359991 7012847657983487295539987)
    ·
      refine ⟨10519271486975230943309981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7012847657983487295539987 10519271486975230943309981)
      ·
        refine ⟨3944726807615711603741243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10519271486975230943309981 3944726807615711603741243)
        ·
          refine ⟨5917090211423567405611865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944726807615711603741243 5917090211423567405611865)
          ·
            refine ⟨4437817658567675554208899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5917090211423567405611865 4437817658567675554208899)
            ·
              refine ⟨6656726487851513331313349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437817658567675554208899 6656726487851513331313349)
              ·
                refine ⟨1248136216472158749621253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6656726487851513331313349 1248136216472158749621253)
                ·
                  refine ⟨234025540588529765553985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1248136216472158749621253 234025540588529765553985)
                  ·
                    rfl

theorem cell22_2050934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_2050934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050934 prefixEnd_2050934 := by exact prefixLift 2050934
  have htrace : WordTrace (prefixWord ++ tailWord_2050934) baseStart_2050934 baseEnd_2050934 := by
    simpa [prefixWord, tailWord_2050934, baseEnd_2050934] using wordTrace_append hprefix tailTrace_2050934
  have hstable : (prefixWord ++ tailWord_2050934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050934).length < 2 ^ (prefixWord ++ tailWord_2050934).sum := by decide
  have hdescent : baseEnd_2050934 < baseStart_2050934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050988 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_2050988 : Nat := 118140960795 + 2050988 * 2 ^ 59
def prefixEnd_2050988 : Nat := 4983230072969 + 3 ^ 40 * 2050988 * 2
def baseEnd_2050988 : Nat := 702095107069151155811789

theorem tailTrace_2050988 : CollatzResearch.WordTrace tailWord_2050988 prefixEnd_2050988 702095107069151155811789 := by
  unfold tailWord_2050988
  simp only [CollatzResearch.WordTrace]
  refine ⟨37402838946814115854112809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49870451929085487805483745 37402838946814115854112809)
  ·
    refine ⟨28052129210110586890584607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37402838946814115854112809 28052129210110586890584607)
    ·
      refine ⟨42078193815165880335876911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28052129210110586890584607 42078193815165880335876911)
      ·
        refine ⟨63117290722748820503815367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42078193815165880335876911 63117290722748820503815367)
        ·
          refine ⟨94675936084123230755723051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63117290722748820503815367 94675936084123230755723051)
          ·
            refine ⟨142013904126184846133584577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94675936084123230755723051 142013904126184846133584577)
            ·
              refine ⟨106510428094638634600188433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142013904126184846133584577 106510428094638634600188433)
              ·
                refine ⟨79882821070978975950141325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106510428094638634600188433 79882821070978975950141325)
                ·
                  refine ⟨29956057901617115981302997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79882821070978975950141325 29956057901617115981302997)
                  ·
                    refine ⟨702095107069151155811789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29956057901617115981302997 702095107069151155811789)
                    ·
                      rfl

theorem cell22_2050988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_2050988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050988 prefixEnd_2050988 := by exact prefixLift 2050988
  have htrace : WordTrace (prefixWord ++ tailWord_2050988) baseStart_2050988 baseEnd_2050988 := by
    simpa [prefixWord, tailWord_2050988, baseEnd_2050988] using wordTrace_append hprefix tailTrace_2050988
  have hstable : (prefixWord ++ tailWord_2050988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050988).length < 2 ^ (prefixWord ++ tailWord_2050988).sum := by decide
  have hdescent : baseEnd_2050988 < baseStart_2050988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051058 : List Nat := [3, 2, 1, 5, 2, 1, 2, 1, 5]
def baseStart_2051058 : Nat := 118140960795 + 2051058 * 2 ^ 59
def prefixEnd_2051058 : Nat := 4983230072969 + 3 ^ 40 * 2051058 * 2
def baseEnd_2051058 : Nat := 234039689833231435520525

theorem tailTrace_2051058 : CollatzResearch.WordTrace tailWord_2051058 prefixEnd_2051058 234039689833231435520525 := by
  unfold tailWord_2051058
  simp only [CollatzResearch.WordTrace]
  refine ⟨18702057750843658415818457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49872154002249755775515885 18702057750843658415818457)
  ·
    refine ⟨14026543313132743811863843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18702057750843658415818457 14026543313132743811863843)
    ·
      refine ⟨21039814969699115717795765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14026543313132743811863843 21039814969699115717795765)
      ·
        refine ⟨1972482653409292098543353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21039814969699115717795765 1972482653409292098543353)
        ·
          refine ⟨1479361990056969073907515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1972482653409292098543353 1479361990056969073907515)
          ·
            refine ⟨2219042985085453610861273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479361990056969073907515 2219042985085453610861273)
            ·
              refine ⟨1664282238814090208145955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219042985085453610861273 1664282238814090208145955)
              ·
                refine ⟨2496423358221135312218933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664282238814090208145955 2496423358221135312218933)
                ·
                  refine ⟨234039689833231435520525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2496423358221135312218933 234039689833231435520525)
                  ·
                    rfl

theorem cell22_2051058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_2051058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051058 prefixEnd_2051058 := by exact prefixLift 2051058
  have htrace : WordTrace (prefixWord ++ tailWord_2051058) baseStart_2051058 baseEnd_2051058 := by
    simpa [prefixWord, tailWord_2051058, baseEnd_2051058] using wordTrace_append hprefix tailTrace_2051058
  have hstable : (prefixWord ++ tailWord_2051058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051058).length < 2 ^ (prefixWord ++ tailWord_2051058).sum := by decide
  have hdescent : baseEnd_2051058 < baseStart_2051058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051065 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 4, 4]
def baseStart_2051065 : Nat := 118140960795 + 2051065 * 2 ^ 59
def prefixEnd_2051065 : Nat := 4983230072969 + 3 ^ 40 * 2051065 * 2
def baseEnd_2051065 : Nat := 702121465742748621636553

theorem tailTrace_2051065 : CollatzResearch.WordTrace tailWord_2051065 prefixEnd_2051065 702121465742748621636553 := by
  unfold tailWord_2051065
  simp only [CollatzResearch.WordTrace]
  refine ⟨74808486314349273858778649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49872324209566182572519099 74808486314349273858778649)
  ·
    refine ⟨56106364735761955394083987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74808486314349273858778649 56106364735761955394083987)
    ·
      refine ⟨84159547103642933091125981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56106364735761955394083987 84159547103642933091125981)
      ·
        refine ⟨31559830163866099909172243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84159547103642933091125981 31559830163866099909172243)
        ·
          refine ⟨47339745245799149863758365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31559830163866099909172243 47339745245799149863758365)
          ·
            refine ⟨17752404467174681198909387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47339745245799149863758365 17752404467174681198909387)
            ·
              refine ⟨26628606700762021798364081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17752404467174681198909387 26628606700762021798364081)
              ·
                refine ⟨19971455025571516348773061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26628606700762021798364081 19971455025571516348773061)
                ·
                  refine ⟨3744647817294659315394949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19971455025571516348773061 3744647817294659315394949)
                  ·
                    refine ⟨702121465742748621636553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3744647817294659315394949 702121465742748621636553)
                    ·
                      rfl

theorem cell22_2051065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_2051065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051065 prefixEnd_2051065 := by exact prefixLift 2051065
  have htrace : WordTrace (prefixWord ++ tailWord_2051065) baseStart_2051065 baseEnd_2051065 := by
    simpa [prefixWord, tailWord_2051065, baseEnd_2051065] using wordTrace_append hprefix tailTrace_2051065
  have hstable : (prefixWord ++ tailWord_2051065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051065).length < 2 ^ (prefixWord ++ tailWord_2051065).sum := by decide
  have hdescent : baseEnd_2051065 < baseStart_2051065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051080 : List Nat := [2, 1, 3, 2, 1, 3, 2, 8]
def baseStart_2051080 : Nat := 118140960795 + 2051080 * 2 ^ 59
def prefixEnd_2051080 : Nat := 4983230072969 + 3 ^ 40 * 2051080 * 2
def baseEnd_2051080 : Nat := 78014066727699286945723

theorem tailTrace_2051080 : CollatzResearch.WordTrace tailWord_2051080 prefixEnd_2051080 78014066727699286945723 := by
  unfold tailWord_2051080
  simp only [CollatzResearch.WordTrace]
  refine ⟨37404516704647465710287347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49872688939529954280383129 37404516704647465710287347)
  ·
    refine ⟨56106775056971198565431021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37404516704647465710287347 56106775056971198565431021)
    ·
      refine ⟨21040040646364199462036633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56106775056971198565431021 21040040646364199462036633)
      ·
        refine ⟨15780030484773149596527475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21040040646364199462036633 15780030484773149596527475)
        ·
          refine ⟨23670045727159724394791213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15780030484773149596527475 23670045727159724394791213)
          ·
            refine ⟨8876267147684896648046705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23670045727159724394791213 8876267147684896648046705)
            ·
              refine ⟨6657200360763672486035029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8876267147684896648046705 6657200360763672486035029)
              ·
                refine ⟨78014066727699286945723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6657200360763672486035029 78014066727699286945723)
                ·
                  rfl

theorem cell22_2051080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 8].length) (baseStart_2051080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051080 prefixEnd_2051080 := by exact prefixLift 2051080
  have htrace : WordTrace (prefixWord ++ tailWord_2051080) baseStart_2051080 baseEnd_2051080 := by
    simpa [prefixWord, tailWord_2051080, baseEnd_2051080] using wordTrace_append hprefix tailTrace_2051080
  have hstable : (prefixWord ++ tailWord_2051080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051080).length < 2 ^ (prefixWord ++ tailWord_2051080).sum := by decide
  have hdescent : baseEnd_2051080 < baseStart_2051080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051082 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_2051082 : Nat := 118140960795 + 2051082 * 2 ^ 59
def prefixEnd_2051082 : Nat := 4983230072969 + 3 ^ 40 * 2051082 * 2
def baseEnd_2051082 : Nat := 702127285190166243961501

theorem tailTrace_2051082 : CollatzResearch.WordTrace tailWord_2051082 prefixEnd_2051082 702127285190166243961501 := by
  unfold tailWord_2051082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18702276588821921440536875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49872737570191790508098333 18702276588821921440536875)
  ·
    refine ⟨28053414883232882160805313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18702276588821921440536875 28053414883232882160805313)
    ·
      refine ⟨21040061162424661620603985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28053414883232882160805313 21040061162424661620603985)
      ·
        refine ⟨15780045871818496215452989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21040061162424661620603985 15780045871818496215452989)
        ·
          refine ⟨5917517201931936080794871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15780045871818496215452989 5917517201931936080794871)
          ·
            refine ⟨8876275802897904121192307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5917517201931936080794871 8876275802897904121192307)
            ·
              refine ⟨13314413704346856181788461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8876275802897904121192307 13314413704346856181788461)
              ·
                refine ⟨4992905139130071068170673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13314413704346856181788461 4992905139130071068170673)
                ·
                  refine ⟨3744678854347553301128005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4992905139130071068170673 3744678854347553301128005)
                  ·
                    refine ⟨702127285190166243961501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3744678854347553301128005 702127285190166243961501)
                    ·
                      rfl

theorem cell22_2051082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_2051082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051082 prefixEnd_2051082 := by exact prefixLift 2051082
  have htrace : WordTrace (prefixWord ++ tailWord_2051082) baseStart_2051082 baseEnd_2051082 := by
    simpa [prefixWord, tailWord_2051082, baseEnd_2051082] using wordTrace_append hprefix tailTrace_2051082
  have hstable : (prefixWord ++ tailWord_2051082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051082).length < 2 ^ (prefixWord ++ tailWord_2051082).sum := by decide
  have hdescent : baseEnd_2051082 < baseStart_2051082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051101 : List Nat := [1, 4, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_2051101 : Nat := 118140960795 + 2051101 * 2 ^ 59
def prefixEnd_2051101 : Nat := 4983230072969 + 3 ^ 40 * 2051101 * 2
def baseEnd_2051101 : Nat := 702133789278456527736443

theorem tailTrace_2051101 : CollatzResearch.WordTrace tailWord_2051101 prefixEnd_2051101 702133789278456527736443 := by
  unfold tailWord_2051101
  simp only [CollatzResearch.WordTrace]
  refine ⟨74809799342218852007089157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49873199561479234671392771 74809799342218852007089157)
  ·
    refine ⟨14026837376666034751329217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74809799342218852007089157 14026837376666034751329217)
    ·
      refine ⟨10520128032499526063496913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14026837376666034751329217 10520128032499526063496913)
      ·
        refine ⟨7890096024374644547622685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10520128032499526063496913 7890096024374644547622685)
        ·
          refine ⟨2958786009140491705358507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7890096024374644547622685 2958786009140491705358507)
          ·
            refine ⟨4438179013710737558037761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958786009140491705358507 4438179013710737558037761)
            ·
              refine ⟨3328634260283053168528321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4438179013710737558037761 3328634260283053168528321)
              ·
                refine ⟨2496475695212289876396241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3328634260283053168528321 2496475695212289876396241)
                ·
                  refine ⟨1872356771409217407297181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2496475695212289876396241 1872356771409217407297181)
                  ·
                    refine ⟨702133789278456527736443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1872356771409217407297181 702133789278456527736443)
                    ·
                      rfl

theorem cell22_2051101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_2051101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051101 prefixEnd_2051101 := by exact prefixLift 2051101
  have htrace : WordTrace (prefixWord ++ tailWord_2051101) baseStart_2051101 baseEnd_2051101 := by
    simpa [prefixWord, tailWord_2051101, baseEnd_2051101] using wordTrace_append hprefix tailTrace_2051101
  have hstable : (prefixWord ++ tailWord_2051101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051101).length < 2 ^ (prefixWord ++ tailWord_2051101).sum := by decide
  have hdescent : baseEnd_2051101 < baseStart_2051101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051114 : List Nat := [3, 1, 4, 1, 3, 2, 1, 7]
def baseStart_2051114 : Nat := 118140960795 + 2051114 * 2 ^ 59
def prefixEnd_2051114 : Nat := 4983230072969 + 3 ^ 40 * 2051114 * 2
def baseEnd_2051114 : Nat := 78015359938236536351267

theorem tailTrace_2051114 : CollatzResearch.WordTrace tailWord_2051114 prefixEnd_2051114 78015359938236536351267 := by
  unfold tailWord_2051114
  simp only [CollatzResearch.WordTrace]
  refine ⟨18702568372792938806828099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49873515660781170151541597 18702568372792938806828099)
  ·
    refine ⟨28053852559189408210242149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18702568372792938806828099 28053852559189408210242149)
    ·
      refine ⟨5260097354848014039420403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28053852559189408210242149 5260097354848014039420403)
      ·
        refine ⟨7890146032272021059130605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5260097354848014039420403 7890146032272021059130605)
        ·
          refine ⟨2958804762102007897173977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7890146032272021059130605 2958804762102007897173977)
          ·
            refine ⟨2219103571576505922880483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2958804762102007897173977 2219103571576505922880483)
            ·
              refine ⟨3328655357364758884320725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2219103571576505922880483 3328655357364758884320725)
              ·
                refine ⟨78015359938236536351267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3328655357364758884320725 78015359938236536351267)
                ·
                  rfl

theorem cell22_2051114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_2051114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051114 prefixEnd_2051114 := by exact prefixLift 2051114
  have htrace : WordTrace (prefixWord ++ tailWord_2051114) baseStart_2051114 baseEnd_2051114 := by
    simpa [prefixWord, tailWord_2051114, baseEnd_2051114] using wordTrace_append hprefix tailTrace_2051114
  have hstable : (prefixWord ++ tailWord_2051114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051114).length < 2 ^ (prefixWord ++ tailWord_2051114).sum := by decide
  have hdescent : baseEnd_2051114 < baseStart_2051114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051125 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 9]
def baseStart_2051125 : Nat := 118140960795 + 2051125 * 2 ^ 59
def prefixEnd_2051125 : Nat := 4983230072969 + 3 ^ 40 * 2051125 * 2
def baseEnd_2051125 : Nat := 234047334989642821712123

theorem tailTrace_2051125 : CollatzResearch.WordTrace tailWord_2051125 prefixEnd_2051125 234047334989642821712123 := by
  unfold tailWord_2051125
  simp only [CollatzResearch.WordTrace]
  refine ⟨74810674694131904105962829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49873783129421269403975219 74810674694131904105962829)
  ·
    refine ⟨28054003010299464039736061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74810674694131904105962829 28054003010299464039736061)
    ·
      refine ⟨10520251128862299014901023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28054003010299464039736061 10520251128862299014901023)
      ·
        refine ⟨15780376693293448522351535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10520251128862299014901023 15780376693293448522351535)
        ·
          refine ⟨23670565039940172783527303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15780376693293448522351535 23670565039940172783527303)
          ·
            refine ⟨35505847559910259175290955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23670565039940172783527303 35505847559910259175290955)
            ·
              refine ⟨53258771339865388762936433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35505847559910259175290955 53258771339865388762936433)
              ·
                refine ⟨39944078504899041572202325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53258771339865388762936433 39944078504899041572202325)
                ·
                  refine ⟨234047334989642821712123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39944078504899041572202325 234047334989642821712123)
                  ·
                    rfl

theorem cell22_2051125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_2051125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051125 prefixEnd_2051125 := by exact prefixLift 2051125
  have htrace : WordTrace (prefixWord ++ tailWord_2051125) baseStart_2051125 baseEnd_2051125 := by
    simpa [prefixWord, tailWord_2051125, baseEnd_2051125] using wordTrace_append hprefix tailTrace_2051125
  have hstable : (prefixWord ++ tailWord_2051125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051125).length < 2 ^ (prefixWord ++ tailWord_2051125).sum := by decide
  have hdescent : baseEnd_2051125 < baseStart_2051125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051129 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 3, 3]
def baseStart_2051129 : Nat := 118140960795 + 2051129 * 2 ^ 59
def prefixEnd_2051129 : Nat := 4983230072969 + 3 ^ 40 * 2051129 * 2
def baseEnd_2051129 : Nat := 702143374250673788036357

theorem tailTrace_2051129 : CollatzResearch.WordTrace tailWord_2051129 prefixEnd_2051129 702143374250673788036357 := by
  unfold tailWord_2051129
  simp only [CollatzResearch.WordTrace]
  refine ⟨74810820586117412789108441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49873880390744941859405627 74810820586117412789108441)
  ·
    refine ⟨56108115439588059591831331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74810820586117412789108441 56108115439588059591831331)
    ·
      refine ⟨84162173159382089387746997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56108115439588059591831331 84162173159382089387746997)
      ·
        refine ⟨7890203733692070880101281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84162173159382089387746997 7890203733692070880101281)
        ·
          refine ⟨5917652800269053160075961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7890203733692070880101281 5917652800269053160075961)
          ·
            refine ⟨4438239600201789870056971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5917652800269053160075961 4438239600201789870056971)
            ·
              refine ⟨6657359400302684805085457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438239600201789870056971 6657359400302684805085457)
              ·
                refine ⟨4993019550227013603814093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6657359400302684805085457 4993019550227013603814093)
                ·
                  refine ⟨1872382331335130101430285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4993019550227013603814093 1872382331335130101430285)
                  ·
                    refine ⟨702143374250673788036357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1872382331335130101430285 702143374250673788036357)
                    ·
                      rfl

theorem cell22_2051129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 3].length) (baseStart_2051129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051129 prefixEnd_2051129 := by exact prefixLift 2051129
  have htrace : WordTrace (prefixWord ++ tailWord_2051129) baseStart_2051129 baseEnd_2051129 := by
    simpa [prefixWord, tailWord_2051129, baseEnd_2051129] using wordTrace_append hprefix tailTrace_2051129
  have hstable : (prefixWord ++ tailWord_2051129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051129).length < 2 ^ (prefixWord ++ tailWord_2051129).sum := by decide
  have hdescent : baseEnd_2051129 < baseStart_2051129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051232 : List Nat := [2, 1, 1, 4, 2, 1, 4, 7]
def baseStart_2051232 : Nat := 118140960795 + 2051232 * 2 ^ 59
def prefixEnd_2051232 : Nat := 4983230072969 + 3 ^ 40 * 2051232 * 2
def baseEnd_2051232 : Nat := 78019848139512872523449

theorem tailTrace_2051232 : CollatzResearch.WordTrace tailWord_2051232 prefixEnd_2051232 78019848139512872523449 := by
  unfold tailWord_2051232
  simp only [CollatzResearch.WordTrace]
  refine ⟨37407288652372130690053975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49876384869829507586738633 37407288652372130690053975)
  ·
    refine ⟨56110932978558196035080963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37407288652372130690053975 56110932978558196035080963)
    ·
      refine ⟨84166399467837294052621445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56110932978558196035080963 84166399467837294052621445)
      ·
        refine ⟨15781199900219492634866521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84166399467837294052621445 15781199900219492634866521)
        ·
          refine ⟨11835899925164619476149891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15781199900219492634866521 11835899925164619476149891)
          ·
            refine ⟨17753849887746929214224837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11835899925164619476149891 17753849887746929214224837)
            ·
              refine ⟨3328846853952549227667157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17753849887746929214224837 3328846853952549227667157)
              ·
                refine ⟨78019848139512872523449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3328846853952549227667157 78019848139512872523449)
                ·
                  rfl

theorem cell22_2051232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 7].length) (baseStart_2051232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051232 prefixEnd_2051232 := by exact prefixLift 2051232
  have htrace : WordTrace (prefixWord ++ tailWord_2051232) baseStart_2051232 baseEnd_2051232 := by
    simpa [prefixWord, tailWord_2051232, baseEnd_2051232] using wordTrace_append hprefix tailTrace_2051232
  have hstable : (prefixWord ++ tailWord_2051232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051232).length < 2 ^ (prefixWord ++ tailWord_2051232).sum := by decide
  have hdescent : baseEnd_2051232 < baseStart_2051232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051236 : List Nat := [2, 3, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_2051236 : Nat := 118140960795 + 2051236 * 2 ^ 59
def prefixEnd_2051236 : Nat := 4983230072969 + 3 ^ 40 * 2051236 * 2
def baseEnd_2051236 : Nat := 702180002537361175611029

theorem tailTrace_2051236 : CollatzResearch.WordTrace tailWord_2051236 prefixEnd_2051236 702180002537361175611029 := by
  unfold tailWord_2051236
  simp only [CollatzResearch.WordTrace]
  refine ⟨37407361598364885031626781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49876482131153180042169041 37407361598364885031626781)
  ·
    refine ⟨14027760599386831886860043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37407361598364885031626781 14027760599386831886860043)
    ·
      refine ⟨21041640899080247830290065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14027760599386831886860043 21041640899080247830290065)
      ·
        refine ⟨15781230674310185872717549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21041640899080247830290065 15781230674310185872717549)
        ·
          refine ⟨5917961502866319702269081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15781230674310185872717549 5917961502866319702269081)
          ·
            refine ⟨4438471127149739776701811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5917961502866319702269081 4438471127149739776701811)
            ·
              refine ⟨6657706690724609665052717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438471127149739776701811 6657706690724609665052717)
              ·
                refine ⟨2496640009021728624394769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6657706690724609665052717 2496640009021728624394769)
                ·
                  refine ⟨1872480006766296468296077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2496640009021728624394769 1872480006766296468296077)
                  ·
                    refine ⟨702180002537361175611029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1872480006766296468296077 702180002537361175611029)
                    ·
                      rfl

theorem cell22_2051236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_2051236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051236 prefixEnd_2051236 := by exact prefixLift 2051236
  have htrace : WordTrace (prefixWord ++ tailWord_2051236) baseStart_2051236 baseEnd_2051236 := by
    simpa [prefixWord, tailWord_2051236, baseEnd_2051236] using wordTrace_append hprefix tailTrace_2051236
  have hstable : (prefixWord ++ tailWord_2051236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051236).length < 2 ^ (prefixWord ++ tailWord_2051236).sum := by decide
  have hdescent : baseEnd_2051236 < baseStart_2051236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051266 : List Nat := [3, 5, 1, 1, 2, 10]
def baseStart_2051266 : Nat := 118140960795 + 2051266 * 2 ^ 59
def prefixEnd_2051266 : Nat := 4983230072969 + 3 ^ 40 * 2051266 * 2
def baseEnd_2051266 : Nat := 8669015705561124658777

theorem tailTrace_2051266 : CollatzResearch.WordTrace tailWord_2051266 prefixEnd_2051266 8669015705561124658777 := by
  unfold tailWord_2051266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18703954346655271296711413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49877211591080723457897101 18703954346655271296711413)
  ·
    refine ⟨1753495719998931684066695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18703954346655271296711413 1753495719998931684066695)
    ·
      refine ⟨2630243579998397526100043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1753495719998931684066695 2630243579998397526100043)
      ·
        refine ⟨3945365369997596289150065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2630243579998397526100043 3945365369997596289150065)
        ·
          refine ⟨2959024027498197216862549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3945365369997596289150065 2959024027498197216862549)
          ·
            refine ⟨8669015705561124658777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2959024027498197216862549 8669015705561124658777)
            ·
              rfl

theorem cell22_2051266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 10].length) (baseStart_2051266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051266 prefixEnd_2051266 := by exact prefixLift 2051266
  have htrace : WordTrace (prefixWord ++ tailWord_2051266) baseStart_2051266 baseEnd_2051266 := by
    simpa [prefixWord, tailWord_2051266, baseEnd_2051266] using wordTrace_append hprefix tailTrace_2051266
  have hstable : (prefixWord ++ tailWord_2051266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051266).length < 2 ^ (prefixWord ++ tailWord_2051266).sum := by decide
  have hdescent : baseEnd_2051266 < baseStart_2051266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051322 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 8]
def baseStart_2051322 : Nat := 118140960795 + 2051322 * 2 ^ 59
def prefixEnd_2051322 : Nat := 4983230072969 + 3 ^ 40 * 2051322 * 2
def baseEnd_2051322 : Nat := 234069814031628539320255

theorem tailTrace_2051322 : CollatzResearch.WordTrace tailWord_2051322 prefixEnd_2051322 234069814031628539320255 := by
  unfold tailWord_2051322
  simp only [CollatzResearch.WordTrace]
  refine ⟨18704464968604551687721055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49878573249612137833922813 18704464968604551687721055)
  ·
    refine ⟨28056697452906827531581583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18704464968604551687721055 28056697452906827531581583)
    ·
      refine ⟨42085046179360241297372375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28056697452906827531581583 42085046179360241297372375)
      ·
        refine ⟨63127569269040361946058563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42085046179360241297372375 63127569269040361946058563)
        ·
          refine ⟨94691353903560542919087845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63127569269040361946058563 94691353903560542919087845)
          ·
            refine ⟨17754628856917601797328971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94691353903560542919087845 17754628856917601797328971)
            ·
              refine ⟨26631943285376402695993457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17754628856917601797328971 26631943285376402695993457)
              ·
                refine ⟨19973957464032302021995093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26631943285376402695993457 19973957464032302021995093)
                ·
                  refine ⟨234069814031628539320255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19973957464032302021995093 234069814031628539320255)
                  ·
                    rfl

theorem cell22_2051322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_2051322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051322 prefixEnd_2051322 := by exact prefixLift 2051322
  have htrace : WordTrace (prefixWord ++ tailWord_2051322) baseStart_2051322 baseEnd_2051322 := by
    simpa [prefixWord, tailWord_2051322, baseEnd_2051322] using wordTrace_append hprefix tailTrace_2051322
  have hstable : (prefixWord ++ tailWord_2051322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051322).length < 2 ^ (prefixWord ++ tailWord_2051322).sum := by decide
  have hdescent : baseEnd_2051322 < baseStart_2051322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051339 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 6]
def baseStart_2051339 : Nat := 118140960795 + 2051339 * 2 ^ 59
def prefixEnd_2051339 : Nat := 4983230072969 + 3 ^ 40 * 2051339 * 2
def baseEnd_2051339 : Nat := 234071753847434413428571

theorem tailTrace_2051339 : CollatzResearch.WordTrace tailWord_2051339 prefixEnd_2051339 234071753847434413428571 := by
  unfold tailWord_2051339
  simp only [CollatzResearch.WordTrace]
  refine ⟨74818479915356618654253071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49878986610237745769502047 74818479915356618654253071)
  ·
    refine ⟨112227719873034927981379607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74818479915356618654253071 112227719873034927981379607)
    ·
      refine ⟨168341579809552391972069411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112227719873034927981379607 168341579809552391972069411)
      ·
        refine ⟨252512369714328587958104117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168341579809552391972069411 252512369714328587958104117)
        ·
          refine ⟨23673034660718305121072261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252512369714328587958104117 23673034660718305121072261)
          ·
            refine ⟨4438693998884682210201049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23673034660718305121072261 4438693998884682210201049)
            ·
              refine ⟨3329020499163511657650787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4438693998884682210201049 3329020499163511657650787)
              ·
                refine ⟨4993530748745267486476181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329020499163511657650787 4993530748745267486476181)
                ·
                  refine ⟨234071753847434413428571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4993530748745267486476181 234071753847434413428571)
                  ·
                    rfl

theorem cell22_2051339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 6].length) (baseStart_2051339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051339 prefixEnd_2051339 := by exact prefixLift 2051339
  have htrace : WordTrace (prefixWord ++ tailWord_2051339) baseStart_2051339 baseEnd_2051339 := by
    simpa [prefixWord, tailWord_2051339, baseEnd_2051339] using wordTrace_append hprefix tailTrace_2051339
  have hstable : (prefixWord ++ tailWord_2051339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051339).length < 2 ^ (prefixWord ++ tailWord_2051339).sum := by decide
  have hdescent : baseEnd_2051339 < baseStart_2051339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051542 : List Nat := [5, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2051542 : Nat := 118140960795 + 2051542 * 2 ^ 59
def prefixEnd_2051542 : Nat := 4983230072969 + 3 ^ 40 * 2051542 * 2
def baseEnd_2051542 : Nat := 234094917530292792486697

theorem tailTrace_2051542 : CollatzResearch.WordTrace tailWord_2051542 prefixEnd_2051542 234094917530292792486697 := by
  unfold tailWord_2051542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4676617745851324020243305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49883922622414122882595253 4676617745851324020243305)
  ·
    refine ⟨3507463309388493015182479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4676617745851324020243305 3507463309388493015182479)
    ·
      refine ⟨5261194964082739522773719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3507463309388493015182479 5261194964082739522773719)
      ·
        refine ⟨7891792446124109284160579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5261194964082739522773719 7891792446124109284160579)
        ·
          refine ⟨11837688669186163926240869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7891792446124109284160579 11837688669186163926240869)
          ·
            refine ⟨2219566625472405736170163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11837688669186163926240869 2219566625472405736170163)
            ·
              refine ⟨3329349938208608604255245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2219566625472405736170163 3329349938208608604255245)
              ·
                refine ⟨1248506226828228226595717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3329349938208608604255245 1248506226828228226595717)
                ·
                  refine ⟨234094917530292792486697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1248506226828228226595717 234094917530292792486697)
                  ·
                    rfl

theorem cell22_2051542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2051542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051542 prefixEnd_2051542 := by exact prefixLift 2051542
  have htrace : WordTrace (prefixWord ++ tailWord_2051542) baseStart_2051542 baseEnd_2051542 := by
    simpa [prefixWord, tailWord_2051542, baseEnd_2051542] using wordTrace_append hprefix tailTrace_2051542
  have hstable : (prefixWord ++ tailWord_2051542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051542).length < 2 ^ (prefixWord ++ tailWord_2051542).sum := by decide
  have hdescent : baseEnd_2051542 < baseStart_2051542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051566 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2051566 : Nat := 118140960795 + 2051566 * 2 ^ 59
def prefixEnd_2051566 : Nat := 4983230072969 + 3 ^ 40 * 2051566 * 2
def baseEnd_2051566 : Nat := 702292968281350314860017

theorem tailTrace_2051566 : CollatzResearch.WordTrace tailWord_2051566 prefixEnd_2051566 702292968281350314860017 := by
  unfold tailWord_2051566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9353344910691779552845819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49884506190356157615177701 9353344910691779552845819)
  ·
    refine ⟨14030017366037669329268729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9353344910691779552845819 14030017366037669329268729)
    ·
      refine ⟨10522513024528251996951547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14030017366037669329268729 10522513024528251996951547)
      ·
        refine ⟨15783769536792377995427321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10522513024528251996951547 15783769536792377995427321)
        ·
          refine ⟨11837827152594283496570491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15783769536792377995427321 11837827152594283496570491)
          ·
            refine ⟨17756740728891425244855737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11837827152594283496570491 17756740728891425244855737)
            ·
              refine ⟨13317555546668568933641803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17756740728891425244855737 13317555546668568933641803)
              ·
                refine ⟨19976333320002853400462705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13317555546668568933641803 19976333320002853400462705)
                ·
                  refine ⟨14982249990002140050347029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19976333320002853400462705 14982249990002140050347029)
                  ·
                    refine ⟨702292968281350314860017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14982249990002140050347029 702292968281350314860017)
                    ·
                      rfl

theorem cell22_2051566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2051566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051566 prefixEnd_2051566 := by exact prefixLift 2051566
  have htrace : WordTrace (prefixWord ++ tailWord_2051566) baseStart_2051566 baseEnd_2051566 := by
    simpa [prefixWord, tailWord_2051566, baseEnd_2051566] using wordTrace_append hprefix tailTrace_2051566
  have hstable : (prefixWord ++ tailWord_2051566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051566).length < 2 ^ (prefixWord ++ tailWord_2051566).sum := by decide
  have hdescent : baseEnd_2051566 < baseStart_2051566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051568 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 3, 3]
def baseStart_2051568 : Nat := 118140960795 + 2051568 * 2 ^ 59
def prefixEnd_2051568 : Nat := 4983230072969 + 3 ^ 40 * 2051568 * 2
def baseEnd_2051568 : Nat := 702293652922222976310011

theorem tailTrace_2051568 : CollatzResearch.WordTrace tailWord_2051568 prefixEnd_2051568 702293652922222976310011 := by
  unfold tailWord_2051568
  simp only [CollatzResearch.WordTrace]
  refine ⟨37413416115763495382169679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49884554821017993842892905 37413416115763495382169679)
  ·
    refine ⟨56120124173645243073254519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37413416115763495382169679 56120124173645243073254519)
    ·
      refine ⟨84180186260467864609881779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56120124173645243073254519 84180186260467864609881779)
      ·
        refine ⟨126270279390701796914822669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84180186260467864609881779 126270279390701796914822669)
        ·
          refine ⟨47351354771513173843058501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126270279390701796914822669 47351354771513173843058501)
          ·
            refine ⟨8878379019658720095573469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47351354771513173843058501 8878379019658720095573469)
            ·
              refine ⟨3329392132372020035840051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8878379019658720095573469 3329392132372020035840051)
              ·
                refine ⟨4994088198558030053760077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329392132372020035840051 4994088198558030053760077)
                ·
                  refine ⟨1872783074459261270160029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4994088198558030053760077 1872783074459261270160029)
                  ·
                    refine ⟨702293652922222976310011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1872783074459261270160029 702293652922222976310011)
                    ·
                      rfl

theorem cell22_2051568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 3, 3].length) (baseStart_2051568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051568 prefixEnd_2051568 := by exact prefixLift 2051568
  have htrace : WordTrace (prefixWord ++ tailWord_2051568) baseStart_2051568 baseEnd_2051568 := by
    simpa [prefixWord, tailWord_2051568, baseEnd_2051568] using wordTrace_append hprefix tailTrace_2051568
  have hstable : (prefixWord ++ tailWord_2051568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051568).length < 2 ^ (prefixWord ++ tailWord_2051568).sum := by decide
  have hdescent : baseEnd_2051568 < baseStart_2051568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051619 : List Nat := [1, 1, 1, 4, 5, 2, 2, 2, 1, 3]
def baseStart_2051619 : Nat := 118140960795 + 2051619 * 2 ^ 59
def prefixEnd_2051619 : Nat := 4983230072969 + 3 ^ 40 * 2051619 * 2
def baseEnd_2051619 : Nat := 702311111264475843284855

theorem tailTrace_2051619 : CollatzResearch.WordTrace tailWord_2051619 prefixEnd_2051619 702311111264475843284855 := by
  unfold tailWord_2051619
  simp only [CollatzResearch.WordTrace]
  refine ⟨74828692354342226474445911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49885794902894817649630607 74828692354342226474445911)
  ·
    refine ⟨112243038531513339711668867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74828692354342226474445911 112243038531513339711668867)
    ·
      refine ⟨168364557797270009567503301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112243038531513339711668867 168364557797270009567503301)
      ·
        refine ⟨31568354586988126793906869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168364557797270009567503301 31568354586988126793906869)
        ·
          refine ⟨2959533242530136886928769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31568354586988126793906869 2959533242530136886928769)
          ·
            refine ⟨2219649931897602665196577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2959533242530136886928769 2219649931897602665196577)
            ·
              refine ⟨1664737448923201998897433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219649931897602665196577 1664737448923201998897433)
              ·
                refine ⟨1248553086692401499173075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664737448923201998897433 1248553086692401499173075)
                ·
                  refine ⟨1872829630038602248759613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248553086692401499173075 1872829630038602248759613)
                  ·
                    refine ⟨702311111264475843284855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1872829630038602248759613 702311111264475843284855)
                    ·
                      rfl

theorem cell22_2051619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 1, 3].length) (baseStart_2051619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051619 prefixEnd_2051619 := by exact prefixLift 2051619
  have htrace : WordTrace (prefixWord ++ tailWord_2051619) baseStart_2051619 baseEnd_2051619 := by
    simpa [prefixWord, tailWord_2051619, baseEnd_2051619] using wordTrace_append hprefix tailTrace_2051619
  have hstable : (prefixWord ++ tailWord_2051619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051619).length < 2 ^ (prefixWord ++ tailWord_2051619).sum := by decide
  have hdescent : baseEnd_2051619 < baseStart_2051619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051658 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 4, 3]
def baseStart_2051658 : Nat := 118140960795 + 2051658 * 2 ^ 59
def prefixEnd_2051658 : Nat := 4983230072969 + 3 ^ 40 * 2051658 * 2
def baseEnd_2051658 : Nat := 702324461761492741559735

theorem tailTrace_2051658 : CollatzResearch.WordTrace tailWord_2051658 prefixEnd_2051658 702324461761492741559735 := by
  unfold tailWord_2051658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18707528700300234033778907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49886743200800624090077085 18707528700300234033778907)
  ·
    refine ⟨28061293050450351050668361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18707528700300234033778907 28061293050450351050668361)
    ·
      refine ⟨21045969787837763288001271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28061293050450351050668361 21045969787837763288001271)
      ·
        refine ⟨31568954681756644932001907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21045969787837763288001271 31568954681756644932001907)
        ·
          refine ⟨47353432022634967398002861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31568954681756644932001907 47353432022634967398002861)
          ·
            refine ⟨17757537008488112774251073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47353432022634967398002861 17757537008488112774251073)
            ·
              refine ⟨13318152756366084580688305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17757537008488112774251073 13318152756366084580688305)
              ·
                refine ⟨9988614567274563435516229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13318152756366084580688305 9988614567274563435516229)
                ·
                  refine ⟨1872865231363980644159293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9988614567274563435516229 1872865231363980644159293)
                  ·
                    refine ⟨702324461761492741559735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1872865231363980644159293 702324461761492741559735)
                    ·
                      rfl

theorem cell22_2051658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_2051658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051658 prefixEnd_2051658 := by exact prefixLift 2051658
  have htrace : WordTrace (prefixWord ++ tailWord_2051658) baseStart_2051658 baseEnd_2051658 := by
    simpa [prefixWord, tailWord_2051658, baseEnd_2051658] using wordTrace_append hprefix tailTrace_2051658
  have hstable : (prefixWord ++ tailWord_2051658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051658).length < 2 ^ (prefixWord ++ tailWord_2051658).sum := by decide
  have hdescent : baseEnd_2051658 < baseStart_2051658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051660 : List Nat := [2, 2, 1, 3, 1, 4, 2, 3, 4]
def baseStart_2051660 : Nat := 118140960795 + 2051660 * 2 ^ 59
def prefixEnd_2051660 : Nat := 4983230072969 + 3 ^ 40 * 2051660 * 2
def baseEnd_2051660 : Nat := 234108382134121801003243

theorem tailTrace_2051660 : CollatzResearch.WordTrace tailWord_2051660 prefixEnd_2051660 234108382134121801003243 := by
  unfold tailWord_2051660
  simp only [CollatzResearch.WordTrace]
  refine ⟨37415093873596845238344217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49886791831462460317792289 37415093873596845238344217)
  ·
    refine ⟨28061320405197633928758163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37415093873596845238344217 28061320405197633928758163)
    ·
      refine ⟨42091980607796450893137245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28061320405197633928758163 42091980607796450893137245)
      ·
        refine ⟨15784492727923669084926467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42091980607796450893137245 15784492727923669084926467)
        ·
          refine ⟨23676739091885503627389701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15784492727923669084926467 23676739091885503627389701)
          ·
            refine ⟨4439388579728531930135569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23676739091885503627389701 4439388579728531930135569)
            ·
              refine ⟨3329541434796398947601677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4439388579728531930135569 3329541434796398947601677)
              ·
                refine ⟨1248578038048649605350629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3329541434796398947601677 1248578038048649605350629)
                ·
                  refine ⟨234108382134121801003243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1248578038048649605350629 234108382134121801003243)
                  ·
                    rfl

theorem cell22_2051660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_2051660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051660 prefixEnd_2051660 := by exact prefixLift 2051660
  have htrace : WordTrace (prefixWord ++ tailWord_2051660) baseStart_2051660 baseEnd_2051660 := by
    simpa [prefixWord, tailWord_2051660, baseEnd_2051660] using wordTrace_append hprefix tailTrace_2051660
  have hstable : (prefixWord ++ tailWord_2051660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051660).length < 2 ^ (prefixWord ++ tailWord_2051660).sum := by decide
  have hdescent : baseEnd_2051660 < baseStart_2051660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051671 : List Nat := [1, 1, 3, 2, 2, 4, 9]
def baseStart_2051671 : Nat := 118140960795 + 2051671 * 2 ^ 59
def prefixEnd_2051671 : Nat := 4983230072969 + 3 ^ 40 * 2051671 * 2
def baseEnd_2051671 : Nat := 26012181923228334851285

theorem tailTrace_2051671 : CollatzResearch.WordTrace tailWord_2051671 prefixEnd_2051671 26012181923228334851285 := by
  unfold tailWord_2051671
  simp only [CollatzResearch.WordTrace]
  refine ⟨74830588950153839355338867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49887059300102559570225911 74830588950153839355338867)
  ·
    refine ⟨112245883425230759033008301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74830588950153839355338867 112245883425230759033008301)
    ·
      refine ⟨42092206284461534637378113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112245883425230759033008301 42092206284461534637378113)
      ·
        refine ⟨31569154713346150978033585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42092206284461534637378113 31569154713346150978033585)
        ·
          refine ⟨23676866035009613233525189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31569154713346150978033585 23676866035009613233525189)
          ·
            refine ⟨4439412381564302481285973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23676866035009613233525189 4439412381564302481285973)
            ·
              refine ⟨26012181923228334851285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4439412381564302481285973 26012181923228334851285)
              ·
                rfl

theorem cell22_2051671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 9].length) (baseStart_2051671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051671 prefixEnd_2051671 := by exact prefixLift 2051671
  have htrace : WordTrace (prefixWord ++ tailWord_2051671) baseStart_2051671 baseEnd_2051671 := by
    simpa [prefixWord, tailWord_2051671, baseEnd_2051671] using wordTrace_append hprefix tailTrace_2051671
  have hstable : (prefixWord ++ tailWord_2051671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051671).length < 2 ^ (prefixWord ++ tailWord_2051671).sum := by decide
  have hdescent : baseEnd_2051671 < baseStart_2051671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051677 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 6]
def baseStart_2051677 : Nat := 118140960795 + 2051677 * 2 ^ 59
def prefixEnd_2051677 : Nat := 4983230072969 + 3 ^ 40 * 2051677 * 2
def baseEnd_2051677 : Nat := 234110321949927675111559

theorem tailTrace_2051677 : CollatzResearch.WordTrace tailWord_2051677 prefixEnd_2051677 234110321949927675111559 := by
  unfold tailWord_2051677
  simp only [CollatzResearch.WordTrace]
  refine ⟨74830807788132102380057285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49887205192088068253371523 74830807788132102380057285)
  ·
    refine ⟨14030776460274769196260741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74830807788132102380057285 14030776460274769196260741)
    ·
      refine ⟨2630770586301519224298889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14030776460274769196260741 2630770586301519224298889)
      ·
        refine ⟨1973077939726139418224167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2630770586301519224298889 1973077939726139418224167)
        ·
          refine ⟨2959616909589209127336251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973077939726139418224167 2959616909589209127336251)
          ·
            refine ⟨4439425364383813691004377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959616909589209127336251 4439425364383813691004377)
            ·
              refine ⟨3329569023287860268253283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4439425364383813691004377 3329569023287860268253283)
              ·
                refine ⟨4994353534931790402379925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329569023287860268253283 4994353534931790402379925)
                ·
                  refine ⟨234110321949927675111559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4994353534931790402379925 234110321949927675111559)
                  ·
                    rfl

theorem cell22_2051677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_2051677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051677 prefixEnd_2051677 := by exact prefixLift 2051677
  have htrace : WordTrace (prefixWord ++ tailWord_2051677) baseStart_2051677 baseEnd_2051677 := by
    simpa [prefixWord, tailWord_2051677, baseEnd_2051677] using wordTrace_append hprefix tailTrace_2051677
  have hstable : (prefixWord ++ tailWord_2051677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051677).length < 2 ^ (prefixWord ++ tailWord_2051677).sum := by decide
  have hdescent : baseEnd_2051677 < baseStart_2051677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051763 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 3, 4]
def baseStart_2051763 : Nat := 118140960795 + 2051763 * 2 ^ 59
def prefixEnd_2051763 : Nat := 4983230072969 + 3 ^ 40 * 2051763 * 2
def baseEnd_2051763 : Nat := 702360405407307467684413

theorem tailTrace_2051763 : CollatzResearch.WordTrace tailWord_2051763 prefixEnd_2051763 702360405407307467684413 := by
  unfold tailWord_2051763
  simp only [CollatzResearch.WordTrace]
  refine ⟨74833944465820539067687943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49889296310547026045125295 74833944465820539067687943)
  ·
    refine ⟨112250916698730808601531915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74833944465820539067687943 112250916698730808601531915)
    ·
      refine ⟨168376375048096212902297873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112250916698730808601531915 168376375048096212902297873)
      ·
        refine ⟨126282281286072159676723405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168376375048096212902297873 126282281286072159676723405)
        ·
          refine ⟨47355855482277059878771277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126282281286072159676723405 47355855482277059878771277)
          ·
            refine ⟨17758445805853897454539229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47355855482277059878771277 17758445805853897454539229)
            ·
              refine ⟨6659417177195211545452211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17758445805853897454539229 6659417177195211545452211)
              ·
                refine ⟨9989125765792817318178317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659417177195211545452211 9989125765792817318178317)
                ·
                  refine ⟨3745922162172306494316869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9989125765792817318178317 3745922162172306494316869)
                  ·
                    refine ⟨702360405407307467684413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3745922162172306494316869 702360405407307467684413)
                    ·
                      rfl

theorem cell22_2051763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 4].length) (baseStart_2051763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051763 prefixEnd_2051763 := by exact prefixLift 2051763
  have htrace : WordTrace (prefixWord ++ tailWord_2051763) baseStart_2051763 baseEnd_2051763 := by
    simpa [prefixWord, tailWord_2051763, baseEnd_2051763] using wordTrace_append hprefix tailTrace_2051763
  have hstable : (prefixWord ++ tailWord_2051763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051763).length < 2 ^ (prefixWord ++ tailWord_2051763).sum := by decide
  have hdescent : baseEnd_2051763 < baseStart_2051763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051788 : List Nat := [2, 2, 1, 5, 3, 1, 2, 2, 1, 3]
def baseStart_2051788 : Nat := 118140960795 + 2051788 * 2 ^ 59
def prefixEnd_2051788 : Nat := 4983230072969 + 3 ^ 40 * 2051788 * 2
def baseEnd_2051788 : Nat := 702368963418215735809337

theorem tailTrace_2051788 : CollatzResearch.WordTrace tailWord_2051788 prefixEnd_2051788 702368963418215735809337 := by
  unfold tailWord_2051788
  simp only [CollatzResearch.WordTrace]
  refine ⟨37417428145364984168674009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49889904193819978891565345 37417428145364984168674009)
  ·
    refine ⟨28063071109023738126505507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37417428145364984168674009 28063071109023738126505507)
    ·
      refine ⟨42094606663535607189758261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28063071109023738126505507 42094606663535607189758261)
      ·
        refine ⟨3946369374706463174039837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42094606663535607189758261 3946369374706463174039837)
        ·
          refine ⟨1479888515514923690264939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3946369374706463174039837 1479888515514923690264939)
          ·
            refine ⟨2219832773272385535397409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479888515514923690264939 2219832773272385535397409)
            ·
              refine ⟨1664874579954289151548057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219832773272385535397409 1664874579954289151548057)
              ·
                refine ⟨1248655934965716863661043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664874579954289151548057 1248655934965716863661043)
                ·
                  refine ⟨1872983902448575295491565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248655934965716863661043 1872983902448575295491565)
                  ·
                    refine ⟨702368963418215735809337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1872983902448575295491565 702368963418215735809337)
                    ·
                      rfl

theorem cell22_2051788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_2051788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051788 prefixEnd_2051788 := by exact prefixLift 2051788
  have htrace : WordTrace (prefixWord ++ tailWord_2051788) baseStart_2051788 baseEnd_2051788 := by
    simpa [prefixWord, tailWord_2051788, baseEnd_2051788] using wordTrace_append hprefix tailTrace_2051788
  have hstable : (prefixWord ++ tailWord_2051788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051788).length < 2 ^ (prefixWord ++ tailWord_2051788).sum := by decide
  have hdescent : baseEnd_2051788 < baseStart_2051788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051808 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 4, 4]
def baseStart_2051808 : Nat := 118140960795 + 2051808 * 2 ^ 59
def prefixEnd_2051808 : Nat := 4983230072969 + 3 ^ 40 * 2051808 * 2
def baseEnd_2051808 : Nat := 702375809826942350309275

theorem tailTrace_2051808 : CollatzResearch.WordTrace tailWord_2051808 prefixEnd_2051808 702375809826942350309275 := by
  unfold tailWord_2051808
  simp only [CollatzResearch.WordTrace]
  refine ⟨37417792875328755876538039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49890390500438341168717385 37417792875328755876538039)
  ·
    refine ⟨56126689312993133814807059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37417792875328755876538039 56126689312993133814807059)
    ·
      refine ⟨84190033969489700722210589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56126689312993133814807059 84190033969489700722210589)
      ·
        refine ⟨31571262738558637770828971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84190033969489700722210589 31571262738558637770828971)
        ·
          refine ⟨47356894107837956656243457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31571262738558637770828971 47356894107837956656243457)
          ·
            refine ⟨35517670580878467492182593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47356894107837956656243457 35517670580878467492182593)
            ·
              refine ⟨26638252935658850619136945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35517670580878467492182593 26638252935658850619136945)
              ·
                refine ⟨19978689701744137964352709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26638252935658850619136945 19978689701744137964352709)
                ·
                  refine ⟨3746004319077025868316133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19978689701744137964352709 3746004319077025868316133)
                  ·
                    refine ⟨702375809826942350309275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3746004319077025868316133 702375809826942350309275)
                    ·
                      rfl

theorem cell22_2051808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_2051808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051808 prefixEnd_2051808 := by exact prefixLift 2051808
  have htrace : WordTrace (prefixWord ++ tailWord_2051808) baseStart_2051808 baseEnd_2051808 := by
    simpa [prefixWord, tailWord_2051808, baseEnd_2051808] using wordTrace_append hprefix tailTrace_2051808
  have hstable : (prefixWord ++ tailWord_2051808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051808).length < 2 ^ (prefixWord ++ tailWord_2051808).sum := by decide
  have hdescent : baseEnd_2051808 < baseStart_2051808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051825 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 2, 4]
def baseStart_2051825 : Nat := 118140960795 + 2051825 * 2 ^ 59
def prefixEnd_2051825 : Nat := 4983230072969 + 3 ^ 40 * 2051825 * 2
def baseEnd_2051825 : Nat := 702381629274359972634223

theorem tailTrace_2051825 : CollatzResearch.WordTrace tailWord_2051825 prefixEnd_2051825 702381629274359972634223 := by
  unfold tailWord_2051825
  simp only [CollatzResearch.WordTrace]
  refine ⟨74836205791595923656444929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49890803861063949104296619 74836205791595923656444929)
  ·
    refine ⟨56127154343696942742333697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74836205791595923656444929 56127154343696942742333697)
    ·
      refine ⟨42095365757772707056750273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56127154343696942742333697 42095365757772707056750273)
      ·
        refine ⟨31571524318329530292562705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42095365757772707056750273 31571524318329530292562705)
        ·
          refine ⟨23678643238747147719422029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31571524318329530292562705 23678643238747147719422029)
          ·
            refine ⟨8879491214530180394783261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23678643238747147719422029 8879491214530180394783261)
            ·
              refine ⟨3329809205448817648043723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8879491214530180394783261 3329809205448817648043723)
              ·
                refine ⟨4994713808173226472065585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329809205448817648043723 4994713808173226472065585)
                ·
                  refine ⟨3746035356129919854049189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4994713808173226472065585 3746035356129919854049189)
                  ·
                    refine ⟨702381629274359972634223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3746035356129919854049189 702381629274359972634223)
                    ·
                      rfl

theorem cell22_2051825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_2051825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051825 prefixEnd_2051825 := by exact prefixLift 2051825
  have htrace : WordTrace (prefixWord ++ tailWord_2051825) baseStart_2051825 baseEnd_2051825 := by
    simpa [prefixWord, tailWord_2051825, baseEnd_2051825] using wordTrace_append hprefix tailTrace_2051825
  have hstable : (prefixWord ++ tailWord_2051825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051825).length < 2 ^ (prefixWord ++ tailWord_2051825).sum := by decide
  have hdescent : baseEnd_2051825 < baseStart_2051825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051844 : List Nat := [2, 3, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_2051844 : Nat := 118140960795 + 2051844 * 2 ^ 59
def prefixEnd_2051844 : Nat := 4983230072969 + 3 ^ 40 * 2051844 * 2
def baseEnd_2051844 : Nat := 702388133362650256409165

theorem tailTrace_2051844 : CollatzResearch.WordTrace tailWord_2051844 prefixEnd_2051844 702388133362650256409165 := by
  unfold tailWord_2051844
  simp only [CollatzResearch.WordTrace]
  refine ⟨37418449389263544950693293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49891265852351393267591057 37418449389263544950693293)
  ·
    refine ⟨14031918520973829356509985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37418449389263544950693293 14031918520973829356509985)
    ·
      refine ⟨10523938890730372017382489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14031918520973829356509985 10523938890730372017382489)
      ·
        refine ⟨7892954168047779013036867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10523938890730372017382489 7892954168047779013036867)
        ·
          refine ⟨11839431252071668519555301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7892954168047779013036867 11839431252071668519555301)
          ·
            refine ⟨2219893359763437847416619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11839431252071668519555301 2219893359763437847416619)
            ·
              refine ⟨3329840039645156771124929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2219893359763437847416619 3329840039645156771124929)
              ·
                refine ⟨2497380029733867578343697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3329840039645156771124929 2497380029733867578343697)
                ·
                  refine ⟨1873035022300400683757773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2497380029733867578343697 1873035022300400683757773)
                  ·
                    refine ⟨702388133362650256409165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1873035022300400683757773 702388133362650256409165)
                    ·
                      rfl

theorem cell22_2051844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_2051844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051844 prefixEnd_2051844 := by exact prefixLift 2051844
  have htrace : WordTrace (prefixWord ++ tailWord_2051844) baseStart_2051844 baseEnd_2051844 := by
    simpa [prefixWord, tailWord_2051844, baseEnd_2051844] using wordTrace_append hprefix tailTrace_2051844
  have hstable : (prefixWord ++ tailWord_2051844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051844).length < 2 ^ (prefixWord ++ tailWord_2051844).sum := by decide
  have hdescent : baseEnd_2051844 < baseStart_2051844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051889 : List Nat := [1, 2, 2, 3, 2, 2, 3, 3, 1, 3]
def baseStart_2051889 : Nat := 118140960795 + 2051889 * 2 ^ 59
def prefixEnd_2051889 : Nat := 4983230072969 + 3 ^ 40 * 2051889 * 2
def baseEnd_2051889 : Nat := 702403537782285139034027

theorem tailTrace_2051889 : CollatzResearch.WordTrace tailWord_2051889 prefixEnd_2051889 702403537782285139034027 := by
  unfold tailWord_2051889
  simp only [CollatzResearch.WordTrace]
  refine ⟨74838540063364062586774721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49892360042242708391183147 74838540063364062586774721)
  ·
    refine ⟨56128905047523046940081041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74838540063364062586774721 56128905047523046940081041)
    ·
      refine ⟨42096678785642285205060781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56128905047523046940081041 42096678785642285205060781)
      ·
        refine ⟨15786254544615856951897793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42096678785642285205060781 15786254544615856951897793)
        ·
          refine ⟨11839690908461892713923345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15786254544615856951897793 11839690908461892713923345)
          ·
            refine ⟨8879768181346419535442509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11839690908461892713923345 8879768181346419535442509)
            ·
              refine ⟨3329913068004907325790941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8879768181346419535442509 3329913068004907325790941)
              ·
                refine ⟨1248717400501840247171603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3329913068004907325790941 1248717400501840247171603)
                ·
                  refine ⟨1873076100752760370757405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248717400501840247171603 1873076100752760370757405)
                  ·
                    refine ⟨702403537782285139034027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1873076100752760370757405 702403537782285139034027)
                    ·
                      rfl

theorem cell22_2051889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_2051889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051889 prefixEnd_2051889 := by exact prefixLift 2051889
  have htrace : WordTrace (prefixWord ++ tailWord_2051889) baseStart_2051889 baseEnd_2051889 := by
    simpa [prefixWord, tailWord_2051889, baseEnd_2051889] using wordTrace_append hprefix tailTrace_2051889
  have hstable : (prefixWord ++ tailWord_2051889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051889).length < 2 ^ (prefixWord ++ tailWord_2051889).sum := by decide
  have hdescent : baseEnd_2051889 < baseStart_2051889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051945 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 6, 3]
def baseStart_2051945 : Nat := 118140960795 + 2051945 * 2 ^ 59
def prefixEnd_2051945 : Nat := 4983230072969 + 3 ^ 40 * 2051945 * 2
def baseEnd_2051945 : Nat := 702422707726719659633855

theorem tailTrace_2051945 : CollatzResearch.WordTrace tailWord_2051945 prefixEnd_2051945 702422707726719659633855 := by
  unfold tailWord_2051945
  simp only [CollatzResearch.WordTrace]
  refine ⟨74840582551161184150813289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49893721700774122767208859 74840582551161184150813289)
  ·
    refine ⟨56130436913370888113109967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74840582551161184150813289 56130436913370888113109967)
    ·
      refine ⟨84195655370056332169664951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56130436913370888113109967 84195655370056332169664951)
      ·
        refine ⟨126293483055084498254497427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84195655370056332169664951 126293483055084498254497427)
        ·
          refine ⟨189440224582626747381746141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126293483055084498254497427 189440224582626747381746141)
          ·
            refine ⟨71040084218485030268154803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189440224582626747381746141 71040084218485030268154803)
            ·
              refine ⟨106560126327727545402232205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71040084218485030268154803 106560126327727545402232205)
              ·
                refine ⟨39960047372897829525837077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106560126327727545402232205 39960047372897829525837077)
                ·
                  refine ⟨1873127220604585759023613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39960047372897829525837077 1873127220604585759023613)
                  ·
                    refine ⟨702422707726719659633855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1873127220604585759023613 702422707726719659633855)
                    ·
                      rfl

theorem cell22_2051945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 3].length) (baseStart_2051945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051945 prefixEnd_2051945 := by exact prefixLift 2051945
  have htrace : WordTrace (prefixWord ++ tailWord_2051945) baseStart_2051945 baseEnd_2051945 := by
    simpa [prefixWord, tailWord_2051945, baseEnd_2051945] using wordTrace_append hprefix tailTrace_2051945
  have hstable : (prefixWord ++ tailWord_2051945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051945).length < 2 ^ (prefixWord ++ tailWord_2051945).sum := by decide
  have hdescent : baseEnd_2051945 < baseStart_2051945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051962 : List Nat := [3, 1, 1, 1, 1, 1, 5, 4, 2, 3]
def baseStart_2051962 : Nat := 118140960795 + 2051962 * 2 ^ 59
def prefixEnd_2051962 : Nat := 4983230072969 + 3 ^ 40 * 2051962 * 2
def baseEnd_2051962 : Nat := 702428527174137281958803

theorem tailTrace_2051962 : CollatzResearch.WordTrace tailWord_2051962 prefixEnd_2051962 702428527174137281958803 := by
  unfold tailWord_2051962
  simp only [CollatzResearch.WordTrace]
  refine ⟨18710300648024899013545535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49894135061399730702788093 18710300648024899013545535)
  ·
    refine ⟨28065450972037348520318303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18710300648024899013545535 28065450972037348520318303)
    ·
      refine ⟨42098176458056022780477455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28065450972037348520318303 42098176458056022780477455)
      ·
        refine ⟨63147264687084034170716183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42098176458056022780477455 63147264687084034170716183)
        ·
          refine ⟨94720897030626051256074275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63147264687084034170716183 94720897030626051256074275)
          ·
            refine ⟨142081345545939076884111413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94720897030626051256074275 142081345545939076884111413)
            ·
              refine ⟨13320126144931788457885445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142081345545939076884111413 13320126144931788457885445)
              ·
                refine ⟨2497523652174710335853521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13320126144931788457885445 2497523652174710335853521)
                ·
                  refine ⟨1873142739131032751890141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2497523652174710335853521 1873142739131032751890141)
                  ·
                    refine ⟨702428527174137281958803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1873142739131032751890141 702428527174137281958803)
                    ·
                      rfl

theorem cell22_2051962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_2051962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051962 prefixEnd_2051962 := by exact prefixLift 2051962
  have htrace : WordTrace (prefixWord ++ tailWord_2051962) baseStart_2051962 baseEnd_2051962 := by
    simpa [prefixWord, tailWord_2051962, baseEnd_2051962] using wordTrace_append hprefix tailTrace_2051962
  have hstable : (prefixWord ++ tailWord_2051962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051962).length < 2 ^ (prefixWord ++ tailWord_2051962).sum := by decide
  have hdescent : baseEnd_2051962 < baseStart_2051962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051994 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 2, 4]
def baseStart_2051994 : Nat := 118140960795 + 2051994 * 2 ^ 59
def prefixEnd_2051994 : Nat := 4983230072969 + 3 ^ 40 * 2051994 * 2
def baseEnd_2051994 : Nat := 702439481428099865158705

theorem tailTrace_2051994 : CollatzResearch.WordTrace tailWord_2051994 prefixEnd_2051994 702439481428099865158705 := by
  unfold tailWord_2051994
  simp only [CollatzResearch.WordTrace]
  refine ⟨18710592431995916379836759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49894913151989110346231357 18710592431995916379836759)
  ·
    refine ⟨28065888647993874569755139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18710592431995916379836759 28065888647993874569755139)
    ·
      refine ⟨42098832971990811854632709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28065888647993874569755139 42098832971990811854632709)
      ·
        refine ⟨7893531182248277222743633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42098832971990811854632709 7893531182248277222743633)
        ·
          refine ⟨5920148386686207917057725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7893531182248277222743633 5920148386686207917057725)
          ·
            refine ⟨2220055645007327968896647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5920148386686207917057725 2220055645007327968896647)
            ·
              refine ⟨3330083467510991953344971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220055645007327968896647 3330083467510991953344971)
              ·
                refine ⟨4995125201266487930017457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3330083467510991953344971 4995125201266487930017457)
                ·
                  refine ⟨3746343900949865947513093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4995125201266487930017457 3746343900949865947513093)
                  ·
                    refine ⟨702439481428099865158705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3746343900949865947513093 702439481428099865158705)
                    ·
                      rfl

theorem cell22_2051994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_2051994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051994 prefixEnd_2051994 := by exact prefixLift 2051994
  have htrace : WordTrace (prefixWord ++ tailWord_2051994) baseStart_2051994 baseEnd_2051994 := by
    simpa [prefixWord, tailWord_2051994, baseEnd_2051994] using wordTrace_append hprefix tailTrace_2051994
  have hstable : (prefixWord ++ tailWord_2051994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051994).length < 2 ^ (prefixWord ++ tailWord_2051994).sum := by decide
  have hdescent : baseEnd_2051994 < baseStart_2051994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051998 : List Nat := [4, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_2051998 : Nat := 118140960795 + 2051998 * 2 ^ 59
def prefixEnd_2051998 : Nat := 4983230072969 + 3 ^ 40 * 2051998 * 2
def baseEnd_2051998 : Nat := 234146950236615062686231

theorem tailTrace_2051998 : CollatzResearch.WordTrace tailWord_2051998 prefixEnd_2051998 234146950236615062686231 := by
  unfold tailWord_2051998
  simp only [CollatzResearch.WordTrace]
  refine ⟨9355314452496146775311581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49895010413312782801661765 9355314452496146775311581)
  ·
    refine ⟨3508242919686055040741843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9355314452496146775311581 3508242919686055040741843)
    ·
      refine ⟨5262364379529082561112765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3508242919686055040741843 5262364379529082561112765)
      ·
        refine ⟨1973386642323405960417287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5262364379529082561112765 1973386642323405960417287)
        ·
          refine ⟨2960079963485108940625931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973386642323405960417287 2960079963485108940625931)
          ·
            refine ⟨4440119945227663410938897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960079963485108940625931 4440119945227663410938897)
            ·
              refine ⟨3330089958920747558204173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4440119945227663410938897 3330089958920747558204173)
              ·
                refine ⟨1248783734595280334326565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3330089958920747558204173 1248783734595280334326565)
                ·
                  refine ⟨234146950236615062686231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1248783734595280334326565 234146950236615062686231)
                  ·
                    rfl

theorem cell22_2051998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_2051998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2051998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2051998 prefixEnd_2051998 := by exact prefixLift 2051998
  have htrace : WordTrace (prefixWord ++ tailWord_2051998) baseStart_2051998 baseEnd_2051998 := by
    simpa [prefixWord, tailWord_2051998, baseEnd_2051998] using wordTrace_append hprefix tailTrace_2051998
  have hstable : (prefixWord ++ tailWord_2051998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051998).length < 2 ^ (prefixWord ++ tailWord_2051998).sum := by decide
  have hdescent : baseEnd_2051998 < baseStart_2051998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052024 : List Nat := [2, 1, 2, 1, 2, 3, 1, 6, 1, 3]
def baseStart_2052024 : Nat := 118140960795 + 2052024 * 2 ^ 59
def prefixEnd_2052024 : Nat := 4983230072969 + 3 ^ 40 * 2052024 * 2
def baseEnd_2052024 : Nat := 702449751041189786908613

theorem tailTrace_2052024 : CollatzResearch.WordTrace tailWord_2052024 prefixEnd_2052024 702449751041189786908613 := by
  unfold tailWord_2052024
  simp only [CollatzResearch.WordTrace]
  refine ⟨37421731958937490321469563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49895642611916653761959417 37421731958937490321469563)
  ·
    refine ⟨56132597938406235482204345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37421731958937490321469563 56132597938406235482204345)
    ·
      refine ⟨42099448453804676611653259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56132597938406235482204345 42099448453804676611653259)
      ·
        refine ⟨63149172680707014917479889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42099448453804676611653259 63149172680707014917479889)
        ·
          refine ⟨47361879510530261188109917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63149172680707014917479889 47361879510530261188109917)
          ·
            refine ⟨17760704816448847945541219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47361879510530261188109917 17760704816448847945541219)
            ·
              refine ⟨26641057224673271918311829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17760704816448847945541219 26641057224673271918311829)
              ·
                refine ⟨1248799557406559621170867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26641057224673271918311829 1248799557406559621170867)
                ·
                  refine ⟨1873199336109839431756301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248799557406559621170867 1873199336109839431756301)
                  ·
                    refine ⟨702449751041189786908613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1873199336109839431756301 702449751041189786908613)
                    ·
                      rfl

theorem cell22_2052024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_2052024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052024 prefixEnd_2052024 := by exact prefixLift 2052024
  have htrace : WordTrace (prefixWord ++ tailWord_2052024) baseStart_2052024 baseEnd_2052024 := by
    simpa [prefixWord, tailWord_2052024, baseEnd_2052024] using wordTrace_append hprefix tailTrace_2052024
  have hstable : (prefixWord ++ tailWord_2052024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052024).length < 2 ^ (prefixWord ++ tailWord_2052024).sum := by decide
  have hdescent : baseEnd_2052024 < baseStart_2052024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052058 : List Nat := [3, 1, 1, 2, 5, 2, 1, 3, 1, 3]
def baseStart_2052058 : Nat := 118140960795 + 2052058 * 2 ^ 59
def prefixEnd_2052058 : Nat := 4983230072969 + 3 ^ 40 * 2052058 * 2
def baseEnd_2052058 : Nat := 702461389936025031558509

theorem tailTrace_2052058 : CollatzResearch.WordTrace tailWord_2052058 prefixEnd_2052058 702461389936025031558509 := by
  unfold tailWord_2052058
  simp only [CollatzResearch.WordTrace]
  refine ⟨18711175999937951112419207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49896469333167869633117885 18711175999937951112419207)
  ·
    refine ⟨28066763999906926668628811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18711175999937951112419207 28066763999906926668628811)
    ·
      refine ⟨42100145999860390002943217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28066763999906926668628811 42100145999860390002943217)
      ·
        refine ⟨31575109499895292502207413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42100145999860390002943217 31575109499895292502207413)
        ·
          refine ⟨2960166515615183672081945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31575109499895292502207413 2960166515615183672081945)
          ·
            refine ⟨2220124886711387754061459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2960166515615183672081945 2220124886711387754061459)
            ·
              refine ⟨3330187330067081631092189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220124886711387754061459 3330187330067081631092189)
              ·
                refine ⟨1248820248775155611659571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3330187330067081631092189 1248820248775155611659571)
                ·
                  refine ⟨1873230373162733417489357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248820248775155611659571 1873230373162733417489357)
                  ·
                    refine ⟨702461389936025031558509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1873230373162733417489357 702461389936025031558509)
                    ·
                      rfl

theorem cell22_2052058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_2052058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052058 prefixEnd_2052058 := by exact prefixLift 2052058
  have htrace : WordTrace (prefixWord ++ tailWord_2052058) baseStart_2052058 baseEnd_2052058 := by
    simpa [prefixWord, tailWord_2052058, baseEnd_2052058] using wordTrace_append hprefix tailTrace_2052058
  have hstable : (prefixWord ++ tailWord_2052058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052058).length < 2 ^ (prefixWord ++ tailWord_2052058).sum := by decide
  have hdescent : baseEnd_2052058 < baseStart_2052058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052065 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 8]
def baseStart_2052065 : Nat := 118140960795 + 2052065 * 2 ^ 59
def prefixEnd_2052065 : Nat := 4983230072969 + 3 ^ 40 * 2052065 * 2
def baseEnd_2052065 : Nat := 234154595393026448877829

theorem tailTrace_2052065 : CollatzResearch.WordTrace tailWord_2052065 prefixEnd_2052065 234154595393026448877829 := by
  unfold tailWord_2052065
  simp only [CollatzResearch.WordTrace]
  refine ⟨74844959310726444645181649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49896639540484296430121099 74844959310726444645181649)
  ·
    refine ⟨56133719483044833483886237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74844959310726444645181649 56133719483044833483886237)
    ·
      refine ⟨21050144806141812556457339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56133719483044833483886237 21050144806141812556457339)
      ·
        refine ⟨31575217209212718834686009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21050144806141812556457339 31575217209212718834686009)
        ·
          refine ⟨23681412906909539126014507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31575217209212718834686009 23681412906909539126014507)
          ·
            refine ⟨35522119360364308689021761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23681412906909539126014507 35522119360364308689021761)
            ·
              refine ⟨26641589520273231516766321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35522119360364308689021761 26641589520273231516766321)
              ·
                refine ⟨19981192140204923637574741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26641589520273231516766321 19981192140204923637574741)
                ·
                  refine ⟨234154595393026448877829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19981192140204923637574741 234154595393026448877829)
                  ·
                    rfl

theorem cell22_2052065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_2052065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052065 prefixEnd_2052065 := by exact prefixLift 2052065
  have htrace : WordTrace (prefixWord ++ tailWord_2052065) baseStart_2052065 baseEnd_2052065 := by
    simpa [prefixWord, tailWord_2052065, baseEnd_2052065] using wordTrace_append hprefix tailTrace_2052065
  have hstable : (prefixWord ++ tailWord_2052065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052065).length < 2 ^ (prefixWord ++ tailWord_2052065).sum := by decide
  have hdescent : baseEnd_2052065 < baseStart_2052065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052095 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 3, 6]
def baseStart_2052095 : Nat := 118140960795 + 2052095 * 2 ^ 59
def prefixEnd_2052095 : Nat := 4983230072969 + 3 ^ 40 * 2052095 * 2
def baseEnd_2052095 : Nat := 702474055792169268383395

theorem tailTrace_2052095 : CollatzResearch.WordTrace tailWord_2052095 prefixEnd_2052095 702474055792169268383395 := by
  unfold tailWord_2052095
  simp only [CollatzResearch.WordTrace]
  refine ⟨74846053500617759768773739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49897369000411839845849159 74846053500617759768773739)
  ·
    refine ⟨112269080250926639653160609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74846053500617759768773739 112269080250926639653160609)
    ·
      refine ⟨84201810188194979739870457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112269080250926639653160609 84201810188194979739870457)
      ·
        refine ⟨63151357641146234804902843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84201810188194979739870457 63151357641146234804902843)
        ·
          refine ⟨94727036461719352207354265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63151357641146234804902843 94727036461719352207354265)
          ·
            refine ⟨71045277346289514155515699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94727036461719352207354265 71045277346289514155515699)
            ·
              refine ⟨106567916019434271233273549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71045277346289514155515699 106567916019434271233273549)
              ·
                refine ⟨39962968507287851712477581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106567916019434271233273549 39962968507287851712477581)
                ·
                  refine ⟨14986113190232944392179093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39962968507287851712477581 14986113190232944392179093)
                  ·
                    refine ⟨702474055792169268383395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14986113190232944392179093 702474055792169268383395)
                    ·
                      rfl

theorem cell22_2052095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_2052095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052095 prefixEnd_2052095 := by exact prefixLift 2052095
  have htrace : WordTrace (prefixWord ++ tailWord_2052095) baseStart_2052095 baseEnd_2052095 := by
    simpa [prefixWord, tailWord_2052095, baseEnd_2052095] using wordTrace_append hprefix tailTrace_2052095
  have hstable : (prefixWord ++ tailWord_2052095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052095).length < 2 ^ (prefixWord ++ tailWord_2052095).sum := by decide
  have hdescent : baseEnd_2052095 < baseStart_2052095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052097 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 1, 5]
def baseStart_2052097 : Nat := 118140960795 + 2052097 * 2 ^ 59
def prefixEnd_2052097 : Nat := 4983230072969 + 3 ^ 40 * 2052097 * 2
def baseEnd_2052097 : Nat := 702474740433041929833389

theorem tailTrace_2052097 : CollatzResearch.WordTrace tailWord_2052097 prefixEnd_2052097 702474740433041929833389 := by
  unfold tailWord_2052097
  simp only [CollatzResearch.WordTrace]
  refine ⟨74846126446610514110346545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49897417631073676073564363 74846126446610514110346545)
  ·
    refine ⟨56134594834957885582759909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74846126446610514110346545 56134594834957885582759909)
    ·
      refine ⟨10525236531554603546767483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56134594834957885582759909 10525236531554603546767483)
      ·
        refine ⟨15787854797331905320151225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10525236531554603546767483 15787854797331905320151225)
        ·
          refine ⟨11840891097998928990113419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15787854797331905320151225 11840891097998928990113419)
          ·
            refine ⟨17761336646998393485170129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11840891097998928990113419 17761336646998393485170129)
            ·
              refine ⟨13321002485248795113877597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17761336646998393485170129 13321002485248795113877597)
              ·
                refine ⟨4995375931968298167704099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13321002485248795113877597 4995375931968298167704099)
                ·
                  refine ⟨7493063897952447251556149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995375931968298167704099 7493063897952447251556149)
                  ·
                    refine ⟨702474740433041929833389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7493063897952447251556149 702474740433041929833389)
                    ·
                      rfl

theorem cell22_2052097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_2052097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052097 prefixEnd_2052097 := by exact prefixLift 2052097
  have htrace : WordTrace (prefixWord ++ tailWord_2052097) baseStart_2052097 baseEnd_2052097 := by
    simpa [prefixWord, tailWord_2052097, baseEnd_2052097] using wordTrace_append hprefix tailTrace_2052097
  have hstable : (prefixWord ++ tailWord_2052097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052097).length < 2 ^ (prefixWord ++ tailWord_2052097).sum := by decide
  have hdescent : baseEnd_2052097 < baseStart_2052097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052157 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_2052157 : Nat := 118140960795 + 2052157 * 2 ^ 59
def prefixEnd_2052157 : Nat := 4983230072969 + 3 ^ 40 * 2052157 * 2
def baseEnd_2052157 : Nat := 702495279659221773333205

theorem tailTrace_2052157 : CollatzResearch.WordTrace tailWord_2052157 prefixEnd_2052157 702495279659221773333205 := by
  unfold tailWord_2052157
  simp only [CollatzResearch.WordTrace]
  refine ⟨74848314826393144357530725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49898876550928762905020483 74848314826393144357530725)
  ·
    refine ⟨14034059029948714567037011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74848314826393144357530725 14034059029948714567037011)
    ·
      refine ⟨21051088544923071850555517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14034059029948714567037011 21051088544923071850555517)
      ·
        refine ⟨7894158204346151943958319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21051088544923071850555517 7894158204346151943958319)
        ·
          refine ⟨11841237306519227915937479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7894158204346151943958319 11841237306519227915937479)
          ·
            refine ⟨17761855959778841873906219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11841237306519227915937479 17761855959778841873906219)
            ·
              refine ⟨26642783939668262810859329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17761855959778841873906219 26642783939668262810859329)
              ·
                refine ⟨19982087954751197108144497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26642783939668262810859329 19982087954751197108144497)
                ·
                  refine ⟨14986565966063397831108373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19982087954751197108144497 14986565966063397831108373)
                  ·
                    refine ⟨702495279659221773333205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14986565966063397831108373 702495279659221773333205)
                    ·
                      rfl

theorem cell22_2052157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_2052157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052157 prefixEnd_2052157 := by exact prefixLift 2052157
  have htrace : WordTrace (prefixWord ++ tailWord_2052157) baseStart_2052157 baseEnd_2052157 := by
    simpa [prefixWord, tailWord_2052157, baseEnd_2052157] using wordTrace_append hprefix tailTrace_2052157
  have hstable : (prefixWord ++ tailWord_2052157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052157).length < 2 ^ (prefixWord ++ tailWord_2052157).sum := by decide
  have hdescent : baseEnd_2052157 < baseStart_2052157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052206 : List Nat := [4, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_2052206 : Nat := 118140960795 + 2052206 * 2 ^ 59
def prefixEnd_2052206 : Nat := 4983230072969 + 3 ^ 40 * 2052206 * 2
def baseEnd_2052206 : Nat := 234170684453533992952685

theorem tailTrace_2052206 : CollatzResearch.WordTrace tailWord_2052206 prefixEnd_2052206 234170684453533992952685 := by
  unfold tailWord_2052206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9356262750401953215758059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49900068002143750484042981 9356262750401953215758059)
  ·
    refine ⟨14034394125602929823637089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9356262750401953215758059 14034394125602929823637089)
    ·
      refine ⟨10525795594202197367727817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14034394125602929823637089 10525795594202197367727817)
      ·
        refine ⟨7894346695651648025795863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10525795594202197367727817 7894346695651648025795863)
        ·
          refine ⟨11841520043477472038693795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7894346695651648025795863 11841520043477472038693795)
          ·
            refine ⟨17762280065216208058040693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11841520043477472038693795 17762280065216208058040693)
            ·
              refine ⟨1665213756114019505441315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17762280065216208058040693 1665213756114019505441315)
              ·
                refine ⟨2497820634171029258161973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1665213756114019505441315 2497820634171029258161973)
                ·
                  refine ⟨234170684453533992952685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2497820634171029258161973 234170684453533992952685)
                  ·
                    rfl

theorem cell22_2052206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_2052206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052206 prefixEnd_2052206 := by exact prefixLift 2052206
  have htrace : WordTrace (prefixWord ++ tailWord_2052206) baseStart_2052206 baseEnd_2052206 := by
    simpa [prefixWord, tailWord_2052206, baseEnd_2052206] using wordTrace_append hprefix tailTrace_2052206
  have hstable : (prefixWord ++ tailWord_2052206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052206).length < 2 ^ (prefixWord ++ tailWord_2052206).sum := by decide
  have hdescent : baseEnd_2052206 < baseStart_2052206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052300 : List Nat := [2, 2, 1, 6, 1, 1, 2, 2, 2, 3]
def baseStart_2052300 : Nat := 118140960795 + 2052300 * 2 ^ 59
def prefixEnd_2052300 : Nat := 4983230072969 + 3 ^ 40 * 2052300 * 2
def baseEnd_2052300 : Nat := 702544231481617067007767

theorem tailTrace_2052300 : CollatzResearch.WordTrace tailWord_2052300 prefixEnd_2052300 702544231481617067007767 := by
  unfold tailWord_2052300
  simp only [CollatzResearch.WordTrace]
  refine ⟨37426765232437539889993177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49902353643250053186657569 37426765232437539889993177)
  ·
    refine ⟨28070073924328154917494883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37426765232437539889993177 28070073924328154917494883)
    ·
      refine ⟨42105110886492232376242325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28070073924328154917494883 42105110886492232376242325)
      ·
        refine ⟨1973677072804323392636359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42105110886492232376242325 1973677072804323392636359)
        ·
          refine ⟨2960515609206485088954539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973677072804323392636359 2960515609206485088954539)
          ·
            refine ⟨4440773413809727633431809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960515609206485088954539 4440773413809727633431809)
            ·
              refine ⟨3330580060357295725073857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4440773413809727633431809 3330580060357295725073857)
              ·
                refine ⟨2497935045267971793805393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3330580060357295725073857 2497935045267971793805393)
                ·
                  refine ⟨1873451283950978845354045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2497935045267971793805393 1873451283950978845354045)
                  ·
                    refine ⟨702544231481617067007767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1873451283950978845354045 702544231481617067007767)
                    ·
                      rfl

theorem cell22_2052300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_2052300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052300 prefixEnd_2052300 := by exact prefixLift 2052300
  have htrace : WordTrace (prefixWord ++ tailWord_2052300) baseStart_2052300 baseEnd_2052300 := by
    simpa [prefixWord, tailWord_2052300, baseEnd_2052300] using wordTrace_append hprefix tailTrace_2052300
  have hstable : (prefixWord ++ tailWord_2052300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052300).length < 2 ^ (prefixWord ++ tailWord_2052300).sum := by decide
  have hdescent : baseEnd_2052300 < baseStart_2052300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052369 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 6]
def baseStart_2052369 : Nat := 118140960795 + 2052369 * 2 ^ 59
def prefixEnd_2052369 : Nat := 4983230072969 + 3 ^ 40 * 2052369 * 2
def baseEnd_2052369 : Nat := 234189283863907962344185

theorem tailTrace_2052369 : CollatzResearch.WordTrace tailWord_2052369 prefixEnd_2052369 234189283863907962344185 := by
  unfold tailWord_2052369
  simp only [CollatzResearch.WordTrace]
  refine ⟨74856047101625104564248161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49904031401083403042832107 74856047101625104564248161)
  ·
    refine ⟨56142035326218828423186121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74856047101625104564248161 56142035326218828423186121)
    ·
      refine ⟨42106526494664121317389591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56142035326218828423186121 42106526494664121317389591)
      ·
        refine ⟨63159789741996181976084387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42106526494664121317389591 63159789741996181976084387)
        ·
          refine ⟨94739684612994272964126581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63159789741996181976084387 94739684612994272964126581)
          ·
            refine ⟨8881845432468213090386867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94739684612994272964126581 8881845432468213090386867)
            ·
              refine ⟨13322768148702319635580301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8881845432468213090386867 13322768148702319635580301)
              ·
                refine ⟨4996038055763369863342613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13322768148702319635580301 4996038055763369863342613)
                ·
                  refine ⟨234189283863907962344185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4996038055763369863342613 234189283863907962344185)
                  ·
                    rfl

theorem cell22_2052369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_2052369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052369 prefixEnd_2052369 := by exact prefixLift 2052369
  have htrace : WordTrace (prefixWord ++ tailWord_2052369) baseStart_2052369 baseEnd_2052369 := by
    simpa [prefixWord, tailWord_2052369, baseEnd_2052369] using wordTrace_append hprefix tailTrace_2052369
  have hstable : (prefixWord ++ tailWord_2052369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052369).length < 2 ^ (prefixWord ++ tailWord_2052369).sum := by decide
  have hdescent : baseEnd_2052369 < baseStart_2052369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052386 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 6]
def baseStart_2052386 : Nat := 118140960795 + 2052386 * 2 ^ 59
def prefixEnd_2052386 : Nat := 4983230072969 + 3 ^ 40 * 2052386 * 2
def baseEnd_2052386 : Nat := 234191223679713836452501

theorem tailTrace_2052386 : CollatzResearch.WordTrace tailWord_2052386 prefixEnd_2052386 234191223679713836452501 := by
  unfold tailWord_2052386
  simp only [CollatzResearch.WordTrace]
  refine ⟨18714166785640879116904253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49904444761709010978411341 18714166785640879116904253)
  ·
    refine ⟨7017812544615329668839095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18714166785640879116904253 7017812544615329668839095)
    ·
      refine ⟨10526718816922994503258643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7017812544615329668839095 10526718816922994503258643)
      ·
        refine ⟨15790078225384491754887965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10526718816922994503258643 15790078225384491754887965)
        ·
          refine ⟨5921279334519184408082987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15790078225384491754887965 5921279334519184408082987)
          ·
            refine ⟨8881919001778776612124481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921279334519184408082987 8881919001778776612124481)
            ·
              refine ⟨6661439251334082459093361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8881919001778776612124481 6661439251334082459093361)
              ·
                refine ⟨4996079438500561844320021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6661439251334082459093361 4996079438500561844320021)
                ·
                  refine ⟨234191223679713836452501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4996079438500561844320021 234191223679713836452501)
                  ·
                    rfl

theorem cell22_2052386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_2052386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052386 prefixEnd_2052386 := by exact prefixLift 2052386
  have htrace : WordTrace (prefixWord ++ tailWord_2052386) baseStart_2052386 baseEnd_2052386 := by
    simpa [prefixWord, tailWord_2052386, baseEnd_2052386] using wordTrace_append hprefix tailTrace_2052386
  have hstable : (prefixWord ++ tailWord_2052386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052386).length < 2 ^ (prefixWord ++ tailWord_2052386).sum := by decide
  have hdescent : baseEnd_2052386 < baseStart_2052386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052388 : List Nat := [2, 3, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_2052388 : Nat := 118140960795 + 2052388 * 2 ^ 59
def prefixEnd_2052388 : Nat := 4983230072969 + 3 ^ 40 * 2052388 * 2
def baseEnd_2052388 : Nat := 702574355680014170807497

theorem tailTrace_2052388 : CollatzResearch.WordTrace tailWord_2052388 prefixEnd_2052388 702574355680014170807497 := by
  unfold tailWord_2052388
  simp only [CollatzResearch.WordTrace]
  refine ⟨37428370044278135404594909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49904493392370847206126545 37428370044278135404594909)
  ·
    refine ⟨14035638766604300776723091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37428370044278135404594909 14035638766604300776723091)
    ·
      refine ⟨21053458149906451165084637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14035638766604300776723091 21053458149906451165084637)
      ·
        refine ⟨7895046806214919186906739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21053458149906451165084637 7895046806214919186906739)
        ·
          refine ⟨11842570209322378780360109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7895046806214919186906739 11842570209322378780360109)
          ·
            refine ⟨4440963828495892042635041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11842570209322378780360109 4440963828495892042635041)
            ·
              refine ⟨3330722871371919031976281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4440963828495892042635041 3330722871371919031976281)
              ·
                refine ⟨2498042153528939273982211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3330722871371919031976281 2498042153528939273982211)
                ·
                  refine ⟨3747063230293408910973317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2498042153528939273982211 3747063230293408910973317)
                  ·
                    refine ⟨702574355680014170807497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3747063230293408910973317 702574355680014170807497)
                    ·
                      rfl

theorem cell22_2052388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_2052388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052388 prefixEnd_2052388 := by exact prefixLift 2052388
  have htrace : WordTrace (prefixWord ++ tailWord_2052388) baseStart_2052388 baseEnd_2052388 := by
    simpa [prefixWord, tailWord_2052388, baseEnd_2052388] using wordTrace_append hprefix tailTrace_2052388
  have hstable : (prefixWord ++ tailWord_2052388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052388).length < 2 ^ (prefixWord ++ tailWord_2052388).sum := by decide
  have hdescent : baseEnd_2052388 < baseStart_2052388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052399 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 1, 6]
def baseStart_2052399 : Nat := 118140960795 + 2052399 * 2 ^ 59
def prefixEnd_2052399 : Nat := 4983230072969 + 3 ^ 40 * 2052399 * 2
def baseEnd_2052399 : Nat := 702578121204813808782463

theorem tailTrace_2052399 : CollatzResearch.WordTrace tailWord_2052399 prefixEnd_2052399 702578121204813808782463 := by
  unfold tailWord_2052399
  simp only [CollatzResearch.WordTrace]
  refine ⟨74857141291516419687840251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49904760861010946458560167 74857141291516419687840251)
  ·
    refine ⟨112285711937274629531760377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74857141291516419687840251 112285711937274629531760377)
    ·
      refine ⟨84214283952955972148820283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112285711937274629531760377 84214283952955972148820283)
      ·
        refine ⟨126321425929433958223230425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84214283952955972148820283 126321425929433958223230425)
        ·
          refine ⟨94741069447075468667422819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126321425929433958223230425 94741069447075468667422819)
          ·
            refine ⟨142111604170613203001134229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94741069447075468667422819 142111604170613203001134229)
            ·
              refine ⟨6661481445497493890678167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142111604170613203001134229 6661481445497493890678167)
              ·
                refine ⟨9992222168246240836017251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6661481445497493890678167 9992222168246240836017251)
                ·
                  refine ⟨14988333252369361254025877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9992222168246240836017251 14988333252369361254025877)
                  ·
                    refine ⟨702578121204813808782463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14988333252369361254025877 702578121204813808782463)
                    ·
                      rfl

theorem cell22_2052399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_2052399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052399 prefixEnd_2052399 := by exact prefixLift 2052399
  have htrace : WordTrace (prefixWord ++ tailWord_2052399) baseStart_2052399 baseEnd_2052399 := by
    simpa [prefixWord, tailWord_2052399, baseEnd_2052399] using wordTrace_append hprefix tailTrace_2052399
  have hstable : (prefixWord ++ tailWord_2052399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052399).length < 2 ^ (prefixWord ++ tailWord_2052399).sum := by decide
  have hdescent : baseEnd_2052399 < baseStart_2052399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052420 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 6]
def baseStart_2052420 : Nat := 118140960795 + 2052420 * 2 ^ 59
def prefixEnd_2052420 : Nat := 4983230072969 + 3 ^ 40 * 2052420 * 2
def baseEnd_2052420 : Nat := 234195103311325584669133

theorem tailTrace_2052420 : CollatzResearch.WordTrace tailWord_2052420 prefixEnd_2052420 234195103311325584669133 := by
  unfold tailWord_2052420
  simp only [CollatzResearch.WordTrace]
  refine ⟨37428953612220170137177357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49905271482960226849569809 37428953612220170137177357)
  ·
    refine ⟨14035857604582563801441509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37428953612220170137177357 14035857604582563801441509)
    ·
      refine ⟨2631723300859230712770283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14035857604582563801441509 2631723300859230712770283)
      ·
        refine ⟨3947584951288846069155425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631723300859230712770283 3947584951288846069155425)
        ·
          refine ⟨2960688713466634551866569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3947584951288846069155425 2960688713466634551866569)
          ·
            refine ⟨2220516535099975913899927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2960688713466634551866569 2220516535099975913899927)
            ·
              refine ⟨3330774802649963870849891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220516535099975913899927 3330774802649963870849891)
              ·
                refine ⟨4996162203974945806274837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3330774802649963870849891 4996162203974945806274837)
                ·
                  refine ⟨234195103311325584669133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4996162203974945806274837 234195103311325584669133)
                  ·
                    rfl

theorem cell22_2052420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_2052420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052420 prefixEnd_2052420 := by exact prefixLift 2052420
  have htrace : WordTrace (prefixWord ++ tailWord_2052420) baseStart_2052420 baseEnd_2052420 := by
    simpa [prefixWord, tailWord_2052420, baseEnd_2052420] using wordTrace_append hprefix tailTrace_2052420
  have hstable : (prefixWord ++ tailWord_2052420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052420).length < 2 ^ (prefixWord ++ tailWord_2052420).sum := by decide
  have hdescent : baseEnd_2052420 < baseStart_2052420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052482 : List Nat := [3, 4, 2, 1, 3, 1, 1, 7]
def baseStart_2052482 : Nat := 118140960795 + 2052482 * 2 ^ 59
def prefixEnd_2052482 : Nat := 4983230072969 + 3 ^ 40 * 2052482 * 2
def baseEnd_2052482 : Nat := 78067392644558806550801

theorem tailTrace_2052482 : CollatzResearch.WordTrace tailWord_2052482 prefixEnd_2052482 78067392644558806550801 := by
  unfold tailWord_2052482
  simp only [CollatzResearch.WordTrace]
  refine ⟨18715042137553931215777925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49906779033477149908741133 18715042137553931215777925)
  ·
    refine ⟨3509070400791362102958361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18715042137553931215777925 3509070400791362102958361)
    ·
      refine ⟨2631802800593521577218771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3509070400791362102958361 2631802800593521577218771)
      ·
        refine ⟨3947704200890282365828157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631802800593521577218771 3947704200890282365828157)
        ·
          refine ⟨1480389075333855887185559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3947704200890282365828157 1480389075333855887185559)
          ·
            refine ⟨2220583613000783830778339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480389075333855887185559 2220583613000783830778339)
            ·
              refine ⟨3330875419501175746167509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220583613000783830778339 3330875419501175746167509)
              ·
                refine ⟨78067392644558806550801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3330875419501175746167509 78067392644558806550801)
                ·
                  rfl

theorem cell22_2052482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_2052482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052482 prefixEnd_2052482 := by exact prefixLift 2052482
  have htrace : WordTrace (prefixWord ++ tailWord_2052482) baseStart_2052482 baseEnd_2052482 := by
    simpa [prefixWord, tailWord_2052482, baseEnd_2052482] using wordTrace_append hprefix tailTrace_2052482
  have hstable : (prefixWord ++ tailWord_2052482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052482).length < 2 ^ (prefixWord ++ tailWord_2052482).sum := by decide
  have hdescent : baseEnd_2052482 < baseStart_2052482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052491 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 2, 5]
def baseStart_2052491 : Nat := 118140960795 + 2052491 * 2 ^ 59
def prefixEnd_2052491 : Nat := 4983230072969 + 3 ^ 40 * 2052491 * 2
def baseEnd_2052491 : Nat := 702609614684956235482181

theorem tailTrace_2052491 : CollatzResearch.WordTrace tailWord_2052491 prefixEnd_2052491 702609614684956235482181 := by
  unfold tailWord_2052491
  simp only [CollatzResearch.WordTrace]
  refine ⟨74860496807183119400189327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49906997871455412933459551 74860496807183119400189327)
  ·
    refine ⟨112290745210774679100283991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74860496807183119400189327 112290745210774679100283991)
    ·
      refine ⟨168436117816162018650425987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112290745210774679100283991 168436117816162018650425987)
      ·
        refine ⟨252654176724243027975638981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168436117816162018650425987 252654176724243027975638981)
        ·
          refine ⟨47372658135795567745432309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252654176724243027975638981 47372658135795567745432309)
          ·
            refine ⟨4441186700230834476134279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47372658135795567745432309 4441186700230834476134279)
            ·
              refine ⟨6661780050346251714201419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4441186700230834476134279 6661780050346251714201419)
              ·
                refine ⟨9992670075519377571302129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6661780050346251714201419 9992670075519377571302129)
                ·
                  refine ⟨7494502556639533178476597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9992670075519377571302129 7494502556639533178476597)
                  ·
                    refine ⟨702609614684956235482181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7494502556639533178476597 702609614684956235482181)
                    ·
                      rfl

theorem cell22_2052491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 5].length) (baseStart_2052491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052491 prefixEnd_2052491 := by exact prefixLift 2052491
  have htrace : WordTrace (prefixWord ++ tailWord_2052491) baseStart_2052491 baseEnd_2052491 := by
    simpa [prefixWord, tailWord_2052491, baseEnd_2052491] using wordTrace_append hprefix tailTrace_2052491
  have hstable : (prefixWord ++ tailWord_2052491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052491).length < 2 ^ (prefixWord ++ tailWord_2052491).sum := by decide
  have hdescent : baseEnd_2052491 < baseStart_2052491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052551 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 1, 6]
def baseStart_2052551 : Nat := 118140960795 + 2052551 * 2 ^ 59
def prefixEnd_2052551 : Nat := 4983230072969 + 3 ^ 40 * 2052551 * 2
def baseEnd_2052551 : Nat := 702630153911136078981997

theorem tailTrace_2052551 : CollatzResearch.WordTrace tailWord_2052551 prefixEnd_2052551 702630153911136078981997 := by
  unfold tailWord_2052551
  simp only [CollatzResearch.WordTrace]
  refine ⟨74862685186965749647373507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49908456791310499764915671 74862685186965749647373507)
  ·
    refine ⟨112294027780448624471060261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74862685186965749647373507 112294027780448624471060261)
    ·
      refine ⟨21055130208834117088323799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112294027780448624471060261 21055130208834117088323799)
      ·
        refine ⟨31582695313251175632485699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21055130208834117088323799 31582695313251175632485699)
        ·
          refine ⟨47374042969876763448728549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31582695313251175632485699 47374042969876763448728549)
          ·
            refine ⟨8882633056851893146636603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47374042969876763448728549 8882633056851893146636603)
            ·
              refine ⟨13323949585277839719954905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882633056851893146636603 13323949585277839719954905)
              ·
                refine ⟨9992962188958379789966179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13323949585277839719954905 9992962188958379789966179)
                ·
                  refine ⟨14989443283437569684949269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9992962188958379789966179 14989443283437569684949269)
                  ·
                    refine ⟨702630153911136078981997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14989443283437569684949269 702630153911136078981997)
                    ·
                      rfl

theorem cell22_2052551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_2052551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052551 prefixEnd_2052551 := by exact prefixLift 2052551
  have htrace : WordTrace (prefixWord ++ tailWord_2052551) baseStart_2052551 baseEnd_2052551 := by
    simpa [prefixWord, tailWord_2052551, baseEnd_2052551] using wordTrace_append hprefix tailTrace_2052551
  have hstable : (prefixWord ++ tailWord_2052551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052551).length < 2 ^ (prefixWord ++ tailWord_2052551).sum := by decide
  have hdescent : baseEnd_2052551 < baseStart_2052551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052553 : List Nat := [1, 2, 1, 1, 2, 1, 4, 5, 2, 3]
def baseStart_2052553 : Nat := 118140960795 + 2052553 * 2 ^ 59
def prefixEnd_2052553 : Nat := 4983230072969 + 3 ^ 40 * 2052553 * 2
def baseEnd_2052553 : Nat := 702630838552008740431991

theorem tailTrace_2052553 : CollatzResearch.WordTrace tailWord_2052553 prefixEnd_2052553 702630838552008740431991 := by
  unfold tailWord_2052553
  simp only [CollatzResearch.WordTrace]
  refine ⟨74862758132958503988946313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49908505421972335992630875 74862758132958503988946313)
  ·
    refine ⟨56147068599718877991709735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74862758132958503988946313 56147068599718877991709735)
    ·
      refine ⟨84220602899578316987564603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56147068599718877991709735 84220602899578316987564603)
      ·
        refine ⟨126330904349367475481346905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84220602899578316987564603 126330904349367475481346905)
        ·
          refine ⟨94748178262025606611010179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126330904349367475481346905 94748178262025606611010179)
          ·
            refine ⟨142122267393038409916515269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94748178262025606611010179 142122267393038409916515269)
            ·
              refine ⟨26647925136194701859346613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142122267393038409916515269 26647925136194701859346613)
              ·
                refine ⟨2498242981518253299313745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26647925136194701859346613 2498242981518253299313745)
                ·
                  refine ⟨1873682236138689974485309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2498242981518253299313745 1873682236138689974485309)
                  ·
                    refine ⟨702630838552008740431991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1873682236138689974485309 702630838552008740431991)
                    ·
                      rfl

theorem cell22_2052553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 3].length) (baseStart_2052553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052553 prefixEnd_2052553 := by exact prefixLift 2052553
  have htrace : WordTrace (prefixWord ++ tailWord_2052553) baseStart_2052553 baseEnd_2052553 := by
    simpa [prefixWord, tailWord_2052553, baseEnd_2052553] using wordTrace_append hprefix tailTrace_2052553
  have hstable : (prefixWord ++ tailWord_2052553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052553).length < 2 ^ (prefixWord ++ tailWord_2052553).sum := by decide
  have hdescent : baseEnd_2052553 < baseStart_2052553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052658 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_2052658 : Nat := 118140960795 + 2052658 * 2 ^ 59
def prefixEnd_2052658 : Nat := 4983230072969 + 3 ^ 40 * 2052658 * 2
def baseEnd_2052658 : Nat := 702666782197823466556669

theorem tailTrace_2052658 : CollatzResearch.WordTrace tailWord_2052658 prefixEnd_2052658 702666782197823466556669 := by
  unfold tailWord_2052658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18716646949394526730379657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49911058531718737947679085 18716646949394526730379657)
  ·
    refine ⟨14037485212045895047784743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18716646949394526730379657 14037485212045895047784743)
    ·
      refine ⟨21056227818068842571677115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14037485212045895047784743 21056227818068842571677115)
      ·
        refine ⟨31584341727103263857515673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21056227818068842571677115 31584341727103263857515673)
        ·
          refine ⟨23688256295327447893136755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31584341727103263857515673 23688256295327447893136755)
          ·
            refine ⟨35532384442991171839705133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23688256295327447893136755 35532384442991171839705133)
            ·
              refine ⟨13324644166121689439889425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35532384442991171839705133 13324644166121689439889425)
              ·
                refine ⟨9993483124591267079917069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13324644166121689439889425 9993483124591267079917069)
                ·
                  refine ⟨3747556171721725154968901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9993483124591267079917069 3747556171721725154968901)
                  ·
                    refine ⟨702666782197823466556669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3747556171721725154968901 702666782197823466556669)
                    ·
                      rfl

theorem cell22_2052658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_2052658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052658 prefixEnd_2052658 := by exact prefixLift 2052658
  have htrace : WordTrace (prefixWord ++ tailWord_2052658) baseStart_2052658 baseEnd_2052658 := by
    simpa [prefixWord, tailWord_2052658, baseEnd_2052658] using wordTrace_append hprefix tailTrace_2052658
  have hstable : (prefixWord ++ tailWord_2052658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052658).length < 2 ^ (prefixWord ++ tailWord_2052658).sum := by decide
  have hdescent : baseEnd_2052658 < baseStart_2052658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052673 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 8]
def baseStart_2052673 : Nat := 118140960795 + 2052673 * 2 ^ 59
def prefixEnd_2052673 : Nat := 4983230072969 + 3 ^ 40 * 2052673 * 2
def baseEnd_2052673 : Nat := 234223972334789475810541

theorem tailTrace_2052673 : CollatzResearch.WordTrace tailWord_2052673 prefixEnd_2052673 234223972334789475810541 := by
  unfold tailWord_2052673
  simp only [CollatzResearch.WordTrace]
  refine ⟨74867134892523764483314673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49911423261682509655543115 74867134892523764483314673)
  ·
    refine ⟨56150351169392823362486005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74867134892523764483314673 56150351169392823362486005)
    ·
      refine ⟨5264095422130577190233063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56150351169392823362486005 5264095422130577190233063)
      ·
        refine ⟨7896143133195865785349595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5264095422130577190233063 7896143133195865785349595)
        ·
          refine ⟨11844214699793798678024393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7896143133195865785349595 11844214699793798678024393)
          ·
            refine ⟨8883161024845349008518295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11844214699793798678024393 8883161024845349008518295)
            ·
              refine ⟨13324741537268023512777443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8883161024845349008518295 13324741537268023512777443)
              ·
                refine ⟨19987112305902035269166165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13324741537268023512777443 19987112305902035269166165)
                ·
                  refine ⟨234223972334789475810541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19987112305902035269166165 234223972334789475810541)
                  ·
                    rfl

theorem cell22_2052673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_2052673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052673 prefixEnd_2052673 := by exact prefixLift 2052673
  have htrace : WordTrace (prefixWord ++ tailWord_2052673) baseStart_2052673 baseEnd_2052673 := by
    simpa [prefixWord, tailWord_2052673, baseEnd_2052673] using wordTrace_append hprefix tailTrace_2052673
  have hstable : (prefixWord ++ tailWord_2052673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052673).length < 2 ^ (prefixWord ++ tailWord_2052673).sum := by decide
  have hdescent : baseEnd_2052673 < baseStart_2052673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052692 : List Nat := [2, 4, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_2052692 : Nat := 118140960795 + 2052692 * 2 ^ 59
def prefixEnd_2052692 : Nat := 4983230072969 + 3 ^ 40 * 2052692 * 2
def baseEnd_2052692 : Nat := 702678421092658711206565

theorem tailTrace_2052692 : CollatzResearch.WordTrace tailWord_2052692 prefixEnd_2052692 702678421092658711206565 := by
  unfold tailWord_2052692
  simp only [CollatzResearch.WordTrace]
  refine ⟨37433913939727465364128165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49911885252969953818837553 37433913939727465364128165)
  ·
    refine ⟨7018858863698899755774031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37433913939727465364128165 7018858863698899755774031)
    ·
      refine ⟨10528288295548349633661047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7018858863698899755774031 10528288295548349633661047)
      ·
        refine ⟨15792432443322524450491571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10528288295548349633661047 15792432443322524450491571)
        ·
          refine ⟨23688648664983786675737357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15792432443322524450491571 23688648664983786675737357)
          ·
            refine ⟨8883243249368920003401509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23688648664983786675737357 8883243249368920003401509)
            ·
              refine ⟨1665608109256672500637783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8883243249368920003401509 1665608109256672500637783)
              ·
                refine ⟨2498412163885008750956675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1665608109256672500637783 2498412163885008750956675)
                ·
                  refine ⟨3747618245827513126435013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2498412163885008750956675 3747618245827513126435013)
                  ·
                    refine ⟨702678421092658711206565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3747618245827513126435013 702678421092658711206565)
                    ·
                      rfl

theorem cell22_2052692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_2052692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052692 prefixEnd_2052692 := by exact prefixLift 2052692
  have htrace : WordTrace (prefixWord ++ tailWord_2052692) baseStart_2052692 baseEnd_2052692 := by
    simpa [prefixWord, tailWord_2052692, baseEnd_2052692] using wordTrace_append hprefix tailTrace_2052692
  have hstable : (prefixWord ++ tailWord_2052692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052692).length < 2 ^ (prefixWord ++ tailWord_2052692).sum := by decide
  have hdescent : baseEnd_2052692 < baseStart_2052692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052703 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 2, 4]
def baseStart_2052703 : Nat := 118140960795 + 2052703 * 2 ^ 59
def prefixEnd_2052703 : Nat := 4983230072969 + 3 ^ 40 * 2052703 * 2
def baseEnd_2052703 : Nat := 702682186617458349181531

theorem tailTrace_2052703 : CollatzResearch.WordTrace tailWord_2052703 prefixEnd_2052703 702682186617458349181531 := by
  unfold tailWord_2052703
  simp only [CollatzResearch.WordTrace]
  refine ⟨74868229082415079606906763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49912152721610053071271175 74868229082415079606906763)
  ·
    refine ⟨112302343623622619410360145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74868229082415079606906763 112302343623622619410360145)
    ·
      refine ⟨84226757717716964557770109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112302343623622619410360145 84226757717716964557770109)
      ·
        refine ⟨31585034144143861709163791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84226757717716964557770109 31585034144143861709163791)
        ·
          refine ⟨47377551216215792563745687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31585034144143861709163791 47377551216215792563745687)
          ·
            refine ⟨71066326824323688845618531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47377551216215792563745687 71066326824323688845618531)
            ·
              refine ⟨106599490236485533268427797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71066326824323688845618531 106599490236485533268427797)
              ·
                refine ⟨4996851104835259371957553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106599490236485533268427797 4996851104835259371957553)
                ·
                  refine ⟨3747638328626444528968165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4996851104835259371957553 3747638328626444528968165)
                  ·
                    refine ⟨702682186617458349181531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3747638328626444528968165 702682186617458349181531)
                    ·
                      rfl

theorem cell22_2052703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_2052703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052703 prefixEnd_2052703 := by exact prefixLift 2052703
  have htrace : WordTrace (prefixWord ++ tailWord_2052703) baseStart_2052703 baseEnd_2052703 := by
    simpa [prefixWord, tailWord_2052703, baseEnd_2052703] using wordTrace_append hprefix tailTrace_2052703
  have hstable : (prefixWord ++ tailWord_2052703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052703).length < 2 ^ (prefixWord ++ tailWord_2052703).sum := by decide
  have hdescent : baseEnd_2052703 < baseStart_2052703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052705 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 4, 3]
def baseStart_2052705 : Nat := 118140960795 + 2052705 * 2 ^ 59
def prefixEnd_2052705 : Nat := 4983230072969 + 3 ^ 40 * 2052705 * 2
def baseEnd_2052705 : Nat := 702682871258331010631525

theorem tailTrace_2052705 : CollatzResearch.WordTrace tailWord_2052705 prefixEnd_2052705 702682871258331010631525 := by
  unfold tailWord_2052705
  simp only [CollatzResearch.WordTrace]
  refine ⟨74868302028407833948479569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49912201352271889298986379 74868302028407833948479569)
  ·
    refine ⟨56151226521305875461359677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74868302028407833948479569 56151226521305875461359677)
    ·
      refine ⟨21056709945489703298009879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56151226521305875461359677 21056709945489703298009879)
      ·
        refine ⟨31585064918234554947014819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21056709945489703298009879 31585064918234554947014819)
        ·
          refine ⟨47377597377351832420522229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31585064918234554947014819 47377597377351832420522229)
          ·
            refine ⟨4441649754126734289423959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47377597377351832420522229 4441649754126734289423959)
            ·
              refine ⟨6662474631190101434135939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4441649754126734289423959 6662474631190101434135939)
              ·
                refine ⟨9993711946785152151203909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662474631190101434135939 9993711946785152151203909)
                ·
                  refine ⟨1873820990022216028350733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9993711946785152151203909 1873820990022216028350733)
                  ·
                    refine ⟨702682871258331010631525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1873820990022216028350733 702682871258331010631525)
                    ·
                      rfl

theorem cell22_2052705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_2052705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052705 prefixEnd_2052705 := by exact prefixLift 2052705
  have htrace : WordTrace (prefixWord ++ tailWord_2052705) baseStart_2052705 baseEnd_2052705 := by
    simpa [prefixWord, tailWord_2052705, baseEnd_2052705] using wordTrace_append hprefix tailTrace_2052705
  have hstable : (prefixWord ++ tailWord_2052705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052705).length < 2 ^ (prefixWord ++ tailWord_2052705).sum := by decide
  have hdescent : baseEnd_2052705 < baseStart_2052705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052722 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_2052722 : Nat := 118140960795 + 2052722 * 2 ^ 59
def prefixEnd_2052722 : Nat := 4983230072969 + 3 ^ 40 * 2052722 * 2
def baseEnd_2052722 : Nat := 702688690705748632956473

theorem tailTrace_2052722 : CollatzResearch.WordTrace tailWord_2052722 prefixEnd_2052722 702688690705748632956473 := by
  unfold tailWord_2052722
  simp only [CollatzResearch.WordTrace]
  refine ⟨18717230517336561462962105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49912614712897497234565613 18717230517336561462962105)
  ·
    refine ⟨14037922888002421097221579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18717230517336561462962105 14037922888002421097221579)
    ·
      refine ⟨21056884332003631645832369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14037922888002421097221579 21056884332003631645832369)
      ·
        refine ⟨15792663249002723734374277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21056884332003631645832369 15792663249002723734374277)
        ·
          refine ⟨2961124359188010700195177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15792663249002723734374277 2961124359188010700195177)
          ·
            refine ⟨2220843269391008025146383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2961124359188010700195177 2220843269391008025146383)
            ·
              refine ⟨3331264904086512037719575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220843269391008025146383 3331264904086512037719575)
              ·
                refine ⟨4996897356129768056579363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3331264904086512037719575 4996897356129768056579363)
                ·
                  refine ⟨7495346034194652084869045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4996897356129768056579363 7495346034194652084869045)
                  ·
                    refine ⟨702688690705748632956473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7495346034194652084869045 702688690705748632956473)
                    ·
                      rfl

theorem cell22_2052722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_2052722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052722 prefixEnd_2052722 := by exact prefixLift 2052722
  have htrace : WordTrace (prefixWord ++ tailWord_2052722) baseStart_2052722 baseEnd_2052722 := by
    simpa [prefixWord, tailWord_2052722, baseEnd_2052722] using wordTrace_append hprefix tailTrace_2052722
  have hstable : (prefixWord ++ tailWord_2052722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052722).length < 2 ^ (prefixWord ++ tailWord_2052722).sum := by decide
  have hdescent : baseEnd_2052722 < baseStart_2052722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052818 : List Nat := [3, 2, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_2052818 : Nat := 118140960795 + 2052818 * 2 ^ 59
def prefixEnd_2052818 : Nat := 4983230072969 + 3 ^ 40 * 2052818 * 2
def baseEnd_2052818 : Nat := 702721553467636382556179

theorem tailTrace_2052818 : CollatzResearch.WordTrace tailWord_2052818 prefixEnd_2052818 702721553467636382556179 := by
  unfold tailWord_2052818
  simp only [CollatzResearch.WordTrace]
  refine ⟨18718105869249613561835777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49914948984665636164895405 18718105869249613561835777)
  ·
    refine ⟨14038579401937210171376833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18718105869249613561835777 14038579401937210171376833)
    ·
      refine ⟨10528934551452907628532625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14038579401937210171376833 10528934551452907628532625)
      ·
        refine ⟨7896700913589680721399469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10528934551452907628532625 7896700913589680721399469)
        ·
          refine ⟨2961262842596130270524801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7896700913589680721399469 2961262842596130270524801)
          ·
            refine ⟨2220947131947097702893601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2961262842596130270524801 2220947131947097702893601)
            ·
              refine ⟨1665710348960323277170201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220947131947097702893601 1665710348960323277170201)
              ·
                refine ⟨1249282761720242457877651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665710348960323277170201 1249282761720242457877651)
                ·
                  refine ⟨1873924142580363686816477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249282761720242457877651 1873924142580363686816477)
                  ·
                    refine ⟨702721553467636382556179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1873924142580363686816477 702721553467636382556179)
                    ·
                      rfl

theorem cell22_2052818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_2052818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052818 prefixEnd_2052818 := by exact prefixLift 2052818
  have htrace : WordTrace (prefixWord ++ tailWord_2052818) baseStart_2052818 baseEnd_2052818 := by
    simpa [prefixWord, tailWord_2052818, baseEnd_2052818] using wordTrace_append hprefix tailTrace_2052818
  have hstable : (prefixWord ++ tailWord_2052818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052818).length < 2 ^ (prefixWord ++ tailWord_2052818).sum := by decide
  have hdescent : baseEnd_2052818 < baseStart_2052818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052915 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 7]
def baseStart_2052915 : Nat := 118140960795 + 2052915 * 2 ^ 59
def prefixEnd_2052915 : Nat := 4983230072969 + 3 ^ 40 * 2052915 * 2
def baseEnd_2052915 : Nat := 234251586183320154293627

theorem tailTrace_2052915 : CollatzResearch.WordTrace tailWord_2052915 prefixEnd_2052915 234251586183320154293627 := by
  unfold tailWord_2052915
  simp only [CollatzResearch.WordTrace]
  refine ⟨74875961357647039813624199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49917307571764693209082799 74875961357647039813624199)
  ·
    refine ⟨112313942036470559720436299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74875961357647039813624199 112313942036470559720436299)
    ·
      refine ⟨168470913054705839580654449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112313942036470559720436299 168470913054705839580654449)
      ·
        refine ⟨126353184791029379685490837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168470913054705839580654449 126353184791029379685490837)
        ·
          refine ⟨5922805537079502172757383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126353184791029379685490837 5922805537079502172757383)
          ·
            refine ⟨8884208305619253259136075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5922805537079502172757383 8884208305619253259136075)
            ·
              refine ⟨13326312458428879888704113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8884208305619253259136075 13326312458428879888704113)
              ·
                refine ⟨9994734343821659916528085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13326312458428879888704113 9994734343821659916528085)
                ·
                  refine ⟨234251586183320154293627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9994734343821659916528085 234251586183320154293627)
                  ·
                    rfl

theorem cell22_2052915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 7].length) (baseStart_2052915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052915 prefixEnd_2052915 := by exact prefixLift 2052915
  have htrace : WordTrace (prefixWord ++ tailWord_2052915) baseStart_2052915 baseEnd_2052915 := by
    simpa [prefixWord, tailWord_2052915, baseEnd_2052915] using wordTrace_append hprefix tailTrace_2052915
  have hstable : (prefixWord ++ tailWord_2052915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052915).length < 2 ^ (prefixWord ++ tailWord_2052915).sum := by decide
  have hdescent : baseEnd_2052915 < baseStart_2052915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052936 : List Nat := [2, 1, 3, 1, 1, 3, 5, 2, 1, 3]
def baseStart_2052936 : Nat := 118140960795 + 2052936 * 2 ^ 59
def prefixEnd_2052936 : Nat := 4983230072969 + 3 ^ 40 * 2052936 * 2
def baseEnd_2052936 : Nat := 702761947279123408105817

theorem tailTrace_2052936 : CollatzResearch.WordTrace tailWord_2052936 prefixEnd_2052936 702761947279123408105817 := by
  unfold tailWord_2052936
  simp only [CollatzResearch.WordTrace]
  refine ⟨37438363645285480200069331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49917818193713973600092441 37438363645285480200069331)
  ·
    refine ⟨56157545467928220300103997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37438363645285480200069331 56157545467928220300103997)
    ·
      refine ⟨21059079550473082612538999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56157545467928220300103997 21059079550473082612538999)
      ·
        refine ⟨31588619325709623918808499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21059079550473082612538999 31588619325709623918808499)
        ·
          refine ⟨47382928988564435878212749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31588619325709623918808499 47382928988564435878212749)
          ·
            refine ⟨17768598370711663454329781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47382928988564435878212749 17768598370711663454329781)
            ·
              refine ⟨1665806097254218448843417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17768598370711663454329781 1665806097254218448843417)
              ·
                refine ⟨1249354572940663836632563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665806097254218448843417 1249354572940663836632563)
                ·
                  refine ⟨1874031859410995754948845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249354572940663836632563 1874031859410995754948845)
                  ·
                    refine ⟨702761947279123408105817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1874031859410995754948845 702761947279123408105817)
                    ·
                      rfl

theorem cell22_2052936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_2052936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052936 prefixEnd_2052936 := by exact prefixLift 2052936
  have htrace : WordTrace (prefixWord ++ tailWord_2052936) baseStart_2052936 baseEnd_2052936 := by
    simpa [prefixWord, tailWord_2052936, baseEnd_2052936] using wordTrace_append hprefix tailTrace_2052936
  have hstable : (prefixWord ++ tailWord_2052936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052936).length < 2 ^ (prefixWord ++ tailWord_2052936).sum := by decide
  have hdescent : baseEnd_2052936 < baseStart_2052936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052960 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 8]
def baseStart_2052960 : Nat := 118140960795 + 2052960 * 2 ^ 59
def prefixEnd_2052960 : Nat := 4983230072969 + 3 ^ 40 * 2052960 * 2
def baseEnd_2052960 : Nat := 234256720989865115168581

theorem tailTrace_2052960 : CollatzResearch.WordTrace tailWord_2052960 prefixEnd_2052960 234256720989865115168581 := by
  unfold tailWord_2052960
  simp only [CollatzResearch.WordTrace]
  refine ⟨37438801321242006249506167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49918401761656008332674889 37438801321242006249506167)
  ·
    refine ⟨56158201981863009374259251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37438801321242006249506167 56158201981863009374259251)
    ·
      refine ⟨84237302972794514061388877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56158201981863009374259251 84237302972794514061388877)
      ·
        refine ⟨31588988614797942773020829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84237302972794514061388877 31588988614797942773020829)
        ·
          refine ⟨11845870730549228539882811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31588988614797942773020829 11845870730549228539882811)
          ·
            refine ⟨17768806095823842809824217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11845870730549228539882811 17768806095823842809824217)
            ·
              refine ⟨13326604571867882107368163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17768806095823842809824217 13326604571867882107368163)
              ·
                refine ⟨19989906857801823161052245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13326604571867882107368163 19989906857801823161052245)
                ·
                  refine ⟨234256720989865115168581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19989906857801823161052245 234256720989865115168581)
                  ·
                    rfl

theorem cell22_2052960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_2052960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052960 prefixEnd_2052960 := by exact prefixLift 2052960
  have htrace : WordTrace (prefixWord ++ tailWord_2052960) baseStart_2052960 baseEnd_2052960 := by
    simpa [prefixWord, tailWord_2052960, baseEnd_2052960] using wordTrace_append hprefix tailTrace_2052960
  have hstable : (prefixWord ++ tailWord_2052960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052960).length < 2 ^ (prefixWord ++ tailWord_2052960).sum := by decide
  have hdescent : baseEnd_2052960 < baseStart_2052960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053035 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 4, 6]
def baseStart_2053035 : Nat := 118140960795 + 2053035 * 2 ^ 59
def prefixEnd_2053035 : Nat := 4983230072969 + 3 ^ 40 * 2053035 * 2
def baseEnd_2053035 : Nat := 702795837002320149880513

theorem tailTrace_2053035 : CollatzResearch.WordTrace tailWord_2053035 prefixEnd_2053035 702795837002320149880513 := by
  unfold tailWord_2053035
  simp only [CollatzResearch.WordTrace]
  refine ⟨74880338117212300307992559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49920225411474866871995039 74880338117212300307992559)
  ·
    refine ⟨112320507175818450461988839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74880338117212300307992559 112320507175818450461988839)
    ·
      refine ⟨168480760763727675692983259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112320507175818450461988839 168480760763727675692983259)
      ·
        refine ⟨252721141145591513539474889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168480760763727675692983259 252721141145591513539474889)
        ·
          refine ⟨189540855859193635154606167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252721141145591513539474889 189540855859193635154606167)
          ·
            refine ⟨284311283788790452731909251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189540855859193635154606167 284311283788790452731909251)
            ·
              refine ⟨426466925683185679097863877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284311283788790452731909251 426466925683185679097863877)
              ·
                refine ⟨79962548565597314830849477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 426466925683185679097863877 79962548565597314830849477)
                ·
                  refine ⟨14992977856049496530784277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79962548565597314830849477 14992977856049496530784277)
                  ·
                    refine ⟨702795837002320149880513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14992977856049496530784277 702795837002320149880513)
                    ·
                      rfl

theorem cell22_2053035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_2053035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053035 prefixEnd_2053035 := by exact prefixLift 2053035
  have htrace : WordTrace (prefixWord ++ tailWord_2053035) baseStart_2053035 baseEnd_2053035 := by
    simpa [prefixWord, tailWord_2053035, baseEnd_2053035] using wordTrace_append hprefix tailTrace_2053035
  have hstable : (prefixWord ++ tailWord_2053035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053035).length < 2 ^ (prefixWord ++ tailWord_2053035).sum := by decide
  have hdescent : baseEnd_2053035 < baseStart_2053035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053060 : List Nat := [2, 3, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_2053060 : Nat := 118140960795 + 2053060 * 2 ^ 59
def prefixEnd_2053060 : Nat := 4983230072969 + 3 ^ 40 * 2053060 * 2
def baseEnd_2053060 : Nat := 702804395013228418005437

theorem tailTrace_2053060 : CollatzResearch.WordTrace tailWord_2053060 prefixEnd_2053060 702804395013228418005437 := by
  unfold tailWord_2053060
  simp only [CollatzResearch.WordTrace]
  refine ⟨37440624971060864788826317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49920833294747819718435089 37440624971060864788826317)
  ·
    refine ⟨14040234364147824295809869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37440624971060864788826317 14040234364147824295809869)
    ·
      refine ⟨5265087886555434110928701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14040234364147824295809869 5265087886555434110928701)
      ·
        refine ⟨1974407957458287791598263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5265087886555434110928701 1974407957458287791598263)
        ·
          refine ⟨2961611936187431687397395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974407957458287791598263 2961611936187431687397395)
          ·
            refine ⟨4442417904281147531096093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961611936187431687397395 4442417904281147531096093)
            ·
              refine ⟨1665906714105430324161035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4442417904281147531096093 1665906714105430324161035)
              ·
                refine ⟨2498860071158145486241553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1665906714105430324161035 2498860071158145486241553)
                ·
                  refine ⟨1874145053368609114681165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2498860071158145486241553 1874145053368609114681165)
                  ·
                    refine ⟨702804395013228418005437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1874145053368609114681165 702804395013228418005437)
                    ·
                      rfl

theorem cell22_2053060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_2053060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053060 prefixEnd_2053060 := by exact prefixLift 2053060
  have htrace : WordTrace (prefixWord ++ tailWord_2053060) baseStart_2053060 baseEnd_2053060 := by
    simpa [prefixWord, tailWord_2053060, baseEnd_2053060] using wordTrace_append hprefix tailTrace_2053060
  have hstable : (prefixWord ++ tailWord_2053060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053060).length < 2 ^ (prefixWord ++ tailWord_2053060).sum := by decide
  have hdescent : baseEnd_2053060 < baseStart_2053060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053131 : List Nat := [1, 1, 1, 1, 6, 4, 1, 2, 1, 4]
def baseStart_2053131 : Nat := 118140960795 + 2053131 * 2 ^ 59
def prefixEnd_2053131 : Nat := 4983230072969 + 3 ^ 40 * 2053131 * 2
def baseEnd_2053131 : Nat := 702828699764207899480219

theorem tailTrace_2053131 : CollatzResearch.WordTrace tailWord_2053131 prefixEnd_2053131 702828699764207899480219 := by
  unfold tailWord_2053131
  simp only [CollatzResearch.WordTrace]
  refine ⟨74883839524864508703487247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49922559683243005802324831 74883839524864508703487247)
  ·
    refine ⟨112325759287296763055230871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74883839524864508703487247 112325759287296763055230871)
    ·
      refine ⟨168488638930945144582846307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112325759287296763055230871 168488638930945144582846307)
      ·
        refine ⟨252732958396417716874269461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168488638930945144582846307 252732958396417716874269461)
        ·
          refine ⟨11846857424832080478481381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 252732958396417716874269461 11846857424832080478481381)
          ·
            refine ⟨2221285767156015089715259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11846857424832080478481381 2221285767156015089715259)
            ·
              refine ⟨3331928650734022634572889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221285767156015089715259 3331928650734022634572889)
              ·
                refine ⟨2498946488050516975929667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3331928650734022634572889 2498946488050516975929667)
                ·
                  refine ⟨3748419732075775463894501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2498946488050516975929667 3748419732075775463894501)
                  ·
                    refine ⟨702828699764207899480219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3748419732075775463894501 702828699764207899480219)
                    ·
                      rfl

theorem cell22_2053131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 4].length) (baseStart_2053131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053131 prefixEnd_2053131 := by exact prefixLift 2053131
  have htrace : WordTrace (prefixWord ++ tailWord_2053131) baseStart_2053131 baseEnd_2053131 := by
    simpa [prefixWord, tailWord_2053131, baseEnd_2053131] using wordTrace_append hprefix tailTrace_2053131
  have hstable : (prefixWord ++ tailWord_2053131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053131).length < 2 ^ (prefixWord ++ tailWord_2053131).sum := by decide
  have hdescent : baseEnd_2053131 < baseStart_2053131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053144 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 1, 5]
def baseStart_2053144 : Nat := 118140960795 + 2053144 * 2 ^ 59
def prefixEnd_2053144 : Nat := 4983230072969 + 3 ^ 40 * 2053144 * 2
def baseEnd_2053144 : Nat := 702833149929880198905179

theorem tailTrace_2053144 : CollatzResearch.WordTrace tailWord_2053144 prefixEnd_2053144 702833149929880198905179 := by
  unfold tailWord_2053144
  simp only [CollatzResearch.WordTrace]
  refine ⟨37442156836908705961855243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49922875782544941282473657 37442156836908705961855243)
  ·
    refine ⟨56163235255363058942782865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37442156836908705961855243 56163235255363058942782865)
    ·
      refine ⟨42122426441522294207087149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56163235255363058942782865 42122426441522294207087149)
      ·
        refine ⟨15795909915570860327657681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42122426441522294207087149 15795909915570860327657681)
        ·
          refine ⟨11846932436678145245743261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15795909915570860327657681 11846932436678145245743261)
          ·
            refine ⟨4442599663754304467153723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11846932436678145245743261 4442599663754304467153723)
            ·
              refine ⟨6663899495631456700730585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442599663754304467153723 6663899495631456700730585)
              ·
                refine ⟨4997924621723592525547939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6663899495631456700730585 4997924621723592525547939)
                ·
                  refine ⟨7496886932585388788321909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4997924621723592525547939 7496886932585388788321909)
                  ·
                    refine ⟨702833149929880198905179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7496886932585388788321909 702833149929880198905179)
                    ·
                      rfl

theorem cell22_2053144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_2053144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053144 prefixEnd_2053144 := by exact prefixLift 2053144
  have htrace : WordTrace (prefixWord ++ tailWord_2053144) baseStart_2053144 baseEnd_2053144 := by
    simpa [prefixWord, tailWord_2053144, baseEnd_2053144] using wordTrace_append hprefix tailTrace_2053144
  have hstable : (prefixWord ++ tailWord_2053144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053144).length < 2 ^ (prefixWord ++ tailWord_2053144).sum := by decide
  have hdescent : baseEnd_2053144 < baseStart_2053144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053148 : List Nat := [2, 2, 3, 1, 4, 1, 3, 1, 1, 4]
def baseStart_2053148 : Nat := 118140960795 + 2053148 * 2 ^ 59
def prefixEnd_2053148 : Nat := 4983230072969 + 3 ^ 40 * 2053148 * 2
def baseEnd_2053148 : Nat := 702834519211625521805167

theorem tailTrace_2053148 : CollatzResearch.WordTrace tailWord_2053148 prefixEnd_2053148 702834519211625521805167 := by
  unfold tailWord_2053148
  simp only [CollatzResearch.WordTrace]
  refine ⟨37442229782901460303428049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49922973043868613737904065 37442229782901460303428049)
  ·
    refine ⟨28081672337176095227571037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37442229782901460303428049 28081672337176095227571037)
    ·
      refine ⟨10530627126441035710339139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28081672337176095227571037 10530627126441035710339139)
      ·
        refine ⟨15795940689661553565508709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10530627126441035710339139 15795940689661553565508709)
        ·
          refine ⟨2961738879311541293532883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15795940689661553565508709 2961738879311541293532883)
          ·
            refine ⟨4442608318967311940299325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961738879311541293532883 4442608318967311940299325)
            ·
              refine ⟨1665978119612741977612247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4442608318967311940299325 1665978119612741977612247)
              ·
                refine ⟨2498967179419112966418371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1665978119612741977612247 2498967179419112966418371)
                ·
                  refine ⟨3748450769128669449627557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2498967179419112966418371 3748450769128669449627557)
                  ·
                    refine ⟨702834519211625521805167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3748450769128669449627557 702834519211625521805167)
                    ·
                      rfl

theorem cell22_2053148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_2053148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053148 prefixEnd_2053148 := by exact prefixLift 2053148
  have htrace : WordTrace (prefixWord ++ tailWord_2053148) baseStart_2053148 baseEnd_2053148 := by
    simpa [prefixWord, tailWord_2053148, baseEnd_2053148] using wordTrace_append hprefix tailTrace_2053148
  have hstable : (prefixWord ++ tailWord_2053148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053148).length < 2 ^ (prefixWord ++ tailWord_2053148).sum := by decide
  have hdescent : baseEnd_2053148 < baseStart_2053148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053187 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 2, 6]
def baseStart_2053187 : Nat := 118140960795 + 2053187 * 2 ^ 59
def prefixEnd_2053187 : Nat := 4983230072969 + 3 ^ 40 * 2053187 * 2
def baseEnd_2053187 : Nat := 702847869708642420080047

theorem tailTrace_2053187 : CollatzResearch.WordTrace tailWord_2053187 prefixEnd_2053187 702847869708642420080047 := by
  unfold tailWord_2053187
  simp only [CollatzResearch.WordTrace]
  refine ⟨74885882012661630267525815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49923921341774420178350543 74885882012661630267525815)
  ·
    refine ⟨112328823018992445401288723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74885882012661630267525815 112328823018992445401288723)
    ·
      refine ⟨168493234528488668101933085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112328823018992445401288723 168493234528488668101933085)
      ·
        refine ⟨63184962948183250538224907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168493234528488668101933085 63184962948183250538224907)
        ·
          refine ⟨94777444422274875807337361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63184962948183250538224907 94777444422274875807337361)
          ·
            refine ⟨71083083316706156855503021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94777444422274875807337361 71083083316706156855503021)
            ·
              refine ⟨26656156243764808820813633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71083083316706156855503021 26656156243764808820813633)
              ·
                refine ⟨19992117182823606615610225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26656156243764808820813633 19992117182823606615610225)
                ·
                  refine ⟨14994087887117704961707669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19992117182823606615610225 14994087887117704961707669)
                  ·
                    refine ⟨702847869708642420080047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14994087887117704961707669 702847869708642420080047)
                    ·
                      rfl

theorem cell22_2053187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_2053187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053187 prefixEnd_2053187 := by exact prefixLift 2053187
  have htrace : WordTrace (prefixWord ++ tailWord_2053187) baseStart_2053187 baseEnd_2053187 := by
    simpa [prefixWord, tailWord_2053187, baseEnd_2053187] using wordTrace_append hprefix tailTrace_2053187
  have hstable : (prefixWord ++ tailWord_2053187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053187).length < 2 ^ (prefixWord ++ tailWord_2053187).sum := by decide
  have hdescent : baseEnd_2053187 < baseStart_2053187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053189 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 5, 3]
def baseStart_2053189 : Nat := 118140960795 + 2053189 * 2 ^ 59
def prefixEnd_2053189 : Nat := 4983230072969 + 3 ^ 40 * 2053189 * 2
def baseEnd_2053189 : Nat := 702848554349515081530041

theorem tailTrace_2053189 : CollatzResearch.WordTrace tailWord_2053189 prefixEnd_2053189 702848554349515081530041 := by
  unfold tailWord_2053189
  simp only [CollatzResearch.WordTrace]
  refine ⟨74885954958654384609098621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49923969972436256406065747 74885954958654384609098621)
  ·
    refine ⟨28082233109495394228411983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74885954958654384609098621 28082233109495394228411983)
    ·
      refine ⟨42123349664243091342617975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28082233109495394228411983 42123349664243091342617975)
      ·
        refine ⟨63185024496364637013926963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42123349664243091342617975 63185024496364637013926963)
        ·
          refine ⟨94777536744546955520890445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63185024496364637013926963 94777536744546955520890445)
          ·
            refine ⟨35541576279205108320333917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94777536744546955520890445 35541576279205108320333917)
            ·
              refine ⟨13328091104701915620125219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35541576279205108320333917 13328091104701915620125219)
              ·
                refine ⟨19992136657052873430187829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13328091104701915620125219 19992136657052873430187829)
                ·
                  refine ⟨1874262811598706884080109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19992136657052873430187829 1874262811598706884080109)
                  ·
                    refine ⟨702848554349515081530041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1874262811598706884080109 702848554349515081530041)
                    ·
                      rfl

theorem cell22_2053189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_2053189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053189 prefixEnd_2053189 := by exact prefixLift 2053189
  have htrace : WordTrace (prefixWord ++ tailWord_2053189) baseStart_2053189 baseEnd_2053189 := by
    simpa [prefixWord, tailWord_2053189, baseEnd_2053189] using wordTrace_append hprefix tailTrace_2053189
  have hstable : (prefixWord ++ tailWord_2053189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053189).length < 2 ^ (prefixWord ++ tailWord_2053189).sum := by decide
  have hdescent : baseEnd_2053189 < baseStart_2053189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053223 : List Nat := [1, 1, 5, 1, 1, 3, 2, 4, 1, 3]
def baseStart_2053223 : Nat := 118140960795 + 2053223 * 2 ^ 59
def prefixEnd_2053223 : Nat := 4983230072969 + 3 ^ 40 * 2053223 * 2
def baseEnd_2053223 : Nat := 702860193244350326179937

theorem tailTrace_2053223 : CollatzResearch.WordTrace tailWord_2053223 prefixEnd_2053223 702860193244350326179937 := by
  unfold tailWord_2053223
  simp only [CollatzResearch.WordTrace]
  refine ⟨74887195040531208415836323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49924796693687472277224215 74887195040531208415836323)
  ·
    refine ⟨112330792560796812623754485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74887195040531208415836323 112330792560796812623754485)
    ·
      refine ⟨10531011802574701183476983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112330792560796812623754485 10531011802574701183476983)
      ·
        refine ⟨15796517703862051775215475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10531011802574701183476983 15796517703862051775215475)
        ·
          refine ⟨23694776555793077662823213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15796517703862051775215475 23694776555793077662823213)
          ·
            refine ⟨8885541208422404123558705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23694776555793077662823213 8885541208422404123558705)
            ·
              refine ⟨6664155906316803092669029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8885541208422404123558705 6664155906316803092669029)
              ·
                refine ⟨1249529232434400579875443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6664155906316803092669029 1249529232434400579875443)
                ·
                  refine ⟨1874293848651600869813165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249529232434400579875443 1874293848651600869813165)
                  ·
                    refine ⟨702860193244350326179937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1874293848651600869813165 702860193244350326179937)
                    ·
                      rfl

theorem cell22_2053223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_2053223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053223 prefixEnd_2053223 := by exact prefixLift 2053223
  have htrace : WordTrace (prefixWord ++ tailWord_2053223) baseStart_2053223 baseEnd_2053223 := by
    simpa [prefixWord, tailWord_2053223, baseEnd_2053223] using wordTrace_append hprefix tailTrace_2053223
  have hstable : (prefixWord ++ tailWord_2053223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053223).length < 2 ^ (prefixWord ++ tailWord_2053223).sum := by decide
  have hdescent : baseEnd_2053223 < baseStart_2053223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053234 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_2053234 : Nat := 118140960795 + 2053234 * 2 ^ 59
def prefixEnd_2053234 : Nat := 4983230072969 + 3 ^ 40 * 2053234 * 2
def baseEnd_2053234 : Nat := 702863958769149964154903

theorem tailTrace_2053234 : CollatzResearch.WordTrace tailWord_2053234 prefixEnd_2053234 702863958769149964154903 := by
  unfold tailWord_2053234
  simp only [CollatzResearch.WordTrace]
  refine ⟨18721899060872839323621689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49925064162327571529657837 18721899060872839323621689)
  ·
    refine ⟨14041424295654629492716267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18721899060872839323621689 14041424295654629492716267)
    ·
      refine ⟨21062136443481944239074401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14041424295654629492716267 21062136443481944239074401)
      ·
        refine ⟨15796602332611458179305801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21062136443481944239074401 15796602332611458179305801)
        ·
          refine ⟨11847451749458593634479351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15796602332611458179305801 11847451749458593634479351)
          ·
            refine ⟨17771177624187890451719027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11847451749458593634479351 17771177624187890451719027)
            ·
              refine ⟨26656766436281835677578541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17771177624187890451719027 26656766436281835677578541)
              ·
                refine ⟨9996287413605688379091953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26656766436281835677578541 9996287413605688379091953)
                ·
                  refine ⟨7497215560204266284318965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9996287413605688379091953 7497215560204266284318965)
                  ·
                    refine ⟨702863958769149964154903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7497215560204266284318965 702863958769149964154903)
                    ·
                      rfl

theorem cell22_2053234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_2053234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053234 prefixEnd_2053234 := by exact prefixLift 2053234
  have htrace : WordTrace (prefixWord ++ tailWord_2053234) baseStart_2053234 baseEnd_2053234 := by
    simpa [prefixWord, tailWord_2053234, baseEnd_2053234] using wordTrace_append hprefix tailTrace_2053234
  have hstable : (prefixWord ++ tailWord_2053234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053234).length < 2 ^ (prefixWord ++ tailWord_2053234).sum := by decide
  have hdescent : baseEnd_2053234 < baseStart_2053234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053296 : List Nat := [2, 1, 1, 1, 2, 1, 2, 7, 2, 3]
def baseStart_2053296 : Nat := 118140960795 + 2053296 * 2 ^ 59
def prefixEnd_2053296 : Nat := 4983230072969 + 3 ^ 40 * 2053296 * 2
def baseEnd_2053296 : Nat := 702885182636202469104713

theorem tailTrace_2053296 : CollatzResearch.WordTrace tailWord_2053296 prefixEnd_2053296 702885182636202469104713 := by
  unfold tailWord_2053296
  simp only [CollatzResearch.WordTrace]
  refine ⟨37444928784633370941621871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49926571712844494588829161 37444928784633370941621871)
  ·
    refine ⟨56167393176950056412432807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37444928784633370941621871 56167393176950056412432807)
    ·
      refine ⟨84251089765425084618649211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56167393176950056412432807 84251089765425084618649211)
      ·
        refine ⟨126376634648137626927973817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84251089765425084618649211 126376634648137626927973817)
        ·
          refine ⟨94782475986103220195980363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126376634648137626927973817 94782475986103220195980363)
          ·
            refine ⟨142173713979154830293970545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94782475986103220195980363 142173713979154830293970545)
            ·
              refine ⟨106630285484366122720477909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142173713979154830293970545 106630285484366122720477909)
              ·
                refine ⟨2499147316039831001261201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 106630285484366122720477909 2499147316039831001261201)
                ·
                  refine ⟨1874360487029873250945901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2499147316039831001261201 1874360487029873250945901)
                  ·
                    refine ⟨702885182636202469104713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1874360487029873250945901 702885182636202469104713)
                    ·
                      rfl

theorem cell22_2053296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 2, 3].length) (baseStart_2053296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053296 prefixEnd_2053296 := by exact prefixLift 2053296
  have htrace : WordTrace (prefixWord ++ tailWord_2053296) baseStart_2053296 baseEnd_2053296 := by
    simpa [prefixWord, tailWord_2053296, baseEnd_2053296] using wordTrace_append hprefix tailTrace_2053296
  have hstable : (prefixWord ++ tailWord_2053296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053296).length < 2 ^ (prefixWord ++ tailWord_2053296).sum := by decide
  have hdescent : baseEnd_2053296 < baseStart_2053296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053309 : List Nat := [1, 4, 1, 2, 1, 1, 4, 8]
def baseStart_2053309 : Nat := 118140960795 + 2053309 * 2 ^ 59
def prefixEnd_2053309 : Nat := 4983230072969 + 3 ^ 40 * 2053309 * 2
def baseEnd_2053309 : Nat := 78098848089097196503297

theorem tailTrace_2053309 : CollatzResearch.WordTrace tailWord_2053309 prefixEnd_2053309 78098848089097196503297 := by
  unfold tailWord_2053309
  simp only [CollatzResearch.WordTrace]
  refine ⟨74890331718219645103466981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49926887812146430068977987 74890331718219645103466981)
  ·
    refine ⟨14041937197166183456900059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74890331718219645103466981 14041937197166183456900059)
    ·
      refine ⟨21062905795749275185350089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14041937197166183456900059 21062905795749275185350089)
      ·
        refine ⟨15797179346811956389012567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21062905795749275185350089 15797179346811956389012567)
        ·
          refine ⟨23695769020217934583518851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15797179346811956389012567 23695769020217934583518851)
          ·
            refine ⟨35543653530326901875278277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23695769020217934583518851 35543653530326901875278277)
            ·
              refine ⟨6664435036936294101614677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35543653530326901875278277 6664435036936294101614677)
              ·
                refine ⟨78098848089097196503297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6664435036936294101614677 78098848089097196503297)
                ·
                  rfl

theorem cell22_2053309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 8].length) (baseStart_2053309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053309 prefixEnd_2053309 := by exact prefixLift 2053309
  have htrace : WordTrace (prefixWord ++ tailWord_2053309) baseStart_2053309 baseEnd_2053309 := by
    simpa [prefixWord, tailWord_2053309, baseEnd_2053309] using wordTrace_append hprefix tailTrace_2053309
  have hstable : (prefixWord ++ tailWord_2053309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053309).length < 2 ^ (prefixWord ++ tailWord_2053309).sum := by decide
  have hdescent : baseEnd_2053309 < baseStart_2053309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053313 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2053313 : Nat := 118140960795 + 2053313 * 2 ^ 59
def prefixEnd_2053313 : Nat := 4983230072969 + 3 ^ 40 * 2053313 * 2
def baseEnd_2053313 : Nat := 702891002083620091429661

theorem tailTrace_2053313 : CollatzResearch.WordTrace tailWord_2053313 prefixEnd_2053313 702891002083620091429661 := by
  unfold tailWord_2053313
  simp only [CollatzResearch.WordTrace]
  refine ⟨74890477610205153786612593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49926985073470102524408395 74890477610205153786612593)
  ·
    refine ⟨56167858207653865339959445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74890477610205153786612593 56167858207653865339959445)
    ·
      refine ⟨2632868353483774937810599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56167858207653865339959445 2632868353483774937810599)
      ·
        refine ⟨3949302530225662406715899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2632868353483774937810599 3949302530225662406715899)
        ·
          refine ⟨5923953795338493610073849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3949302530225662406715899 5923953795338493610073849)
          ·
            refine ⟨4442965346503870207555387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5923953795338493610073849 4442965346503870207555387)
            ·
              refine ⟨6664448019755805311333081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442965346503870207555387 6664448019755805311333081)
              ·
                refine ⟨4998336014816853983499811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6664448019755805311333081 4998336014816853983499811)
                ·
                  refine ⟨7497504022225280975249717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998336014816853983499811 7497504022225280975249717)
                  ·
                    refine ⟨702891002083620091429661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7497504022225280975249717 702891002083620091429661)
                    ·
                      rfl

theorem cell22_2053313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2053313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053313 prefixEnd_2053313 := by exact prefixLift 2053313
  have htrace : WordTrace (prefixWord ++ tailWord_2053313) baseStart_2053313 baseEnd_2053313 := by
    simpa [prefixWord, tailWord_2053313, baseEnd_2053313] using wordTrace_append hprefix tailTrace_2053313
  have hstable : (prefixWord ++ tailWord_2053313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053313).length < 2 ^ (prefixWord ++ tailWord_2053313).sum := by decide
  have hdescent : baseEnd_2053313 < baseStart_2053313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053326 : List Nat := [4, 1, 1, 1, 6, 9]
def baseStart_2053326 : Nat := 118140960795 + 2053326 * 2 ^ 59
def prefixEnd_2053326 : Nat := 4983230072969 + 3 ^ 40 * 2053326 * 2
def baseEnd_2053326 : Nat := 8677721632707313467341

theorem tailTrace_2053326 : CollatzResearch.WordTrace tailWord_2053326 prefixEnd_2053326 8677721632707313467341 := by
  unfold tailWord_2053326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361368969894757125854479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49927301172772038004557221 9361368969894757125854479)
  ·
    refine ⟨14042053454842135688781719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9361368969894757125854479 14042053454842135688781719)
    ·
      refine ⟨21063080182263203533172579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14042053454842135688781719 21063080182263203533172579)
      ·
        refine ⟨31594620273394805299758869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21063080182263203533172579 31594620273394805299758869)
        ·
          refine ⟨1480997825315381498426197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31594620273394805299758869 1480997825315381498426197)
          ·
            refine ⟨8677721632707313467341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1480997825315381498426197 8677721632707313467341)
            ·
              rfl

theorem cell22_2053326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 9].length) (baseStart_2053326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053326 prefixEnd_2053326 := by exact prefixLift 2053326
  have htrace : WordTrace (prefixWord ++ tailWord_2053326) baseStart_2053326 baseEnd_2053326 := by
    simpa [prefixWord, tailWord_2053326, baseEnd_2053326] using wordTrace_append hprefix tailTrace_2053326
  have hstable : (prefixWord ++ tailWord_2053326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053326).length < 2 ^ (prefixWord ++ tailWord_2053326).sum := by decide
  have hdescent : baseEnd_2053326 < baseStart_2053326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053369 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 1, 7]
def baseStart_2053369 : Nat := 118140960795 + 2053369 * 2 ^ 59
def prefixEnd_2053369 : Nat := 4983230072969 + 3 ^ 40 * 2053369 * 2
def baseEnd_2053369 : Nat := 702910172028054612029489

theorem tailTrace_2053369 : CollatzResearch.WordTrace tailWord_2053369 prefixEnd_2053369 702910172028054612029489 := by
  unfold tailWord_2053369
  simp only [CollatzResearch.WordTrace]
  refine ⟨74892520098002275350651161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49928346732001516900434107 74892520098002275350651161)
  ·
    refine ⟨56169390073501706512988371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74892520098002275350651161 56169390073501706512988371)
    ·
      refine ⟨84254085110252559769482557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56169390073501706512988371 84254085110252559769482557)
      ·
        refine ⟨31595281916344709913555959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84254085110252559769482557 31595281916344709913555959)
        ·
          refine ⟨47392922874517064870333939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31595281916344709913555959 47392922874517064870333939)
          ·
            refine ⟨71089384311775597305500909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47392922874517064870333939 71089384311775597305500909)
            ·
              refine ⟨26658519116915848989562841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71089384311775597305500909 26658519116915848989562841)
              ·
                refine ⟨19993889337686886742172131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26658519116915848989562841 19993889337686886742172131)
                ·
                  refine ⟨29990834006530330113258197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19993889337686886742172131 29990834006530330113258197)
                  ·
                    refine ⟨702910172028054612029489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29990834006530330113258197 702910172028054612029489)
                    ·
                      rfl

theorem cell22_2053369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_2053369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053369 prefixEnd_2053369 := by exact prefixLift 2053369
  have htrace : WordTrace (prefixWord ++ tailWord_2053369) baseStart_2053369 baseEnd_2053369 := by
    simpa [prefixWord, tailWord_2053369, baseEnd_2053369] using wordTrace_append hprefix tailTrace_2053369
  have hstable : (prefixWord ++ tailWord_2053369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053369).length < 2 ^ (prefixWord ++ tailWord_2053369).sum := by decide
  have hdescent : baseEnd_2053369 < baseStart_2053369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053375 : List Nat := [1, 1, 2, 2, 1, 6, 2, 3, 1, 3]
def baseStart_2053375 : Nat := 118140960795 + 2053375 * 2 ^ 59
def prefixEnd_2053375 : Nat := 4983230072969 + 3 ^ 40 * 2053375 * 2
def baseEnd_2053375 : Nat := 702912225950672596379471

theorem tailTrace_2053375 : CollatzResearch.WordTrace tailWord_2053375 prefixEnd_2053375 702912225950672596379471 := by
  unfold tailWord_2053375
  simp only [CollatzResearch.WordTrace]
  refine ⟨74892738935980538375369579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49928492623987025583579719 74892738935980538375369579)
  ·
    refine ⟨112339108403970807563054369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74892738935980538375369579 112339108403970807563054369)
    ·
      refine ⟨84254331302978105672290777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112339108403970807563054369 84254331302978105672290777)
      ·
        refine ⟨63190748477233579254218083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84254331302978105672290777 63190748477233579254218083)
        ·
          refine ⟨94786122715850368881327125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63190748477233579254218083 94786122715850368881327125)
          ·
            refine ⟨4443099502305486041312209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94786122715850368881327125 4443099502305486041312209)
            ·
              refine ⟨3332324626729114530984157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443099502305486041312209 3332324626729114530984157)
              ·
                refine ⟨1249621735023417949119059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3332324626729114530984157 1249621735023417949119059)
                ·
                  refine ⟨1874432602535126923678589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249621735023417949119059 1874432602535126923678589)
                  ·
                    refine ⟨702912225950672596379471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1874432602535126923678589 702912225950672596379471)
                    ·
                      rfl

theorem cell22_2053375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 1, 3].length) (baseStart_2053375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053375 prefixEnd_2053375 := by exact prefixLift 2053375
  have htrace : WordTrace (prefixWord ++ tailWord_2053375) baseStart_2053375 baseEnd_2053375 := by
    simpa [prefixWord, tailWord_2053375, baseEnd_2053375] using wordTrace_append hprefix tailTrace_2053375
  have hstable : (prefixWord ++ tailWord_2053375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053375).length < 2 ^ (prefixWord ++ tailWord_2053375).sum := by decide
  have hdescent : baseEnd_2053375 < baseStart_2053375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053388 : List Nat := [2, 2, 1, 2, 2, 5, 1, 2, 5]
def baseStart_2053388 : Nat := 118140960795 + 2053388 * 2 ^ 59
def prefixEnd_2053388 : Nat := 4983230072969 + 3 ^ 40 * 2053388 * 2
def baseEnd_2053388 : Nat := 234305558705448298601477

theorem tailTrace_2053388 : CollatzResearch.WordTrace tailWord_2053388 prefixEnd_2053388 234305558705448298601477 := by
  unfold tailWord_2053388
  simp only [CollatzResearch.WordTrace]
  refine ⟨37446606542466720797796409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49928808723288961063728545 37446606542466720797796409)
  ·
    refine ⟨28084954906850040598347307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37446606542466720797796409 28084954906850040598347307)
    ·
      refine ⟨42127432360275060897520961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28084954906850040598347307 42127432360275060897520961)
      ·
        refine ⟨31595574270206295673140721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42127432360275060897520961 31595574270206295673140721)
        ·
          refine ⟨23696680702654721754855541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31595574270206295673140721 23696680702654721754855541)
          ·
            refine ⟨2221563815873880164517707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23696680702654721754855541 2221563815873880164517707)
            ·
              refine ⟨3332345723810820246776561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221563815873880164517707 3332345723810820246776561)
              ·
                refine ⟨2499259292858115185082421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3332345723810820246776561 2499259292858115185082421)
                ·
                  refine ⟨234305558705448298601477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2499259292858115185082421 234305558705448298601477)
                  ·
                    rfl

theorem cell22_2053388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_2053388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053388 prefixEnd_2053388 := by exact prefixLift 2053388
  have htrace : WordTrace (prefixWord ++ tailWord_2053388) baseStart_2053388 baseEnd_2053388 := by
    simpa [prefixWord, tailWord_2053388, baseEnd_2053388] using wordTrace_append hprefix tailTrace_2053388
  have hstable : (prefixWord ++ tailWord_2053388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053388).length < 2 ^ (prefixWord ++ tailWord_2053388).sum := by decide
  have hdescent : baseEnd_2053388 < baseStart_2053388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053405 : List Nat := [1, 4, 2, 3, 1, 2, 3, 1, 5]
def baseStart_2053405 : Nat := 118140960795 + 2053405 * 2 ^ 59
def prefixEnd_2053405 : Nat := 4983230072969 + 3 ^ 40 * 2053405 * 2
def baseEnd_2053405 : Nat := 234307498521254172709793

theorem tailTrace_2053405 : CollatzResearch.WordTrace tailWord_2053405 prefixEnd_2053405 234307498521254172709793 := by
  unfold tailWord_2053405
  simp only [CollatzResearch.WordTrace]
  refine ⟨74893833125871853498961669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49929222083914568999307779 74893833125871853498961669)
  ·
    refine ⟨14042593711100972531055313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74893833125871853498961669 14042593711100972531055313)
    ·
      refine ⟨10531945283325729398291485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14042593711100972531055313 10531945283325729398291485)
      ·
        refine ⟨3949479481247148524359307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10531945283325729398291485 3949479481247148524359307)
        ·
          refine ⟨5924219221870722786538961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3949479481247148524359307 5924219221870722786538961)
          ·
            refine ⟨4443164416403042089904221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5924219221870722786538961 4443164416403042089904221)
            ·
              refine ⟨1666186656151140783714083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4443164416403042089904221 1666186656151140783714083)
              ·
                refine ⟨2499279984226711175571125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666186656151140783714083 2499279984226711175571125)
                ·
                  refine ⟨234307498521254172709793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2499279984226711175571125 234307498521254172709793)
                  ·
                    rfl

theorem cell22_2053405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_2053405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053405 prefixEnd_2053405 := by exact prefixLift 2053405
  have htrace : WordTrace (prefixWord ++ tailWord_2053405) baseStart_2053405 baseEnd_2053405 := by
    simpa [prefixWord, tailWord_2053405, baseEnd_2053405] using wordTrace_append hprefix tailTrace_2053405
  have hstable : (prefixWord ++ tailWord_2053405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053405).length < 2 ^ (prefixWord ++ tailWord_2053405).sum := by decide
  have hdescent : baseEnd_2053405 < baseStart_2053405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053448 : List Nat := [2, 1, 3, 1, 1, 2, 1, 6, 2, 3]
def baseStart_2053448 : Nat := 118140960795 + 2053448 * 2 ^ 59
def prefixEnd_2053448 : Nat := 4983230072969 + 3 ^ 40 * 2053448 * 2
def baseEnd_2053448 : Nat := 702937215342524739304247

theorem tailTrace_2053448 : CollatzResearch.WordTrace tailWord_2053448 prefixEnd_2053448 702937215342524739304247 := by
  unfold tailWord_2053448
  simp only [CollatzResearch.WordTrace]
  refine ⟨37447700732358035921388499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49930267643144047895184665 37447700732358035921388499)
  ·
    refine ⟨56171551098537053882082749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37447700732358035921388499 56171551098537053882082749)
    ·
      refine ⟨21064331661951395205781031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56171551098537053882082749 21064331661951395205781031)
      ·
        refine ⟨31596497492927092808671547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21064331661951395205781031 31596497492927092808671547)
        ·
          refine ⟨47394746239390639213007321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31596497492927092808671547 47394746239390639213007321)
          ·
            refine ⟨35546059679542979409755491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47394746239390639213007321 35546059679542979409755491)
            ·
              refine ⟨53319089519314469114633237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35546059679542979409755491 53319089519314469114633237)
              ·
                refine ⟨2499332321217865739748433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53319089519314469114633237 2499332321217865739748433)
                ·
                  refine ⟨1874499240913399304811325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2499332321217865739748433 1874499240913399304811325)
                  ·
                    refine ⟨702937215342524739304247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1874499240913399304811325 702937215342524739304247)
                    ·
                      rfl

theorem cell22_2053448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_2053448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053448 prefixEnd_2053448 := by exact prefixLift 2053448
  have htrace : WordTrace (prefixWord ++ tailWord_2053448) baseStart_2053448 baseEnd_2053448 := by
    simpa [prefixWord, tailWord_2053448, baseEnd_2053448] using wordTrace_append hprefix tailTrace_2053448
  have hstable : (prefixWord ++ tailWord_2053448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053448).length < 2 ^ (prefixWord ++ tailWord_2053448).sum := by decide
  have hdescent : baseEnd_2053448 < baseStart_2053448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053461 : List Nat := [1, 3, 2, 2, 3, 1, 1, 9]
def baseStart_2053461 : Nat := 118140960795 + 2053461 * 2 ^ 59
def prefixEnd_2053461 : Nat := 4983230072969 + 3 ^ 40 * 2053461 * 2
def baseEnd_2053461 : Nat := 78104629500910782081023

theorem tailTrace_2053461 : CollatzResearch.WordTrace tailWord_2053461 prefixEnd_2053461 78104629500910782081023 := by
  unfold tailWord_2053461
  simp only [CollatzResearch.WordTrace]
  refine ⟨74895875613668975063000237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49930583742445983375333491 74895875613668975063000237)
  ·
    refine ⟨28085953355125865648625089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74895875613668975063000237 28085953355125865648625089)
    ·
      refine ⟨21064465016344399236468817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28085953355125865648625089 21064465016344399236468817)
      ·
        refine ⟨15798348762258299427351613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21064465016344399236468817 15798348762258299427351613)
        ·
          refine ⟨5924380785846862285256855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15798348762258299427351613 5924380785846862285256855)
          ·
            refine ⟨8886571178770293427885283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5924380785846862285256855 8886571178770293427885283)
            ·
              refine ⟨13329856768155440141827925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8886571178770293427885283 13329856768155440141827925)
              ·
                refine ⟨78104629500910782081023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13329856768155440141827925 78104629500910782081023)
                ·
                  rfl

theorem cell22_2053461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 9].length) (baseStart_2053461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053461 prefixEnd_2053461 := by exact prefixLift 2053461
  have htrace : WordTrace (prefixWord ++ tailWord_2053461) baseStart_2053461 baseEnd_2053461 := by
    simpa [prefixWord, tailWord_2053461, baseEnd_2053461] using wordTrace_append hprefix tailTrace_2053461
  have hstable : (prefixWord ++ tailWord_2053461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053461).length < 2 ^ (prefixWord ++ tailWord_2053461).sum := by decide
  have hdescent : baseEnd_2053461 < baseStart_2053461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053465 : List Nat := [1, 2, 1, 2, 2, 2, 6, 1, 2, 3]
def baseStart_2053465 : Nat := 118140960795 + 2053465 * 2 ^ 59
def prefixEnd_2053465 : Nat := 4983230072969 + 3 ^ 40 * 2053465 * 2
def baseEnd_2053465 : Nat := 702943034789942361629195

theorem tailTrace_2053465 : CollatzResearch.WordTrace tailWord_2053465 prefixEnd_2053465 702943034789942361629195 := by
  unfold tailWord_2053465
  simp only [CollatzResearch.WordTrace]
  refine ⟨74896021505654483746145849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49930681003769655830763899 74896021505654483746145849)
  ·
    refine ⟨56172016129240862809609387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74896021505654483746145849 56172016129240862809609387)
    ·
      refine ⟨84258024193861294214414081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56172016129240862809609387 84258024193861294214414081)
      ·
        refine ⟨63193518145395970660810561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84258024193861294214414081 63193518145395970660810561)
        ·
          refine ⟨47395138609046977995607921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63193518145395970660810561 47395138609046977995607921)
          ·
            refine ⟨35546353956785233496705941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47395138609046977995607921 35546353956785233496705941)
            ·
              refine ⟨1666235341724307820158091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35546353956785233496705941 1666235341724307820158091)
              ·
                refine ⟨2499353012586461730237137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666235341724307820158091 2499353012586461730237137)
                ·
                  refine ⟨1874514759439846297677853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2499353012586461730237137 1874514759439846297677853)
                  ·
                    refine ⟨702943034789942361629195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1874514759439846297677853 702943034789942361629195)
                    ·
                      rfl

theorem cell22_2053465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 2, 3].length) (baseStart_2053465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053465 prefixEnd_2053465 := by exact prefixLift 2053465
  have htrace : WordTrace (prefixWord ++ tailWord_2053465) baseStart_2053465 baseEnd_2053465 := by
    simpa [prefixWord, tailWord_2053465, baseEnd_2053465] using wordTrace_append hprefix tailTrace_2053465
  have hstable : (prefixWord ++ tailWord_2053465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053465).length < 2 ^ (prefixWord ++ tailWord_2053465).sum := by decide
  have hdescent : baseEnd_2053465 < baseStart_2053465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053480 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 2, 4]
def baseStart_2053480 : Nat := 118140960795 + 2053480 * 2 ^ 59
def prefixEnd_2053480 : Nat := 4983230072969 + 3 ^ 40 * 2053480 * 2
def baseEnd_2053480 : Nat := 702948169596487322504149

theorem tailTrace_2053480 : CollatzResearch.WordTrace tailWord_2053480 prefixEnd_2053480 702948169596487322504149 := by
  unfold tailWord_2053480
  simp only [CollatzResearch.WordTrace]
  refine ⟨37448284300300070653970947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49931045733733427538627929 37448284300300070653970947)
  ·
    refine ⟨56172426450450105980956421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37448284300300070653970947 56172426450450105980956421)
    ·
      refine ⟨10532329959459394871429329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56172426450450105980956421 10532329959459394871429329)
      ·
        refine ⟨7899247469594546153571997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10532329959459394871429329 7899247469594546153571997)
        ·
          refine ⟨2962217801097954807589499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7899247469594546153571997 2962217801097954807589499)
          ·
            refine ⟨4443326701646932211384249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962217801097954807589499 4443326701646932211384249)
            ·
              refine ⟨3332495026235199158538187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443326701646932211384249 3332495026235199158538187)
              ·
                refine ⟨4998742539352798737807281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332495026235199158538187 4998742539352798737807281)
                ·
                  refine ⟨3749056904514599053355461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4998742539352798737807281 3749056904514599053355461)
                  ·
                    refine ⟨702948169596487322504149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3749056904514599053355461 702948169596487322504149)
                    ·
                      rfl

theorem cell22_2053480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_2053480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053480 prefixEnd_2053480 := by exact prefixLift 2053480
  have htrace : WordTrace (prefixWord ++ tailWord_2053480) baseStart_2053480 baseEnd_2053480 := by
    simpa [prefixWord, tailWord_2053480, baseEnd_2053480] using wordTrace_append hprefix tailTrace_2053480
  have hstable : (prefixWord ++ tailWord_2053480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053480).length < 2 ^ (prefixWord ++ tailWord_2053480).sum := by decide
  have hdescent : baseEnd_2053480 < baseStart_2053480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053521 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 2, 5]
def baseStart_2053521 : Nat := 118140960795 + 2053521 * 2 ^ 59
def prefixEnd_2053521 : Nat := 4983230072969 + 3 ^ 40 * 2053521 * 2
def baseEnd_2053521 : Nat := 702962204734376882229023

theorem tailTrace_2053521 : CollatzResearch.WordTrace tailWord_2053521 prefixEnd_2053521 702962204734376882229023 := by
  unfold tailWord_2053521
  simp only [CollatzResearch.WordTrace]
  refine ⟨74898063993451605310184417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49932042662301070206789611 74898063993451605310184417)
  ·
    refine ⟨56173547995088703982638313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74898063993451605310184417 56173547995088703982638313)
    ·
      refine ⟨42130160996316527986978735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56173547995088703982638313 42130160996316527986978735)
      ·
        refine ⟨63195241494474791980468103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42130160996316527986978735 63195241494474791980468103)
        ·
          refine ⟨94792862241712187970702155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63195241494474791980468103 94792862241712187970702155)
          ·
            refine ⟨142189293362568281956053233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94792862241712187970702155 142189293362568281956053233)
            ·
              refine ⟨106641970021926211467039925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142189293362568281956053233 106641970021926211467039925)
              ·
                refine ⟨9997684689555582325034993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106641970021926211467039925 9997684689555582325034993)
                ·
                  refine ⟨7498263517166686743776245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9997684689555582325034993 7498263517166686743776245)
                  ·
                    refine ⟨702962204734376882229023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7498263517166686743776245 702962204734376882229023)
                    ·
                      rfl

theorem cell22_2053521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_2053521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053521 prefixEnd_2053521 := by exact prefixLift 2053521
  have htrace : WordTrace (prefixWord ++ tailWord_2053521) baseStart_2053521 baseEnd_2053521 := by
    simpa [prefixWord, tailWord_2053521, baseEnd_2053521] using wordTrace_append hprefix tailTrace_2053521
  have hstable : (prefixWord ++ tailWord_2053521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053521).length < 2 ^ (prefixWord ++ tailWord_2053521).sum := by decide
  have hdescent : baseEnd_2053521 < baseStart_2053521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053583 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 1, 5]
def baseStart_2053583 : Nat := 118140960795 + 2053583 * 2 ^ 59
def prefixEnd_2053583 : Nat := 4983230072969 + 3 ^ 40 * 2053583 * 2
def baseEnd_2053583 : Nat := 702983428601429387178833

theorem tailTrace_2053583 : CollatzResearch.WordTrace tailWord_2053583 prefixEnd_2053583 702983428601429387178833 := by
  unfold tailWord_2053583
  simp only [CollatzResearch.WordTrace]
  refine ⟨74900325319226989898941403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49933550212817993265960935 74900325319226989898941403)
  ·
    refine ⟨112350487978840484848412105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74900325319226989898941403 112350487978840484848412105)
    ·
      refine ⟨84262865984130363636309079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112350487978840484848412105 84262865984130363636309079)
      ·
        refine ⟨126394298976195545454463619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84262865984130363636309079 126394298976195545454463619)
        ·
          refine ⟨189591448464293318181695429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126394298976195545454463619 189591448464293318181695429)
          ·
            refine ⟨35548396587054997159067893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189591448464293318181695429 35548396587054997159067893)
            ·
              refine ⟨3332662180036405983662615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35548396587054997159067893 3332662180036405983662615)
              ·
                refine ⟨4998993270054608975493923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332662180036405983662615 4998993270054608975493923)
                ·
                  refine ⟨7498489905081913463240885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998993270054608975493923 7498489905081913463240885)
                  ·
                    refine ⟨702983428601429387178833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7498489905081913463240885 702983428601429387178833)
                    ·
                      rfl

theorem cell22_2053583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_2053583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053583 prefixEnd_2053583 := by exact prefixLift 2053583
  have htrace : WordTrace (prefixWord ++ tailWord_2053583) baseStart_2053583 baseEnd_2053583 := by
    simpa [prefixWord, tailWord_2053583, baseEnd_2053583] using wordTrace_append hprefix tailTrace_2053583
  have hstable : (prefixWord ++ tailWord_2053583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053583).length < 2 ^ (prefixWord ++ tailWord_2053583).sum := by decide
  have hdescent : baseEnd_2053583 < baseStart_2053583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053634 : List Nat := [3, 4, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_2053634 : Nat := 118140960795 + 2053634 * 2 ^ 59
def prefixEnd_2053634 : Nat := 4983230072969 + 3 ^ 40 * 2053634 * 2
def baseEnd_2053634 : Nat := 703000886943682254153677

theorem tailTrace_2053634 : CollatzResearch.WordTrace tailWord_2053634 prefixEnd_2053634 703000886943682254153677 := by
  unfold tailWord_2053634
  simp only [CollatzResearch.WordTrace]
  refine ⟨18725546360510556402261989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49934790294694817072698637 18725546360510556402261989)
  ·
    refine ⟨3511039942595729325424123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18725546360510556402261989 3511039942595729325424123)
    ·
      refine ⟨5266559913893593988136185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511039942595729325424123 5266559913893593988136185)
      ·
        refine ⟨3949919935420195491102139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5266559913893593988136185 3949919935420195491102139)
        ·
          refine ⟨5924879903130293236653209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3949919935420195491102139 5924879903130293236653209)
          ·
            refine ⟨4443659927347719927489907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5924879903130293236653209 4443659927347719927489907)
            ·
              refine ⟨6665489891021579891234861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4443659927347719927489907 6665489891021579891234861)
              ·
                refine ⟨2499558709133092459213073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6665489891021579891234861 2499558709133092459213073)
                ·
                  refine ⟨1874669031849819344409805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2499558709133092459213073 1874669031849819344409805)
                  ·
                    refine ⟨703000886943682254153677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1874669031849819344409805 703000886943682254153677)
                    ·
                      rfl

theorem cell22_2053634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_2053634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053634 prefixEnd_2053634 := by exact prefixLift 2053634
  have htrace : WordTrace (prefixWord ++ tailWord_2053634) baseStart_2053634 baseEnd_2053634 := by
    simpa [prefixWord, tailWord_2053634, baseEnd_2053634] using wordTrace_append hprefix tailTrace_2053634
  have hstable : (prefixWord ++ tailWord_2053634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053634).length < 2 ^ (prefixWord ++ tailWord_2053634).sum := by decide
  have hdescent : baseEnd_2053634 < baseStart_2053634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053638 : List Nat := [6, 2, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2053638 : Nat := 118140960795 + 2053638 * 2 ^ 59
def prefixEnd_2053638 : Nat := 4983230072969 + 3 ^ 40 * 2053638 * 2
def baseEnd_2053638 : Nat := 703002256225427577053665

theorem tailTrace_2053638 : CollatzResearch.WordTrace tailWord_2053638 prefixEnd_2053638 703002256225427577053665 := by
  unfold tailWord_2053638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340697854188366696631049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49934887556018489528129045 2340697854188366696631049)
  ·
    refine ⟨1755523390641275022473287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2340697854188366696631049 1755523390641275022473287)
    ·
      refine ⟨2633285085961912533709931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1755523390641275022473287 2633285085961912533709931)
      ·
        refine ⟨3949927628942868800564897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2633285085961912533709931 3949927628942868800564897)
        ·
          refine ⟨2962445721707151600423673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3949927628942868800564897 2962445721707151600423673)
          ·
            refine ⟨2221834291280363700317755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2962445721707151600423673 2221834291280363700317755)
            ·
              refine ⟨3332751436920545550476633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221834291280363700317755 3332751436920545550476633)
              ·
                refine ⟨2499563577690409162857475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3332751436920545550476633 2499563577690409162857475)
                ·
                  refine ⟨3749345366535613744286213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499563577690409162857475 3749345366535613744286213)
                  ·
                    refine ⟨703002256225427577053665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3749345366535613744286213 703002256225427577053665)
                    ·
                      rfl

theorem cell22_2053638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2053638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053638 prefixEnd_2053638 := by exact prefixLift 2053638
  have htrace : WordTrace (prefixWord ++ tailWord_2053638) baseStart_2053638 baseEnd_2053638 := by
    simpa [prefixWord, tailWord_2053638, baseEnd_2053638] using wordTrace_append hprefix tailTrace_2053638
  have hstable : (prefixWord ++ tailWord_2053638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053638).length < 2 ^ (prefixWord ++ tailWord_2053638).sum := by decide
  have hdescent : baseEnd_2053638 < baseStart_2053638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053763 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 1, 9]
def baseStart_2053763 : Nat := 118140960795 + 2053763 * 2 ^ 59
def prefixEnd_2053763 : Nat := 4983230072969 + 3 ^ 40 * 2053763 * 2
def baseEnd_2053763 : Nat := 703045046279968917678281

theorem tailTrace_2053763 : CollatzResearch.WordTrace tailWord_2053763 prefixEnd_2053763 703045046279968917678281 := by
  unfold tailWord_2053763
  simp only [CollatzResearch.WordTrace]
  refine ⟨74906890458574880640493943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49937926972383253760329295 74906890458574880640493943)
  ·
    refine ⟨112360335687862320960740915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74906890458574880640493943 112360335687862320960740915)
    ·
      refine ⟨168540503531793481441111373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112360335687862320960740915 168540503531793481441111373)
      ·
        refine ⟨63202688824422555540416765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168540503531793481441111373 63202688824422555540416765)
        ·
          refine ⟨23701008309158458327656287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63202688824422555540416765 23701008309158458327656287)
          ·
            refine ⟨35551512463737687491484431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23701008309158458327656287 35551512463737687491484431)
            ·
              refine ⟨53327268695606531237226647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35551512463737687491484431 53327268695606531237226647)
              ·
                refine ⟨79990903043409796855839971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53327268695606531237226647 79990903043409796855839971)
                ·
                  refine ⟨119986354565114695283759957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79990903043409796855839971 119986354565114695283759957)
                  ·
                    refine ⟨703045046279968917678281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 119986354565114695283759957 703045046279968917678281)
                    ·
                      rfl

theorem cell22_2053763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_2053763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053763 prefixEnd_2053763 := by exact prefixLift 2053763
  have htrace : WordTrace (prefixWord ++ tailWord_2053763) baseStart_2053763 baseEnd_2053763 := by
    simpa [prefixWord, tailWord_2053763, baseEnd_2053763] using wordTrace_append hprefix tailTrace_2053763
  have hstable : (prefixWord ++ tailWord_2053763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053763).length < 2 ^ (prefixWord ++ tailWord_2053763).sum := by decide
  have hdescent : baseEnd_2053763 < baseStart_2053763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053797 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 3, 3]
def baseStart_2053797 : Nat := 118140960795 + 2053797 * 2 ^ 59
def prefixEnd_2053797 : Nat := 4983230072969 + 3 ^ 40 * 2053797 * 2
def baseEnd_2053797 : Nat := 703056685174804162328177

theorem tailTrace_2053797 : CollatzResearch.WordTrace tailWord_2053797 prefixEnd_2053797 703056685174804162328177 := by
  unfold tailWord_2053797
  simp only [CollatzResearch.WordTrace]
  refine ⟨74908130540451704447231645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49938753693634469631487763 74908130540451704447231645)
  ·
    refine ⟨28090548952669389167711867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74908130540451704447231645 28090548952669389167711867)
    ·
      refine ⟨42135823429004083751567801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28090548952669389167711867 42135823429004083751567801)
      ·
        refine ⟨31601867571753062813675851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42135823429004083751567801 31601867571753062813675851)
        ·
          refine ⟨47402801357629594220513777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31601867571753062813675851 47402801357629594220513777)
          ·
            refine ⟨35552101018222195665385333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47402801357629594220513777 35552101018222195665385333)
            ·
              refine ⟨3333009470458330843629875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35552101018222195665385333 3333009470458330843629875)
              ·
                refine ⟨4999514205687496265444813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333009470458330843629875 4999514205687496265444813)
                ·
                  refine ⟨1874817827132811099541805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4999514205687496265444813 1874817827132811099541805)
                  ·
                    refine ⟨703056685174804162328177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1874817827132811099541805 703056685174804162328177)
                    ·
                      rfl

theorem cell22_2053797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_2053797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053797 prefixEnd_2053797 := by exact prefixLift 2053797
  have htrace : WordTrace (prefixWord ++ tailWord_2053797) baseStart_2053797 baseEnd_2053797 := by
    simpa [prefixWord, tailWord_2053797, baseEnd_2053797] using wordTrace_append hprefix tailTrace_2053797
  have hstable : (prefixWord ++ tailWord_2053797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053797).length < 2 ^ (prefixWord ++ tailWord_2053797).sum := by decide
  have hdescent : baseEnd_2053797 < baseStart_2053797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053844 : List Nat := [2, 4, 1, 3, 1, 2, 2, 2, 5]
def baseStart_2053844 : Nat := 118140960795 + 2053844 * 2 ^ 59
def prefixEnd_2053844 : Nat := 4983230072969 + 3 ^ 40 * 2053844 * 2
def baseEnd_2053844 : Nat := 234357591411770568801011

theorem tailTrace_2053844 : CollatzResearch.WordTrace tailWord_2053844 prefixEnd_2053844 234357591411770568801011 := by
  unfold tailWord_2053844
  simp only [CollatzResearch.WordTrace]
  refine ⟨37454922385640715737096293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49939896514187620982795057 37454922385640715737096293)
  ·
    refine ⟨7022797947307634200705555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37454922385640715737096293 7022797947307634200705555)
    ·
      refine ⟨10534196920961451301058333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7022797947307634200705555 10534196920961451301058333)
      ·
        refine ⟨3950323845360544237896875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10534196920961451301058333 3950323845360544237896875)
        ·
          refine ⟨5925485768040816356845313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3950323845360544237896875 5925485768040816356845313)
          ·
            refine ⟨4444114326030612267633985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5925485768040816356845313 4444114326030612267633985)
            ·
              refine ⟨3333085744522959200725489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4444114326030612267633985 3333085744522959200725489)
              ·
                refine ⟨2499814308392219400544117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3333085744522959200725489 2499814308392219400544117)
                ·
                  refine ⟨234357591411770568801011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2499814308392219400544117 234357591411770568801011)
                  ·
                    rfl

theorem cell22_2053844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_2053844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053844 prefixEnd_2053844 := by exact prefixLift 2053844
  have htrace : WordTrace (prefixWord ++ tailWord_2053844) baseStart_2053844 baseEnd_2053844 := by
    simpa [prefixWord, tailWord_2053844, baseEnd_2053844] using wordTrace_append hprefix tailTrace_2053844
  have hstable : (prefixWord ++ tailWord_2053844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053844).length < 2 ^ (prefixWord ++ tailWord_2053844).sum := by decide
  have hdescent : baseEnd_2053844 < baseStart_2053844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053855 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 6]
def baseStart_2053855 : Nat := 118140960795 + 2053855 * 2 ^ 59
def prefixEnd_2053855 : Nat := 4983230072969 + 3 ^ 40 * 2053855 * 2
def baseEnd_2053855 : Nat := 234358846586703781459333

theorem tailTrace_2053855 : CollatzResearch.WordTrace tailWord_2053855 prefixEnd_2053855 234358846586703781459333 := by
  unfold tailWord_2053855
  simp only [CollatzResearch.WordTrace]
  refine ⟨74910245974241580352843019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49940163982827720235228679 74910245974241580352843019)
  ·
    refine ⟨112365368961362370529264529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74910245974241580352843019 112365368961362370529264529)
    ·
      refine ⟨84274026721021777896948397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112365368961362370529264529 84274026721021777896948397)
      ·
        refine ⟨31602760020383166711355649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84274026721021777896948397 31602760020383166711355649)
        ·
          refine ⟨23702070015287375033516737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31602760020383166711355649 23702070015287375033516737)
          ·
            refine ⟨17776552511465531275137553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23702070015287375033516737 17776552511465531275137553)
            ·
              refine ⟨13332414383599148456353165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17776552511465531275137553 13332414383599148456353165)
              ·
                refine ⟨4999655393849680671132437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13332414383599148456353165 4999655393849680671132437)
                ·
                  refine ⟨234358846586703781459333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4999655393849680671132437 234358846586703781459333)
                  ·
                    rfl

theorem cell22_2053855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 6].length) (baseStart_2053855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053855 prefixEnd_2053855 := by exact prefixLift 2053855
  have htrace : WordTrace (prefixWord ++ tailWord_2053855) baseStart_2053855 baseEnd_2053855 := by
    simpa [prefixWord, tailWord_2053855, baseEnd_2053855] using wordTrace_append hprefix tailTrace_2053855
  have hstable : (prefixWord ++ tailWord_2053855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053855).length < 2 ^ (prefixWord ++ tailWord_2053855).sum := by decide
  have hdescent : baseEnd_2053855 < baseStart_2053855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053902 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_2053902 : Nat := 118140960795 + 2053902 * 2 ^ 59
def prefixEnd_2053902 : Nat := 4983230072969 + 3 ^ 40 * 2053902 * 2
def baseEnd_2053902 : Nat := 703092628820618888452855

theorem tailTrace_2053902 : CollatzResearch.WordTrace tailWord_2053902 prefixEnd_2053902 703092628820618888452855 := by
  unfold tailWord_2053902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9363995025633913422475495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49941306803380871586535973 9363995025633913422475495)
  ·
    refine ⟨14045992538450870133713243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9363995025633913422475495 14045992538450870133713243)
    ·
      refine ⟨21068988807676305200569865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14045992538450870133713243 21068988807676305200569865)
      ·
        refine ⟨15801741605757228900427399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21068988807676305200569865 15801741605757228900427399)
        ·
          refine ⟨23702612408635843350641099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15801741605757228900427399 23702612408635843350641099)
          ·
            refine ⟨35553918612953765025961649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23702612408635843350641099 35553918612953765025961649)
            ·
              refine ⟨26665438959715323769471237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35553918612953765025961649 26665438959715323769471237)
              ·
                refine ⟨4999769804946623206775857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26665438959715323769471237 4999769804946623206775857)
                ·
                  refine ⟨3749827353709967405081893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4999769804946623206775857 3749827353709967405081893)
                  ·
                    refine ⟨703092628820618888452855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3749827353709967405081893 703092628820618888452855)
                    ·
                      rfl

theorem cell22_2053902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_2053902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053902 prefixEnd_2053902 := by exact prefixLift 2053902
  have htrace : WordTrace (prefixWord ++ tailWord_2053902) baseStart_2053902 baseEnd_2053902 := by
    simpa [prefixWord, tailWord_2053902, baseEnd_2053902] using wordTrace_append hprefix tailTrace_2053902
  have hstable : (prefixWord ++ tailWord_2053902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053902).length < 2 ^ (prefixWord ++ tailWord_2053902).sum := by decide
  have hdescent : baseEnd_2053902 < baseStart_2053902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053906 : List Nat := [3, 2, 4, 1, 1, 1, 2, 4, 4]
def baseStart_2053906 : Nat := 118140960795 + 2053906 * 2 ^ 59
def prefixEnd_2053906 : Nat := 4983230072969 + 3 ^ 40 * 2053906 * 2
def baseEnd_2053906 : Nat := 234364666034121403784281

theorem tailTrace_2053906 : CollatzResearch.WordTrace tailWord_2053906 prefixEnd_2053906 234364666034121403784281 := by
  unfold tailWord_2053906
  simp only [CollatzResearch.WordTrace]
  refine ⟨18728026524264204015737393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49941404064704544041966381 18728026524264204015737393)
  ·
    refine ⟨14046019893198153011803045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18728026524264204015737393 14046019893198153011803045)
    ·
      refine ⟨2633628729974653689713071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14046019893198153011803045 2633628729974653689713071)
      ·
        refine ⟨3950443094961980534569607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2633628729974653689713071 3950443094961980534569607)
        ·
          refine ⟨5925664642442970801854411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3950443094961980534569607 5925664642442970801854411)
          ·
            refine ⟨8888496963664456202781617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5925664642442970801854411 8888496963664456202781617)
            ·
              refine ⟨6666372722748342152086213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8888496963664456202781617 6666372722748342152086213)
              ·
                refine ⟨1249944885515314153516165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6666372722748342152086213 1249944885515314153516165)
                ·
                  refine ⟨234364666034121403784281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1249944885515314153516165 234364666034121403784281)
                  ·
                    rfl

theorem cell22_2053906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_2053906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053906 prefixEnd_2053906 := by exact prefixLift 2053906
  have htrace : WordTrace (prefixWord ++ tailWord_2053906) baseStart_2053906 baseEnd_2053906 := by
    simpa [prefixWord, tailWord_2053906, baseEnd_2053906] using wordTrace_append hprefix tailTrace_2053906
  have hstable : (prefixWord ++ tailWord_2053906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053906).length < 2 ^ (prefixWord ++ tailWord_2053906).sum := by decide
  have hdescent : baseEnd_2053906 < baseStart_2053906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053921 : List Nat := [1, 2, 3, 2, 1, 4, 3, 1, 2, 3]
def baseStart_2053921 : Nat := 118140960795 + 2053921 * 2 ^ 59
def prefixEnd_2053921 : Nat := 4983230072969 + 3 ^ 40 * 2053921 * 2
def baseEnd_2053921 : Nat := 703099132908909172227797

theorem tailTrace_2053921 : CollatzResearch.WordTrace tailWord_2053921 prefixEnd_2053921 703099132908909172227797 := by
  unfold tailWord_2053921
  simp only [CollatzResearch.WordTrace]
  refine ⟨74912653192002473624745617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49941768794668315749830411 74912653192002473624745617)
  ·
    refine ⟨56184489894001855218559213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74912653192002473624745617 56184489894001855218559213)
    ·
      refine ⟨21069183710250695706959705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56184489894001855218559213 21069183710250695706959705)
      ·
        refine ⟨15801887782688021780219779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21069183710250695706959705 15801887782688021780219779)
        ·
          refine ⟨23702831674032032670329669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15801887782688021780219779 23702831674032032670329669)
          ·
            refine ⟨4444280938881006125686813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23702831674032032670329669 4444280938881006125686813)
            ·
              refine ⟨1666605352080377297132555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4444280938881006125686813 1666605352080377297132555)
              ·
                refine ⟨2499908028120565945698833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666605352080377297132555 2499908028120565945698833)
                ·
                  refine ⟨1874931021090424459274125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2499908028120565945698833 1874931021090424459274125)
                  ·
                    refine ⟨703099132908909172227797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1874931021090424459274125 703099132908909172227797)
                    ·
                      rfl

theorem cell22_2053921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_2053921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053921 prefixEnd_2053921 := by exact prefixLift 2053921
  have htrace : WordTrace (prefixWord ++ tailWord_2053921) baseStart_2053921 baseEnd_2053921 := by
    simpa [prefixWord, tailWord_2053921, baseEnd_2053921] using wordTrace_append hprefix tailTrace_2053921
  have hstable : (prefixWord ++ tailWord_2053921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053921).length < 2 ^ (prefixWord ++ tailWord_2053921).sum := by decide
  have hdescent : baseEnd_2053921 < baseStart_2053921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053934 : List Nat := [4, 1, 3, 2, 2, 1, 1, 8]
def baseStart_2053934 : Nat := 118140960795 + 2053934 * 2 ^ 59
def prefixEnd_2053934 : Nat := 4983230072969 + 3 ^ 40 * 2053934 * 2
def baseEnd_2053934 : Nat := 78122620341620163516973

theorem tailTrace_2053934 : CollatzResearch.WordTrace tailWord_2053934 prefixEnd_2053934 78122620341620163516973 := by
  unfold tailWord_2053934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9364140917619422105621107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49942084893970251229979237 9364140917619422105621107)
  ·
    refine ⟨14046211376429133158431661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9364140917619422105621107 14046211376429133158431661)
    ·
      refine ⟨5267329266160924934411873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14046211376429133158431661 5267329266160924934411873)
      ·
        refine ⟨3950496949620693700808905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5267329266160924934411873 3950496949620693700808905)
        ·
          refine ⟨2962872712215520275606679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3950496949620693700808905 2962872712215520275606679)
          ·
            refine ⟨4444309068323280413410019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962872712215520275606679 4444309068323280413410019)
            ·
              refine ⟨6666463602484920620115029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4444309068323280413410019 6666463602484920620115029)
              ·
                refine ⟨78122620341620163516973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6666463602484920620115029 78122620341620163516973)
                ·
                  rfl

theorem cell22_2053934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_2053934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053934 prefixEnd_2053934 := by exact prefixLift 2053934
  have htrace : WordTrace (prefixWord ++ tailWord_2053934) baseStart_2053934 baseEnd_2053934 := by
    simpa [prefixWord, tailWord_2053934, baseEnd_2053934] using wordTrace_append hprefix tailTrace_2053934
  have hstable : (prefixWord ++ tailWord_2053934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053934).length < 2 ^ (prefixWord ++ tailWord_2053934).sum := by decide
  have hdescent : baseEnd_2053934 < baseStart_2053934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053962 : List Nat := [3, 1, 2, 1, 1, 1, 4, 4, 5]
def baseStart_2053962 : Nat := 118140960795 + 2053962 * 2 ^ 59
def prefixEnd_2053962 : Nat := 4983230072969 + 3 ^ 40 * 2053962 * 2
def baseEnd_2053962 : Nat := 234371056015599577317557

theorem tailTrace_2053962 : CollatzResearch.WordTrace tailWord_2053962 prefixEnd_2053962 234371056015599577317557 := by
  unfold tailWord_2053962
  simp only [CollatzResearch.WordTrace]
  refine ⟨18728537146213484406747035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49942765723235958417992093 18728537146213484406747035)
  ·
    refine ⟨28092805719320226610120553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18728537146213484406747035 28092805719320226610120553)
    ·
      refine ⟨21069604289490169957590415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28092805719320226610120553 21069604289490169957590415)
      ·
        refine ⟨31604406434235254936385623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21069604289490169957590415 31604406434235254936385623)
        ·
          refine ⟨47406609651352882404578435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31604406434235254936385623 47406609651352882404578435)
          ·
            refine ⟨71109914477029323606867653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47406609651352882404578435 71109914477029323606867653)
            ·
              refine ⟨13333108964442998176287685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71109914477029323606867653 13333108964442998176287685)
              ·
                refine ⟨2499957930833062158053941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13333108964442998176287685 2499957930833062158053941)
                ·
                  refine ⟨234371056015599577317557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2499957930833062158053941 234371056015599577317557)
                  ·
                    rfl

theorem cell22_2053962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_2053962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2053962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2053962 prefixEnd_2053962 := by exact prefixLift 2053962
  have htrace : WordTrace (prefixWord ++ tailWord_2053962) baseStart_2053962 baseEnd_2053962 := by
    simpa [prefixWord, tailWord_2053962, baseEnd_2053962] using wordTrace_append hprefix tailTrace_2053962
  have hstable : (prefixWord ++ tailWord_2053962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053962).length < 2 ^ (prefixWord ++ tailWord_2053962).sum := by decide
  have hdescent : baseEnd_2053962 < baseStart_2053962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054017 : List Nat := [1, 2, 4, 4, 1, 2, 2, 2, 1, 3]
def baseStart_2054017 : Nat := 118140960795 + 2054017 * 2 ^ 59
def prefixEnd_2054017 : Nat := 4983230072969 + 3 ^ 40 * 2054017 * 2
def baseEnd_2054017 : Nat := 703131995670796921827503

theorem tailTrace_2054017 : CollatzResearch.WordTrace tailWord_2054017 prefixEnd_2054017 703131995670796921827503 := by
  unfold tailWord_2054017
  simp only [CollatzResearch.WordTrace]
  refine ⟨74916154599654682020240305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49944103066436454680160203 74916154599654682020240305)
  ·
    refine ⟨56187115949741011515180229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74916154599654682020240305 56187115949741011515180229)
    ·
      refine ⟨10535084240576439659096293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56187115949741011515180229 10535084240576439659096293)
      ·
        refine ⟨1975328295108082436080555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10535084240576439659096293 1975328295108082436080555)
        ·
          refine ⟨2962992442662123654120833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975328295108082436080555 2962992442662123654120833)
          ·
            refine ⟨2222244331996592740590625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2962992442662123654120833 2222244331996592740590625)
            ·
              refine ⟨1666683248997444555442969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222244331996592740590625 1666683248997444555442969)
              ·
                refine ⟨1250012436748083416582227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1666683248997444555442969 1250012436748083416582227)
                ·
                  refine ⟨1875018655122125124873341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250012436748083416582227 1875018655122125124873341)
                  ·
                    refine ⟨703131995670796921827503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1875018655122125124873341 703131995670796921827503)
                    ·
                      rfl

theorem cell22_2054017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_2054017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054017 prefixEnd_2054017 := by exact prefixLift 2054017
  have htrace : WordTrace (prefixWord ++ tailWord_2054017) baseStart_2054017 baseEnd_2054017 := by
    simpa [prefixWord, tailWord_2054017, baseEnd_2054017] using wordTrace_append hprefix tailTrace_2054017
  have hstable : (prefixWord ++ tailWord_2054017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054017).length < 2 ^ (prefixWord ++ tailWord_2054017).sum := by decide
  have hdescent : baseEnd_2054017 < baseStart_2054017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054037 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_2054037 : Nat := 118140960795 + 2054037 * 2 ^ 59
def prefixEnd_2054037 : Nat := 4983230072969 + 3 ^ 40 * 2054037 * 2
def baseEnd_2054037 : Nat := 703138842079523536327441

theorem tailTrace_2054037 : CollatzResearch.WordTrace tailWord_2054037 prefixEnd_2054037 703138842079523536327441 := by
  unfold tailWord_2054037
  simp only [CollatzResearch.WordTrace]
  refine ⟨74916884059582225435968365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49944589373054816957312243 74916884059582225435968365)
  ·
    refine ⟨28093831522343334538488137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74916884059582225435968365 28093831522343334538488137)
    ·
      refine ⟨21070373641757500903866103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28093831522343334538488137 21070373641757500903866103)
      ·
        refine ⟨31605560462636251355799155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21070373641757500903866103 31605560462636251355799155)
        ·
          refine ⟨47408340693954377033698733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31605560462636251355799155 47408340693954377033698733)
          ·
            refine ⟨17778127760232891387637025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47408340693954377033698733 17778127760232891387637025)
            ·
              refine ⟨13333595820174668540727769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17778127760232891387637025 13333595820174668540727769)
              ·
                refine ⟨10000196865131001405545827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13333595820174668540727769 10000196865131001405545827)
                ·
                  refine ⟨15000295297696502108318741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10000196865131001405545827 15000295297696502108318741)
                  ·
                    refine ⟨703138842079523536327441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15000295297696502108318741 703138842079523536327441)
                    ·
                      rfl

theorem cell22_2054037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_2054037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054037 prefixEnd_2054037 := by exact prefixLift 2054037
  have htrace : WordTrace (prefixWord ++ tailWord_2054037) baseStart_2054037 baseEnd_2054037 := by
    simpa [prefixWord, tailWord_2054037, baseEnd_2054037] using wordTrace_append hprefix tailTrace_2054037
  have hstable : (prefixWord ++ tailWord_2054037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054037).length < 2 ^ (prefixWord ++ tailWord_2054037).sum := by decide
  have hdescent : baseEnd_2054037 < baseStart_2054037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054039 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 1, 5]
def baseStart_2054039 : Nat := 118140960795 + 2054039 * 2 ^ 59
def prefixEnd_2054039 : Nat := 4983230072969 + 3 ^ 40 * 2054039 * 2
def baseEnd_2054039 : Nat := 703139526720396197777435

theorem tailTrace_2054039 : CollatzResearch.WordTrace tailWord_2054039 prefixEnd_2054039 703139526720396197777435 := by
  unfold tailWord_2054039
  simp only [CollatzResearch.WordTrace]
  refine ⟨74916957005574979777541171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49944638003716653185027447 74916957005574979777541171)
  ·
    refine ⟨112375435508362469666311757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74916957005574979777541171 112375435508362469666311757)
    ·
      refine ⟨42140788315635926124866909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112375435508362469666311757 42140788315635926124866909)
      ·
        refine ⟨15802795618363472296825091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42140788315635926124866909 15802795618363472296825091)
        ·
          refine ⟨23704193427545208445237637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15802795618363472296825091 23704193427545208445237637)
          ·
            refine ⟨4444536267664726583482057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23704193427545208445237637 4444536267664726583482057)
            ·
              refine ⟨3333402200748544937611543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4444536267664726583482057 3333402200748544937611543)
              ·
                refine ⟨5000103301122817406417315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333402200748544937611543 5000103301122817406417315)
                ·
                  refine ⟨7500154951684226109625973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5000103301122817406417315 7500154951684226109625973)
                  ·
                    refine ⟨703139526720396197777435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7500154951684226109625973 703139526720396197777435)
                    ·
                      rfl

theorem cell22_2054039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_2054039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054039 prefixEnd_2054039 := by exact prefixLift 2054039
  have htrace : WordTrace (prefixWord ++ tailWord_2054039) baseStart_2054039 baseEnd_2054039 := by
    simpa [prefixWord, tailWord_2054039, baseEnd_2054039] using wordTrace_append hprefix tailTrace_2054039
  have hstable : (prefixWord ++ tailWord_2054039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054039).length < 2 ^ (prefixWord ++ tailWord_2054039).sum := by decide
  have hdescent : baseEnd_2054039 < baseStart_2054039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054101 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 3, 3]
def baseStart_2054101 : Nat := 118140960795 + 2054101 * 2 ^ 59
def prefixEnd_2054101 : Nat := 4983230072969 + 3 ^ 40 * 2054101 * 2
def baseEnd_2054101 : Nat := 703160750587448702727245

theorem tailTrace_2054101 : CollatzResearch.WordTrace tailWord_2054101 prefixEnd_2054101 703160750587448702727245 := by
  unfold tailWord_2054101
  simp only [CollatzResearch.WordTrace]
  refine ⟨74919218331350364366298157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49946145554233576244198771 74919218331350364366298157)
  ·
    refine ⟨28094706874256386637361809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74919218331350364366298157 28094706874256386637361809)
    ·
      refine ⟨21071030155692289978021357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28094706874256386637361809 21071030155692289978021357)
      ·
        refine ⟨7901636308384608741758009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21071030155692289978021357 7901636308384608741758009)
        ·
          refine ⟨5926227231288456556318507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7901636308384608741758009 5926227231288456556318507)
          ·
            refine ⟨8889340846932684834477761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5926227231288456556318507 8889340846932684834477761)
            ·
              refine ⟨6667005635199513625858321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8889340846932684834477761 6667005635199513625858321)
              ·
                refine ⟨5000254226399635219393741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6667005635199513625858321 5000254226399635219393741)
                ·
                  refine ⟨1875095334899863207272653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5000254226399635219393741 1875095334899863207272653)
                  ·
                    refine ⟨703160750587448702727245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1875095334899863207272653 703160750587448702727245)
                    ·
                      rfl

theorem cell22_2054101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_2054101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054101 prefixEnd_2054101 := by exact prefixLift 2054101
  have htrace : WordTrace (prefixWord ++ tailWord_2054101) baseStart_2054101 baseEnd_2054101 := by
    simpa [prefixWord, tailWord_2054101, baseEnd_2054101] using wordTrace_append hprefix tailTrace_2054101
  have hstable : (prefixWord ++ tailWord_2054101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054101).length < 2 ^ (prefixWord ++ tailWord_2054101).sum := by decide
  have hdescent : baseEnd_2054101 < baseStart_2054101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054112 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 1, 7]
def baseStart_2054112 : Nat := 118140960795 + 2054112 * 2 ^ 59
def prefixEnd_2054112 : Nat := 4983230072969 + 3 ^ 40 * 2054112 * 2
def baseEnd_2054112 : Nat := 703164516112248340702211

theorem tailTrace_2054112 : CollatzResearch.WordTrace tailWord_2054112 prefixEnd_2054112 703164516112248340702211 := by
  unfold tailWord_2054112
  simp only [CollatzResearch.WordTrace]
  refine ⟨37459809767155256622474295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49946413022873675496632393 37459809767155256622474295)
  ·
    refine ⟨56189714650732884933711443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37459809767155256622474295 56189714650732884933711443)
    ·
      refine ⟨84284571976099327400567165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56189714650732884933711443 84284571976099327400567165)
      ·
        refine ⟨31606714491037247775212687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84284571976099327400567165 31606714491037247775212687)
        ·
          refine ⟨47410071736555871662819031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31606714491037247775212687 47410071736555871662819031)
          ·
            refine ⟨71115107604833807494228547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47410071736555871662819031 71115107604833807494228547)
            ·
              refine ⟨106672661407250711241342821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71115107604833807494228547 106672661407250711241342821)
              ·
                refine ⟨20001124013859508357751779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106672661407250711241342821 20001124013859508357751779)
                ·
                  refine ⟨30001686020789262536627669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20001124013859508357751779 30001686020789262536627669)
                  ·
                    refine ⟨703164516112248340702211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30001686020789262536627669 703164516112248340702211)
                    ·
                      rfl

theorem cell22_2054112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_2054112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054112 prefixEnd_2054112 := by exact prefixLift 2054112
  have htrace : WordTrace (prefixWord ++ tailWord_2054112) baseStart_2054112 baseEnd_2054112 := by
    simpa [prefixWord, tailWord_2054112, baseEnd_2054112] using wordTrace_append hprefix tailTrace_2054112
  have hstable : (prefixWord ++ tailWord_2054112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054112).length < 2 ^ (prefixWord ++ tailWord_2054112).sum := by decide
  have hdescent : baseEnd_2054112 < baseStart_2054112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054148 : List Nat := [2, 3, 2, 4, 1, 1, 1, 3, 5]
def baseStart_2054148 : Nat := 118140960795 + 2054148 * 2 ^ 59
def prefixEnd_2054148 : Nat := 4983230072969 + 3 ^ 40 * 2054148 * 2
def baseEnd_2054148 : Nat := 234392279882652082267367

theorem tailTrace_2054148 : CollatzResearch.WordTrace tailWord_2054148 prefixEnd_2054148 234392279882652082267367 := by
  unfold tailWord_2054148
  simp only [CollatzResearch.WordTrace]
  refine ⟨37460466281090045696629549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49947288374786727595506065 37460466281090045696629549)
  ·
    refine ⟨14047674855408767136236081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37460466281090045696629549 14047674855408767136236081)
    ·
      refine ⟨10535756141556575352177061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14047674855408767136236081 10535756141556575352177061)
      ·
        refine ⟨1975454276541857878533199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10535756141556575352177061 1975454276541857878533199)
        ·
          refine ⟨2963181414812786817799799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975454276541857878533199 2963181414812786817799799)
          ·
            refine ⟨4444772122219180226699699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963181414812786817799799 4444772122219180226699699)
            ·
              refine ⟨6667158183328770340049549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4444772122219180226699699 6667158183328770340049549)
              ·
                refine ⟨2500184318748288877518581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6667158183328770340049549 2500184318748288877518581)
                ·
                  refine ⟨234392279882652082267367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2500184318748288877518581 234392279882652082267367)
                  ·
                    rfl

theorem cell22_2054148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_2054148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054148 prefixEnd_2054148 := by exact prefixLift 2054148
  have htrace : WordTrace (prefixWord ++ tailWord_2054148) baseStart_2054148 baseEnd_2054148 := by
    simpa [prefixWord, tailWord_2054148, baseEnd_2054148] using wordTrace_append hprefix tailTrace_2054148
  have hstable : (prefixWord ++ tailWord_2054148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054148).length < 2 ^ (prefixWord ++ tailWord_2054148).sum := by decide
  have hdescent : baseEnd_2054148 < baseStart_2054148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054178 : List Nat := [3, 3, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_2054178 : Nat := 118140960795 + 2054178 * 2 ^ 59
def prefixEnd_2054178 : Nat := 4983230072969 + 3 ^ 40 * 2054178 * 2
def baseEnd_2054178 : Nat := 703187109261046168552009

theorem tailTrace_2054178 : CollatzResearch.WordTrace tailWord_2054178 prefixEnd_2054178 703187109261046168552009 := by
  unfold tailWord_2054178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18730506688017851629212797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49948017834714271011234125 18730506688017851629212797)
  ·
    refine ⟨7023940008006694360954799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18730506688017851629212797 7023940008006694360954799)
    ·
      refine ⟨10535910012010041541432199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7023940008006694360954799 10535910012010041541432199)
      ·
        refine ⟨15803865018015062312148299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10535910012010041541432199 15803865018015062312148299)
        ·
          refine ⟨23705797527022593468222449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15803865018015062312148299 23705797527022593468222449)
          ·
            refine ⟨17779348145266945101166837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23705797527022593468222449 17779348145266945101166837)
            ·
              refine ⟨1666813888618776103234391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17779348145266945101166837 1666813888618776103234391)
              ·
                refine ⟨2500220832928164154851587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666813888618776103234391 2500220832928164154851587)
                ·
                  refine ⟨3750331249392246232277381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500220832928164154851587 3750331249392246232277381)
                  ·
                    refine ⟨703187109261046168552009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3750331249392246232277381 703187109261046168552009)
                    ·
                      rfl

theorem cell22_2054178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_2054178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054178 prefixEnd_2054178 := by exact prefixLift 2054178
  have htrace : WordTrace (prefixWord ++ tailWord_2054178) baseStart_2054178 baseEnd_2054178 := by
    simpa [prefixWord, tailWord_2054178, baseEnd_2054178] using wordTrace_append hprefix tailTrace_2054178
  have hstable : (prefixWord ++ tailWord_2054178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054178).length < 2 ^ (prefixWord ++ tailWord_2054178).sum := by decide
  have hdescent : baseEnd_2054178 < baseStart_2054178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054193 : List Nat := [1, 2, 2, 3, 1, 3, 4, 2, 4]
def baseStart_2054193 : Nat := 118140960795 + 2054193 * 2 ^ 59
def prefixEnd_2054193 : Nat := 4983230072969 + 3 ^ 40 * 2054193 * 2
def baseEnd_2054193 : Nat := 234397414689197043142321

theorem tailTrace_2054193 : CollatzResearch.WordTrace tailWord_2054193 prefixEnd_2054193 234397414689197043142321 := by
  unfold tailWord_2054193
  simp only [CollatzResearch.WordTrace]
  refine ⟨74922573847017064078647233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49948382564678042719098155 74922573847017064078647233)
  ·
    refine ⟨56191930385262798058985425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74922573847017064078647233 56191930385262798058985425)
    ·
      refine ⟨42143947788947098544239069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56191930385262798058985425 42143947788947098544239069)
      ·
        refine ⟨15803980420855161954089651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42143947788947098544239069 15803980420855161954089651)
        ·
          refine ⟨23705970631282742931134477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15803980420855161954089651 23705970631282742931134477)
          ·
            refine ⟨8889738986731028599175429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23705970631282742931134477 8889738986731028599175429)
            ·
              refine ⟨1666826060012067862345393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8889738986731028599175429 1666826060012067862345393)
              ·
                refine ⟨1250119545009050896759045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1666826060012067862345393 1250119545009050896759045)
                ·
                  refine ⟨234397414689197043142321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1250119545009050896759045 234397414689197043142321)
                  ·
                    rfl

theorem cell22_2054193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 4].length) (baseStart_2054193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054193 prefixEnd_2054193 := by exact prefixLift 2054193
  have htrace : WordTrace (prefixWord ++ tailWord_2054193) baseStart_2054193 baseEnd_2054193 := by
    simpa [prefixWord, tailWord_2054193, baseEnd_2054193] using wordTrace_append hprefix tailTrace_2054193
  have hstable : (prefixWord ++ tailWord_2054193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054193).length < 2 ^ (prefixWord ++ tailWord_2054193).sum := by decide
  have hdescent : baseEnd_2054193 < baseStart_2054193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054242 : List Nat := [3, 3, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2054242 : Nat := 118140960795 + 2054242 * 2 ^ 59
def prefixEnd_2054242 : Nat := 4983230072969 + 3 ^ 40 * 2054242 * 2
def baseEnd_2054242 : Nat := 703209017768971334951813

theorem tailTrace_2054242 : CollatzResearch.WordTrace tailWord_2054242 prefixEnd_2054242 703209017768971334951813 := by
  unfold tailWord_2054242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18731090255959886361795245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49949574015893030298120653 18731090255959886361795245)
  ·
    refine ⟨7024158845984957385673217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18731090255959886361795245 7024158845984957385673217)
    ·
      refine ⟨5268119134488718039254913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7024158845984957385673217 5268119134488718039254913)
      ·
        refine ⟨3951089350866538529441185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5268119134488718039254913 3951089350866538529441185)
        ·
          refine ⟨2963317013149903897080889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3951089350866538529441185 2963317013149903897080889)
          ·
            refine ⟨2222487759862427922810667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2963317013149903897080889 2222487759862427922810667)
            ·
              refine ⟨3333731639793641884216001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222487759862427922810667 3333731639793641884216001)
              ·
                refine ⟨2500298729845231413162001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3333731639793641884216001 2500298729845231413162001)
                ·
                  refine ⟨1875224047383923559871501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2500298729845231413162001 1875224047383923559871501)
                  ·
                    refine ⟨703209017768971334951813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1875224047383923559871501 703209017768971334951813)
                    ·
                      rfl

theorem cell22_2054242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2054242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054242 prefixEnd_2054242 := by exact prefixLift 2054242
  have htrace : WordTrace (prefixWord ++ tailWord_2054242) baseStart_2054242 baseEnd_2054242 := by
    simpa [prefixWord, tailWord_2054242, baseEnd_2054242] using wordTrace_append hprefix tailTrace_2054242
  have hstable : (prefixWord ++ tailWord_2054242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054242).length < 2 ^ (prefixWord ++ tailWord_2054242).sum := by decide
  have hdescent : baseEnd_2054242 < baseStart_2054242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054249 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 7]
def baseStart_2054249 : Nat := 118140960795 + 2054249 * 2 ^ 59
def prefixEnd_2054249 : Nat := 4983230072969 + 3 ^ 40 * 2054249 * 2
def baseEnd_2054249 : Nat := 234403804670675216675597

theorem tailTrace_2054249 : CollatzResearch.WordTrace tailWord_2054249 prefixEnd_2054249 234403804670675216675597 := by
  unfold tailWord_2054249
  simp only [CollatzResearch.WordTrace]
  refine ⟨74924616334814185642685801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49949744223209457095123867 74924616334814185642685801)
  ·
    refine ⟨56193462251110639232014351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74924616334814185642685801 56193462251110639232014351)
    ·
      refine ⟨84290193376665958848021527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56193462251110639232014351 84290193376665958848021527)
      ·
        refine ⟨126435290064998938272032291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84290193376665958848021527 126435290064998938272032291)
        ·
          refine ⟨189652935097498407408048437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126435290064998938272032291 189652935097498407408048437)
          ·
            refine ⟨17779962665390475694504541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189652935097498407408048437 17779962665390475694504541)
            ·
              refine ⟨6667485999521428385439203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17779962665390475694504541 6667485999521428385439203)
              ·
                refine ⟨10001228999282142578158805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6667485999521428385439203 10001228999282142578158805)
                ·
                  refine ⟨234403804670675216675597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10001228999282142578158805 234403804670675216675597)
                  ·
                    rfl

theorem cell22_2054249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_2054249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054249 prefixEnd_2054249 := by exact prefixLift 2054249
  have htrace : WordTrace (prefixWord ++ tailWord_2054249) baseStart_2054249 baseEnd_2054249 := by
    simpa [prefixWord, tailWord_2054249, baseEnd_2054249] using wordTrace_append hprefix tailTrace_2054249
  have hstable : (prefixWord ++ tailWord_2054249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054249).length < 2 ^ (prefixWord ++ tailWord_2054249).sum := by decide
  have hdescent : baseEnd_2054249 < baseStart_2054249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054253 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_2054253 : Nat := 118140960795 + 2054253 * 2 ^ 59
def prefixEnd_2054253 : Nat := 4983230072969 + 3 ^ 40 * 2054253 * 2
def baseEnd_2054253 : Nat := 703212783293770972926779

theorem tailTrace_2054253 : CollatzResearch.WordTrace tailWord_2054253 prefixEnd_2054253 703212783293770972926779 := by
  unfold tailWord_2054253
  simp only [CollatzResearch.WordTrace]
  refine ⟨74924762226799694325831413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49949841484533129550554275 74924762226799694325831413)
  ·
    refine ⟨7024196458762471343046695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74924762226799694325831413 7024196458762471343046695)
    ·
      refine ⟨10536294688143707014570043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7024196458762471343046695 10536294688143707014570043)
      ·
        refine ⟨15804442032215560521855065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10536294688143707014570043 15804442032215560521855065)
        ·
          refine ⟨11853331524161670391391299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15804442032215560521855065 11853331524161670391391299)
          ·
            refine ⟨17779997286242505587086949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11853331524161670391391299 17779997286242505587086949)
            ·
              refine ⟨3333749491170469797578803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17779997286242505587086949 3333749491170469797578803)
              ·
                refine ⟨5000624236755704696368205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333749491170469797578803 5000624236755704696368205)
                ·
                  refine ⟨1875234088783389261138077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5000624236755704696368205 1875234088783389261138077)
                  ·
                    refine ⟨703212783293770972926779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1875234088783389261138077 703212783293770972926779)
                    ·
                      rfl

theorem cell22_2054253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_2054253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054253 prefixEnd_2054253 := by exact prefixLift 2054253
  have htrace : WordTrace (prefixWord ++ tailWord_2054253) baseStart_2054253 baseEnd_2054253 := by
    simpa [prefixWord, tailWord_2054253, baseEnd_2054253] using wordTrace_append hprefix tailTrace_2054253
  have hstable : (prefixWord ++ tailWord_2054253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054253).length < 2 ^ (prefixWord ++ tailWord_2054253).sum := by decide
  have hdescent : baseEnd_2054253 < baseStart_2054253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054341 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_2054341 : Nat := 118140960795 + 2054341 * 2 ^ 59
def prefixEnd_2054341 : Nat := 4983230072969 + 3 ^ 40 * 2054341 * 2
def baseEnd_2054341 : Nat := 703242907492168076726509

theorem tailTrace_2054341 : CollatzResearch.WordTrace tailWord_2054341 prefixEnd_2054341 703242907492168076726509 := by
  unfold tailWord_2054341
  simp only [CollatzResearch.WordTrace]
  refine ⟨74927971850480885355034877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49951981233653923570023251 74927971850480885355034877)
  ·
    refine ⟨28097989443930332008138079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74927971850480885355034877 28097989443930332008138079)
    ·
      refine ⟨42146984165895498012207119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28097989443930332008138079 42146984165895498012207119)
      ·
        refine ⟨63220476248843247018310679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42146984165895498012207119 63220476248843247018310679)
        ·
          refine ⟨94830714373264870527466019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63220476248843247018310679 94830714373264870527466019)
          ·
            refine ⟨142246071559897305791199029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94830714373264870527466019 142246071559897305791199029)
            ·
              refine ⟨13335569208740372417924909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142246071559897305791199029 13335569208740372417924909)
              ·
                refine ⟨5000838453277639656721841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13335569208740372417924909 5000838453277639656721841)
                ·
                  refine ⟨3750628839958229742541381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5000838453277639656721841 3750628839958229742541381)
                  ·
                    refine ⟨703242907492168076726509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3750628839958229742541381 703242907492168076726509)
                    ·
                      rfl

theorem cell22_2054341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_2054341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054341 prefixEnd_2054341 := by exact prefixLift 2054341
  have htrace : WordTrace (prefixWord ++ tailWord_2054341) baseStart_2054341 baseEnd_2054341 := by
    simpa [prefixWord, tailWord_2054341, baseEnd_2054341] using wordTrace_append hprefix tailTrace_2054341
  have hstable : (prefixWord ++ tailWord_2054341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054341).length < 2 ^ (prefixWord ++ tailWord_2054341).sum := by decide
  have hdescent : baseEnd_2054341 < baseStart_2054341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054360 : List Nat := [2, 1, 2, 2, 4, 2, 2, 2, 2, 3]
def baseStart_2054360 : Nat := 118140960795 + 2054360 * 2 ^ 59
def prefixEnd_2054360 : Nat := 4983230072969 + 3 ^ 40 * 2054360 * 2
def baseEnd_2054360 : Nat := 703249411580458360501451

theorem tailTrace_2054360 : CollatzResearch.WordTrace tailWord_2054360 prefixEnd_2054360 703249411580458360501451 := by
  unfold tailWord_2054360
  simp only [CollatzResearch.WordTrace]
  refine ⟨37464332418706025799988267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49952443224941367733317689 37464332418706025799988267)
  ·
    refine ⟨56196498628059038699982401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37464332418706025799988267 56196498628059038699982401)
    ·
      refine ⟨42147373971044279024986801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56196498628059038699982401 42147373971044279024986801)
      ·
        refine ⟨31610530478283209268740101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42147373971044279024986801 31610530478283209268740101)
        ·
          refine ⟨5926974464678101737888769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31610530478283209268740101 5926974464678101737888769)
          ·
            refine ⟨4445230848508576303416577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5926974464678101737888769 4445230848508576303416577)
            ·
              refine ⟨3333923136381432227562433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4445230848508576303416577 3333923136381432227562433)
              ·
                refine ⟨2500442352286074170671825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3333923136381432227562433 2500442352286074170671825)
                ·
                  refine ⟨1875331764214555628003869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2500442352286074170671825 1875331764214555628003869)
                  ·
                    refine ⟨703249411580458360501451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1875331764214555628003869 703249411580458360501451)
                    ·
                      rfl

theorem cell22_2054360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_2054360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054360 prefixEnd_2054360 := by exact prefixLift 2054360
  have htrace : WordTrace (prefixWord ++ tailWord_2054360) baseStart_2054360 baseEnd_2054360 := by
    simpa [prefixWord, tailWord_2054360, baseEnd_2054360] using wordTrace_append hprefix tailTrace_2054360
  have hstable : (prefixWord ++ tailWord_2054360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054360).length < 2 ^ (prefixWord ++ tailWord_2054360).sum := by decide
  have hdescent : baseEnd_2054360 < baseStart_2054360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054373 : List Nat := [1, 3, 1, 4, 2, 3, 1, 7]
def baseStart_2054373 : Nat := 118140960795 + 2054373 * 2 ^ 59
def prefixEnd_2054373 : Nat := 4983230072969 + 3 ^ 40 * 2054373 * 2
def baseEnd_2054373 : Nat := 78139317971792295547379

theorem tailTrace_2054373 : CollatzResearch.WordTrace tailWord_2054373 prefixEnd_2054373 78139317971792295547379 := by
  unfold tailWord_2054373
  simp only [CollatzResearch.WordTrace]
  refine ⟨74929138986364954820199773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49952759324243303213466515 74929138986364954820199773)
  ·
    refine ⟨28098427119886858057574915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74929138986364954820199773 28098427119886858057574915)
    ·
      refine ⟨42147640679830287086362373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28098427119886858057574915 42147640679830287086362373)
      ·
        refine ⟨7902682627468178828692945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42147640679830287086362373 7902682627468178828692945)
        ·
          refine ⟨5927011970601134121519709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7902682627468178828692945 5927011970601134121519709)
          ·
            refine ⟨2222629488975425295569891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5927011970601134121519709 2222629488975425295569891)
            ·
              refine ⟨3333944233463137943354837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222629488975425295569891 3333944233463137943354837)
              ·
                refine ⟨78139317971792295547379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3333944233463137943354837 78139317971792295547379)
                ·
                  rfl

theorem cell22_2054373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 7].length) (baseStart_2054373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054373 prefixEnd_2054373 := by exact prefixLift 2054373
  have htrace : WordTrace (prefixWord ++ tailWord_2054373) baseStart_2054373 baseEnd_2054373 := by
    simpa [prefixWord, tailWord_2054373, baseEnd_2054373] using wordTrace_append hprefix tailTrace_2054373
  have hstable : (prefixWord ++ tailWord_2054373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054373).length < 2 ^ (prefixWord ++ tailWord_2054373).sum := by decide
  have hdescent : baseEnd_2054373 < baseStart_2054373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054401 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 7]
def baseStart_2054401 : Nat := 118140960795 + 2054401 * 2 ^ 59
def prefixEnd_2054401 : Nat := 4983230072969 + 3 ^ 40 * 2054401 * 2
def baseEnd_2054401 : Nat := 234421148906115973408775

theorem tailTrace_2054401 : CollatzResearch.WordTrace tailWord_2054401 prefixEnd_2054401 234421148906115973408775 := by
  unfold tailWord_2054401
  simp only [CollatzResearch.WordTrace]
  refine ⟨74930160230263515602219057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49953440153509010401479371 74930160230263515602219057)
  ·
    refine ⟨56197620172697636701664293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74930160230263515602219057 56197620172697636701664293)
    ·
      refine ⟨10537053782380806881562055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56197620172697636701664293 10537053782380806881562055)
      ·
        refine ⟨15805580673571210322343083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10537053782380806881562055 15805580673571210322343083)
        ·
          refine ⟨23708371010356815483514625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15805580673571210322343083 23708371010356815483514625)
          ·
            refine ⟨17781278257767611612635969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23708371010356815483514625 17781278257767611612635969)
            ·
              refine ⟨13335958693325708709476977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17781278257767611612635969 13335958693325708709476977)
              ·
                refine ⟨10001969019994281532107733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13335958693325708709476977 10001969019994281532107733)
                ·
                  refine ⟨234421148906115973408775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10001969019994281532107733 234421148906115973408775)
                  ·
                    rfl

theorem cell22_2054401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_2054401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054401 prefixEnd_2054401 := by exact prefixLift 2054401
  have htrace : WordTrace (prefixWord ++ tailWord_2054401) baseStart_2054401 baseEnd_2054401 := by
    simpa [prefixWord, tailWord_2054401, baseEnd_2054401] using wordTrace_append hprefix tailTrace_2054401
  have hstable : (prefixWord ++ tailWord_2054401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054401).length < 2 ^ (prefixWord ++ tailWord_2054401).sum := by decide
  have hdescent : baseEnd_2054401 < baseStart_2054401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054553 : List Nat := [1, 2, 1, 2, 1, 4, 1, 5, 5]
def baseStart_2054553 : Nat := 118140960795 + 2054553 * 2 ^ 59
def prefixEnd_2054553 : Nat := 4983230072969 + 3 ^ 40 * 2054553 * 2
def baseEnd_2054553 : Nat := 234438493141556730141953

theorem tailTrace_2054553 : CollatzResearch.WordTrace tailWord_2054553 prefixEnd_2054553 234438493141556730141953 := by
  unfold tailWord_2054553
  simp only [CollatzResearch.WordTrace]
  refine ⟨74935704125712845561752313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49957136083808563707834875 74935704125712845561752313)
  ·
    refine ⟨56201778094284634171314235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74935704125712845561752313 56201778094284634171314235)
    ·
      refine ⟨84302667141426951256971353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56201778094284634171314235 84302667141426951256971353)
      ·
        refine ⟨63227000356070213442728515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84302667141426951256971353 63227000356070213442728515)
        ·
          refine ⟨94840500534105320164092773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63227000356070213442728515 94840500534105320164092773)
          ·
            refine ⟨17782593850144747530767395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94840500534105320164092773 17782593850144747530767395)
            ·
              refine ⟨26673890775217121296151093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17782593850144747530767395 26673890775217121296151093)
              ·
                refine ⟨2500677260176605121514165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26673890775217121296151093 2500677260176605121514165)
                ·
                  refine ⟨234438493141556730141953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2500677260176605121514165 234438493141556730141953)
                  ·
                    rfl

theorem cell22_2054553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 5].length) (baseStart_2054553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054553 prefixEnd_2054553 := by exact prefixLift 2054553
  have htrace : WordTrace (prefixWord ++ tailWord_2054553) baseStart_2054553 baseEnd_2054553 := by
    simpa [prefixWord, tailWord_2054553, baseEnd_2054553] using wordTrace_append hprefix tailTrace_2054553
  have hstable : (prefixWord ++ tailWord_2054553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054553).length < 2 ^ (prefixWord ++ tailWord_2054553).sum := by decide
  have hdescent : baseEnd_2054553 < baseStart_2054553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054557 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_2054557 : Nat := 118140960795 + 2054557 * 2 ^ 59
def prefixEnd_2054557 : Nat := 4983230072969 + 3 ^ 40 * 2054557 * 2
def baseEnd_2054557 : Nat := 703316848706415513325847

theorem tailTrace_2054557 : CollatzResearch.WordTrace tailWord_2054557 prefixEnd_2054557 703316848706415513325847 := by
  unfold tailWord_2054557
  simp only [CollatzResearch.WordTrace]
  refine ⟨74935850017698354244897925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49957233345132236163265283 74935850017698354244897925)
  ·
    refine ⟨14050471878318441420918361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74935850017698354244897925 14050471878318441420918361)
    ·
      refine ⟨10537853908738831065688771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14050471878318441420918361 10537853908738831065688771)
      ·
        refine ⟨15806780863108246598533157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10537853908738831065688771 15806780863108246598533157)
        ·
          refine ⟨2963771411832796237224967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15806780863108246598533157 2963771411832796237224967)
          ·
            refine ⟨4445657117749194355837451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963771411832796237224967 4445657117749194355837451)
            ·
              refine ⟨6668485676623791533756177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4445657117749194355837451 6668485676623791533756177)
              ·
                refine ⟨5001364257467843650317133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6668485676623791533756177 5001364257467843650317133)
                ·
                  refine ⟨1875511596550441368868925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5001364257467843650317133 1875511596550441368868925)
                  ·
                    refine ⟨703316848706415513325847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1875511596550441368868925 703316848706415513325847)
                    ·
                      rfl

theorem cell22_2054557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_2054557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054557 prefixEnd_2054557 := by exact prefixLift 2054557
  have htrace : WordTrace (prefixWord ++ tailWord_2054557) baseStart_2054557 baseEnd_2054557 := by
    simpa [prefixWord, tailWord_2054557, baseEnd_2054557] using wordTrace_append hprefix tailTrace_2054557
  have hstable : (prefixWord ++ tailWord_2054557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054557).length < 2 ^ (prefixWord ++ tailWord_2054557).sum := by decide
  have hdescent : baseEnd_2054557 < baseStart_2054557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054632 : List Nat := [2, 1, 4, 1, 1, 3, 3, 3, 4]
def baseStart_2054632 : Nat := 118140960795 + 2054632 * 2 ^ 59
def prefixEnd_2054632 : Nat := 4983230072969 + 3 ^ 40 * 2054632 * 2
def baseEnd_2054632 : Nat := 234447507579713439233539

theorem tailTrace_2054632 : CollatzResearch.WordTrace tailWord_2054632 prefixEnd_2054632 234447507579713439233539 := by
  unfold tailWord_2054632
  simp only [CollatzResearch.WordTrace]
  refine ⟨37469292746213321026939075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49959056994951094702585433 37469292746213321026939075)
  ·
    refine ⟨56203939119319981540408613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37469292746213321026939075 56203939119319981540408613)
    ·
      refine ⟨10538238584872496538826615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56203939119319981540408613 10538238584872496538826615)
      ·
        refine ⟨15807357877308744808239923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10538238584872496538826615 15807357877308744808239923)
        ·
          refine ⟨23711036815963117212359885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15807357877308744808239923 23711036815963117212359885)
          ·
            refine ⟨8891638805986168954634957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23711036815963117212359885 8891638805986168954634957)
            ·
              refine ⟨3334364552244813357988109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8891638805986168954634957 3334364552244813357988109)
              ·
                refine ⟨1250386707091805009245541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3334364552244813357988109 1250386707091805009245541)
                ·
                  refine ⟨234447507579713439233539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1250386707091805009245541 234447507579713439233539)
                  ·
                    rfl

theorem cell22_2054632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 4].length) (baseStart_2054632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054632 prefixEnd_2054632 := by exact prefixLift 2054632
  have htrace : WordTrace (prefixWord ++ tailWord_2054632) baseStart_2054632 baseEnd_2054632 := by
    simpa [prefixWord, tailWord_2054632, baseEnd_2054632] using wordTrace_append hprefix tailTrace_2054632
  have hstable : (prefixWord ++ tailWord_2054632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054632).length < 2 ^ (prefixWord ++ tailWord_2054632).sum := by decide
  have hdescent : baseEnd_2054632 < baseStart_2054632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054660 : List Nat := [2, 3, 2, 3, 1, 1, 1, 9]
def baseStart_2054660 : Nat := 118140960795 + 2054660 * 2 ^ 59
def prefixEnd_2054660 : Nat := 4983230072969 + 3 ^ 40 * 2054660 * 2
def baseEnd_2054660 : Nat := 78150234190150842000059

theorem tailTrace_2054660 : CollatzResearch.WordTrace tailWord_2054660 prefixEnd_2054660 78150234190150842000059 := by
  unfold tailWord_2054660
  simp only [CollatzResearch.WordTrace]
  refine ⟨37469803368162601417948717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49959737824216801890598289 37469803368162601417948717)
  ·
    refine ⟨14051176263060975531730769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37469803368162601417948717 14051176263060975531730769)
    ·
      refine ⟨10538382197295731648798077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14051176263060975531730769 10538382197295731648798077)
      ·
        refine ⟨3951893323985899368299279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10538382197295731648798077 3951893323985899368299279)
        ·
          refine ⟨5927839985978849052448919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3951893323985899368299279 5927839985978849052448919)
          ·
            refine ⟨8891759978968273578673379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5927839985978849052448919 8891759978968273578673379)
            ·
              refine ⟨13337639968452410368010069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8891759978968273578673379 13337639968452410368010069)
              ·
                refine ⟨78150234190150842000059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13337639968452410368010069 78150234190150842000059)
                ·
                  rfl

theorem cell22_2054660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 9].length) (baseStart_2054660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054660 prefixEnd_2054660 := by exact prefixLift 2054660
  have htrace : WordTrace (prefixWord ++ tailWord_2054660) baseStart_2054660 baseEnd_2054660 := by
    simpa [prefixWord, tailWord_2054660, baseEnd_2054660] using wordTrace_append hprefix tailTrace_2054660
  have hstable : (prefixWord ++ tailWord_2054660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054660).length < 2 ^ (prefixWord ++ tailWord_2054660).sum := by decide
  have hdescent : baseEnd_2054660 < baseStart_2054660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054673 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 4, 6]
def baseStart_2054673 : Nat := 118140960795 + 2054673 * 2 ^ 59
def prefixEnd_2054673 : Nat := 4983230072969 + 3 ^ 40 * 2054673 * 2
def baseEnd_2054673 : Nat := 703356557877029877425491

theorem tailTrace_2054673 : CollatzResearch.WordTrace tailWord_2054673 prefixEnd_2054673 703356557877029877425491 := by
  unfold tailWord_2054673
  simp only [CollatzResearch.WordTrace]
  refine ⟨74940080885278106056120673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49960053923518737370747115 74940080885278106056120673)
  ·
    refine ⟨56205060663958579542090505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74940080885278106056120673 56205060663958579542090505)
    ·
      refine ⟨42153795497968934656567879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56205060663958579542090505 42153795497968934656567879)
      ·
        refine ⟨63230693246953401984851819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42153795497968934656567879 63230693246953401984851819)
        ·
          refine ⟨94846039870430102977277729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63230693246953401984851819 94846039870430102977277729)
          ·
            refine ⟨71134529902822577232958297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94846039870430102977277729 71134529902822577232958297)
            ·
              refine ⟨53350897427116932924718723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71134529902822577232958297 53350897427116932924718723)
              ·
                refine ⟨80026346140675399387078085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53350897427116932924718723 80026346140675399387078085)
                ·
                  refine ⟨15004939901376637385077141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80026346140675399387078085 15004939901376637385077141)
                  ·
                    refine ⟨703356557877029877425491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15004939901376637385077141 703356557877029877425491)
                    ·
                      rfl

theorem cell22_2054673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_2054673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054673 prefixEnd_2054673 := by exact prefixLift 2054673
  have htrace : WordTrace (prefixWord ++ tailWord_2054673) baseStart_2054673 baseEnd_2054673 := by
    simpa [prefixWord, tailWord_2054673, baseEnd_2054673] using wordTrace_append hprefix tailTrace_2054673
  have hstable : (prefixWord ++ tailWord_2054673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054673).length < 2 ^ (prefixWord ++ tailWord_2054673).sum := by decide
  have hdescent : baseEnd_2054673 < baseStart_2054673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054675 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 5, 3]
def baseStart_2054675 : Nat := 118140960795 + 2054675 * 2 ^ 59
def prefixEnd_2054675 : Nat := 4983230072969 + 3 ^ 40 * 2054675 * 2
def baseEnd_2054675 : Nat := 703357242517902538875485

theorem tailTrace_2054675 : CollatzResearch.WordTrace tailWord_2054675 prefixEnd_2054675 703357242517902538875485 := by
  unfold tailWord_2054675
  simp only [CollatzResearch.WordTrace]
  refine ⟨74940153831270860397693479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49960102554180573598462319 74940153831270860397693479)
  ·
    refine ⟨112410230746906290596540219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74940153831270860397693479 112410230746906290596540219)
    ·
      refine ⟨168615346120359435894810329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112410230746906290596540219 168615346120359435894810329)
      ·
        refine ⟨126461509590269576921107747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168615346120359435894810329 126461509590269576921107747)
        ·
          refine ⟨189692264385404365381661621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126461509590269576921107747 189692264385404365381661621)
          ·
            refine ⟨17783649786131659254530777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189692264385404365381661621 17783649786131659254530777)
            ·
              refine ⟨13337737339598744440898083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17783649786131659254530777 13337737339598744440898083)
              ·
                refine ⟨20006606009398116661347125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13337737339598744440898083 20006606009398116661347125)
                ·
                  refine ⟨1875619313381073437001293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20006606009398116661347125 1875619313381073437001293)
                  ·
                    refine ⟨703357242517902538875485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1875619313381073437001293 703357242517902538875485)
                    ·
                      rfl

theorem cell22_2054675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 3].length) (baseStart_2054675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054675 prefixEnd_2054675 := by exact prefixLift 2054675
  have htrace : WordTrace (prefixWord ++ tailWord_2054675) baseStart_2054675 baseEnd_2054675 := by
    simpa [prefixWord, tailWord_2054675, baseEnd_2054675] using wordTrace_append hprefix tailTrace_2054675
  have hstable : (prefixWord ++ tailWord_2054675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054675).length < 2 ^ (prefixWord ++ tailWord_2054675).sum := by decide
  have hdescent : baseEnd_2054675 < baseStart_2054675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054679 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 2, 4]
def baseStart_2054679 : Nat := 118140960795 + 2054679 * 2 ^ 59
def prefixEnd_2054679 : Nat := 4983230072969 + 3 ^ 40 * 2054679 * 2
def baseEnd_2054679 : Nat := 703358611799647861775473

theorem tailTrace_2054679 : CollatzResearch.WordTrace tailWord_2054679 prefixEnd_2054679 703358611799647861775473 := by
  unfold tailWord_2054679
  simp only [CollatzResearch.WordTrace]
  refine ⟨74940299723256369080839091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49960199815504246053892727 74940299723256369080839091)
  ·
    refine ⟨112410449584884553621258637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74940299723256369080839091 112410449584884553621258637)
    ·
      refine ⟨42153918594331707607971989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112410449584884553621258637 42153918594331707607971989)
      ·
        refine ⟨1975964934109298794123687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42153918594331707607971989 1975964934109298794123687)
        ·
          refine ⟨2963947401163948191185531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975964934109298794123687 2963947401163948191185531)
          ·
            refine ⟨4445921101745922286778297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963947401163948191185531 4445921101745922286778297)
            ·
              refine ⟨3334440826309441715083723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4445921101745922286778297 3334440826309441715083723)
              ·
                refine ⟨5001661239464162572625585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3334440826309441715083723 5001661239464162572625585)
                ·
                  refine ⟨3751245929598121929469189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5001661239464162572625585 3751245929598121929469189)
                  ·
                    refine ⟨703358611799647861775473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3751245929598121929469189 703358611799647861775473)
                    ·
                      rfl

theorem cell22_2054679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_2054679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054679 prefixEnd_2054679 := by exact prefixLift 2054679
  have htrace : WordTrace (prefixWord ++ tailWord_2054679) baseStart_2054679 baseEnd_2054679 := by
    simpa [prefixWord, tailWord_2054679, baseEnd_2054679] using wordTrace_append hprefix tailTrace_2054679
  have hstable : (prefixWord ++ tailWord_2054679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054679).length < 2 ^ (prefixWord ++ tailWord_2054679).sum := by decide
  have hdescent : baseEnd_2054679 < baseStart_2054679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054703 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 5, 7]
def baseStart_2054703 : Nat := 118140960795 + 2054703 * 2 ^ 59
def prefixEnd_2054703 : Nat := 4983230072969 + 3 ^ 40 * 2054703 * 2
def baseEnd_2054703 : Nat := 703366827490119799175399

theorem tailTrace_2054703 : CollatzResearch.WordTrace tailWord_2054703 prefixEnd_2054703 703366827490119799175399 := by
  unfold tailWord_2054703
  simp only [CollatzResearch.WordTrace]
  refine ⟨74941175075169421179712763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49960783383446280786475175 74941175075169421179712763)
  ·
    refine ⟨112411762612754131769569145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74941175075169421179712763 112411762612754131769569145)
    ·
      refine ⟨84308821959565598827176859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112411762612754131769569145 84308821959565598827176859)
      ·
        refine ⟨126463232939348398240765289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84308821959565598827176859 126463232939348398240765289)
        ·
          refine ⟨94847424704511298680573967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126463232939348398240765289 94847424704511298680573967)
          ·
            refine ⟨142271137056766948020860951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94847424704511298680573967 142271137056766948020860951)
            ·
              refine ⟨213406705585150422031291427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142271137056766948020860951 213406705585150422031291427)
              ·
                refine ⟨320110058377725633046937141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213406705585150422031291427 320110058377725633046937141)
                ·
                  refine ⟨30010317972911778098150357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320110058377725633046937141 30010317972911778098150357)
                  ·
                    refine ⟨703366827490119799175399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30010317972911778098150357 703366827490119799175399)
                    ·
                      rfl

theorem cell22_2054703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_2054703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054703 prefixEnd_2054703 := by exact prefixLift 2054703
  have htrace : WordTrace (prefixWord ++ tailWord_2054703) baseStart_2054703 baseEnd_2054703 := by
    simpa [prefixWord, tailWord_2054703, baseEnd_2054703] using wordTrace_append hprefix tailTrace_2054703
  have hstable : (prefixWord ++ tailWord_2054703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054703).length < 2 ^ (prefixWord ++ tailWord_2054703).sum := by decide
  have hdescent : baseEnd_2054703 < baseStart_2054703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054705 : List Nat := [1, 2, 2, 3, 1, 1, 3, 4, 5]
def baseStart_2054705 : Nat := 118140960795 + 2054705 * 2 ^ 59
def prefixEnd_2054705 : Nat := 4983230072969 + 3 ^ 40 * 2054705 * 2
def baseEnd_2054705 : Nat := 234455837376997486875131

theorem tailTrace_2054705 : CollatzResearch.WordTrace tailWord_2054705 prefixEnd_2054705 234455837376997486875131 := by
  unfold tailWord_2054705
  simp only [CollatzResearch.WordTrace]
  refine ⟨74941248021162175521285569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49960832014108117014190379 74941248021162175521285569)
  ·
    refine ⟨56205936015871631640964177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74941248021162175521285569 56205936015871631640964177)
    ·
      refine ⟨42154452011903723730723133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56205936015871631640964177 42154452011903723730723133)
      ·
        refine ⟨15807919504463896399021175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42154452011903723730723133 15807919504463896399021175)
        ·
          refine ⟨23711879256695844598531763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15807919504463896399021175 23711879256695844598531763)
          ·
            refine ⟨35567818885043766897797645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23711879256695844598531763 35567818885043766897797645)
            ·
              refine ⟨13337932081891412586674117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35567818885043766897797645 13337932081891412586674117)
              ·
                refine ⟨2500862265354639860001397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13337932081891412586674117 2500862265354639860001397)
                ·
                  refine ⟨234455837376997486875131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2500862265354639860001397 234455837376997486875131)
                  ·
                    rfl

theorem cell22_2054705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 5].length) (baseStart_2054705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054705 prefixEnd_2054705 := by exact prefixLift 2054705
  have htrace : WordTrace (prefixWord ++ tailWord_2054705) baseStart_2054705 baseEnd_2054705 := by
    simpa [prefixWord, tailWord_2054705, baseEnd_2054705] using wordTrace_append hprefix tailTrace_2054705
  have hstable : (prefixWord ++ tailWord_2054705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054705).length < 2 ^ (prefixWord ++ tailWord_2054705).sum := by decide
  have hdescent : baseEnd_2054705 < baseStart_2054705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054709 : List Nat := [1, 3, 3, 1, 1, 2, 3, 4, 1, 3]
def baseStart_2054709 : Nat := 118140960795 + 2054709 * 2 ^ 59
def prefixEnd_2054709 : Nat := 4983230072969 + 3 ^ 40 * 2054709 * 2
def baseEnd_2054709 : Nat := 703368881412737783525381

theorem tailTrace_2054709 : CollatzResearch.WordTrace tailWord_2054709 prefixEnd_2054709 703368881412737783525381 := by
  unfold tailWord_2054709
  simp only [CollatzResearch.WordTrace]
  refine ⟨74941393913147684204431181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49960929275431789469620787 74941393913147684204431181)
  ·
    refine ⟨28103022717430381576661693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74941393913147684204431181 28103022717430381576661693)
    ·
      refine ⟨10538633519036393091248135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28103022717430381576661693 10538633519036393091248135)
      ·
        refine ⟨15807950278554589636872203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10538633519036393091248135 15807950278554589636872203)
        ·
          refine ⟨23711925417831884455308305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15807950278554589636872203 23711925417831884455308305)
          ·
            refine ⟨17783944063373913341481229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23711925417831884455308305 17783944063373913341481229)
            ·
              refine ⟨6668979023765217503055461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17783944063373913341481229 6668979023765217503055461)
              ·
                refine ⟨1250433566955978281822899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6668979023765217503055461 1250433566955978281822899)
                ·
                  refine ⟨1875650350433967422734349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250433566955978281822899 1875650350433967422734349)
                  ·
                    refine ⟨703368881412737783525381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1875650350433967422734349 703368881412737783525381)
                    ·
                      rfl

theorem cell22_2054709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_2054709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054709 prefixEnd_2054709 := by exact prefixLift 2054709
  have htrace : WordTrace (prefixWord ++ tailWord_2054709) baseStart_2054709 baseEnd_2054709 := by
    simpa [prefixWord, tailWord_2054709, baseEnd_2054709] using wordTrace_append hprefix tailTrace_2054709
  have hstable : (prefixWord ++ tailWord_2054709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054709).length < 2 ^ (prefixWord ++ tailWord_2054709).sum := by decide
  have hdescent : baseEnd_2054709 < baseStart_2054709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054726 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_2054726 : Nat := 118140960795 + 2054726 * 2 ^ 59
def prefixEnd_2054726 : Nat := 4983230072969 + 3 ^ 40 * 2054726 * 2
def baseEnd_2054726 : Nat := 703374700860155405850329

theorem tailTrace_2054726 : CollatzResearch.WordTrace tailWord_2054726 prefixEnd_2054726 703374700860155405850329 := by
  unfold tailWord_2054726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2341937936065190503368751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49961342636057397405200021 2341937936065190503368751)
  ·
    refine ⟨3512906904097785755053127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2341937936065190503368751 3512906904097785755053127)
    ·
      refine ⟨5269360356146678632579691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3512906904097785755053127 5269360356146678632579691)
      ·
        refine ⟨7904040534220017948869537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5269360356146678632579691 7904040534220017948869537)
        ·
          refine ⟨5928030400665013461652153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7904040534220017948869537 5928030400665013461652153)
          ·
            refine ⟨4446022800498760096239115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5928030400665013461652153 4446022800498760096239115)
            ·
              refine ⟨6669034200748140144358673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4446022800498760096239115 6669034200748140144358673)
              ·
                refine ⟨5001775650561105108269005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6669034200748140144358673 5001775650561105108269005)
                ·
                  refine ⟨1875665868960414415600877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5001775650561105108269005 1875665868960414415600877)
                  ·
                    refine ⟨703374700860155405850329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1875665868960414415600877 703374700860155405850329)
                    ·
                      rfl

theorem cell22_2054726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_2054726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054726 prefixEnd_2054726 := by exact prefixLift 2054726
  have htrace : WordTrace (prefixWord ++ tailWord_2054726) baseStart_2054726 baseEnd_2054726 := by
    simpa [prefixWord, tailWord_2054726, baseEnd_2054726] using wordTrace_append hprefix tailTrace_2054726
  have hstable : (prefixWord ++ tailWord_2054726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054726).length < 2 ^ (prefixWord ++ tailWord_2054726).sum := by decide
  have hdescent : baseEnd_2054726 < baseStart_2054726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054735 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 3, 4]
def baseStart_2054735 : Nat := 118140960795 + 2054735 * 2 ^ 59
def prefixEnd_2054735 : Nat := 4983230072969 + 3 ^ 40 * 2054735 * 2
def baseEnd_2054735 : Nat := 703377781744082382375301

theorem tailTrace_2054735 : CollatzResearch.WordTrace tailWord_2054735 prefixEnd_2054735 703377781744082382375301 := by
  unfold tailWord_2054735
  simp only [CollatzResearch.WordTrace]
  refine ⟨74942342211053490644877659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49961561474035660429918439 74942342211053490644877659)
  ·
    refine ⟨112413513316580235967316489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74942342211053490644877659 112413513316580235967316489)
    ·
      refine ⟨84310134987435176975487367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112413513316580235967316489 84310134987435176975487367)
      ·
        refine ⟨126465202481152765463231051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84310134987435176975487367 126465202481152765463231051)
        ·
          refine ⟨189697803721729148194846577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126465202481152765463231051 189697803721729148194846577)
          ·
            refine ⟨142273352791296861146134933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189697803721729148194846577 142273352791296861146134933)
            ·
              refine ⟨6669063412092040366225075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142273352791296861146134933 6669063412092040366225075)
              ·
                refine ⟨10003595118138060549337613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669063412092040366225075 10003595118138060549337613)
                ·
                  refine ⟨3751348169301772706001605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10003595118138060549337613 3751348169301772706001605)
                  ·
                    refine ⟨703377781744082382375301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3751348169301772706001605 703377781744082382375301)
                    ·
                      rfl

theorem cell22_2054735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_2054735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054735 prefixEnd_2054735 := by exact prefixLift 2054735
  have htrace : WordTrace (prefixWord ++ tailWord_2054735) baseStart_2054735 baseEnd_2054735 := by
    simpa [prefixWord, tailWord_2054735, baseEnd_2054735] using wordTrace_append hprefix tailTrace_2054735
  have hstable : (prefixWord ++ tailWord_2054735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054735).length < 2 ^ (prefixWord ++ tailWord_2054735).sum := by decide
  have hdescent : baseEnd_2054735 < baseStart_2054735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054767 : List Nat := [1, 1, 2, 1, 3, 2, 4, 4, 4]
def baseStart_2054767 : Nat := 118140960795 + 2054767 * 2 ^ 59
def prefixEnd_2054767 : Nat := 4983230072969 + 3 ^ 40 * 2054767 * 2
def baseEnd_2054767 : Nat := 234462911999348321858401

theorem tailTrace_2054767 : CollatzResearch.WordTrace tailWord_2054767 prefixEnd_2054767 234462911999348321858401 := by
  unfold tailWord_2054767
  simp only [CollatzResearch.WordTrace]
  refine ⟨74943509346937560110042555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49962339564625040073361703 74943509346937560110042555)
  ·
    refine ⟨112415264020406340165063833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74943509346937560110042555 112415264020406340165063833)
    ·
      refine ⟨84311448015304755123797875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112415264020406340165063833 84311448015304755123797875)
      ·
        refine ⟨126467172022957132685696813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84311448015304755123797875 126467172022957132685696813)
        ·
          refine ⟨47425189508608924757136305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126467172022957132685696813 47425189508608924757136305)
          ·
            refine ⟨35568892131456693567852229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47425189508608924757136305 35568892131456693567852229)
            ·
              refine ⟨6669167274648130043972293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35568892131456693567852229 6669167274648130043972293)
              ·
                refine ⟨1250468863996524383244805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6669167274648130043972293 1250468863996524383244805)
                ·
                  refine ⟨234462911999348321858401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1250468863996524383244805 234462911999348321858401)
                  ·
                    rfl

theorem cell22_2054767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 4].length) (baseStart_2054767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054767 prefixEnd_2054767 := by exact prefixLift 2054767
  have htrace : WordTrace (prefixWord ++ tailWord_2054767) baseStart_2054767 baseEnd_2054767 := by
    simpa [prefixWord, tailWord_2054767, baseEnd_2054767] using wordTrace_append hprefix tailTrace_2054767
  have hstable : (prefixWord ++ tailWord_2054767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054767).length < 2 ^ (prefixWord ++ tailWord_2054767).sum := by decide
  have hdescent : baseEnd_2054767 < baseStart_2054767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054780 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_2054780 : Nat := 118140960795 + 2054780 * 2 ^ 59
def prefixEnd_2054780 : Nat := 4983230072969 + 3 ^ 40 * 2054780 * 2
def baseEnd_2054780 : Nat := 703393186163717265000163

theorem tailTrace_2054780 : CollatzResearch.WordTrace tailWord_2054780 prefixEnd_2054780 703393186163717265000163 := by
  unfold tailWord_2054780
  simp only [CollatzResearch.WordTrace]
  refine ⟨37471991747945231665132897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49962655663926975553510529 37471991747945231665132897)
  ·
    refine ⟨28103993810958923748849673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37471991747945231665132897 28103993810958923748849673)
    ·
      refine ⟨21077995358219192811637255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28103993810958923748849673 21077995358219192811637255)
      ·
        refine ⟨31616993037328789217455883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21077995358219192811637255 31616993037328789217455883)
        ·
          refine ⟨47425489555993183826183825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31616993037328789217455883 47425489555993183826183825)
          ·
            refine ⟨35569117166994887869637869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47425489555993183826183825 35569117166994887869637869)
            ·
              refine ⟨13338418937623082951114201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35569117166994887869637869 13338418937623082951114201)
              ·
                refine ⟨10003814203217312213335651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13338418937623082951114201 10003814203217312213335651)
                ·
                  refine ⟨15005721304825968320003477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10003814203217312213335651 15005721304825968320003477)
                  ·
                    refine ⟨703393186163717265000163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15005721304825968320003477 703393186163717265000163)
                    ·
                      rfl

theorem cell22_2054780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_2054780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054780 prefixEnd_2054780 := by exact prefixLift 2054780
  have htrace : WordTrace (prefixWord ++ tailWord_2054780) baseStart_2054780 baseEnd_2054780 := by
    simpa [prefixWord, tailWord_2054780, baseEnd_2054780] using wordTrace_append hprefix tailTrace_2054780
  have hstable : (prefixWord ++ tailWord_2054780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054780).length < 2 ^ (prefixWord ++ tailWord_2054780).sum := by decide
  have hdescent : baseEnd_2054780 < baseStart_2054780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054812 : List Nat := [2, 2, 3, 2, 2, 3, 8]
def baseStart_2054812 : Nat := 118140960795 + 2054812 * 2 ^ 59
def prefixEnd_2054812 : Nat := 4983230072969 + 3 ^ 40 * 2054812 * 2
def baseEnd_2054812 : Nat := 26052005200654809192595

theorem tailTrace_2054812 : CollatzResearch.WordTrace tailWord_2054812 prefixEnd_2054812 26052005200654809192595 := by
  unfold tailWord_2054812
  simp only [CollatzResearch.WordTrace]
  refine ⟨37472575315887266397715345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49963433754516355196953793 37472575315887266397715345)
  ·
    refine ⟨28104431486915449798286509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37472575315887266397715345 28104431486915449798286509)
    ·
      refine ⟨10539161807593293674357441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28104431486915449798286509 10539161807593293674357441)
      ·
        refine ⟨7904371355694970255768081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10539161807593293674357441 7904371355694970255768081)
        ·
          refine ⟨5928278516771227691826061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7904371355694970255768081 5928278516771227691826061)
          ·
            refine ⟨2223104443789210384434773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5928278516771227691826061 2223104443789210384434773)
            ·
              refine ⟨26052005200654809192595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2223104443789210384434773 26052005200654809192595)
              ·
                rfl

theorem cell22_2054812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 8].length) (baseStart_2054812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054812 prefixEnd_2054812 := by exact prefixLift 2054812
  have htrace : WordTrace (prefixWord ++ tailWord_2054812) baseStart_2054812 baseEnd_2054812 := by
    simpa [prefixWord, tailWord_2054812, baseEnd_2054812] using wordTrace_append hprefix tailTrace_2054812
  have hstable : (prefixWord ++ tailWord_2054812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054812).length < 2 ^ (prefixWord ++ tailWord_2054812).sum := by decide
  have hdescent : baseEnd_2054812 < baseStart_2054812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054814 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_2054814 : Nat := 118140960795 + 2054814 * 2 ^ 59
def prefixEnd_2054814 : Nat := 4983230072969 + 3 ^ 40 * 2054814 * 2
def baseEnd_2054814 : Nat := 703404825058552509650059

theorem tailTrace_2054814 : CollatzResearch.WordTrace tailWord_2054814 prefixEnd_2054814 703404825058552509650059 := by
  unfold tailWord_2054814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9368152947220910892125437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49963482385178191424668997 9368152947220910892125437)
  ·
    refine ⟨3513057355207841584547039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9368152947220910892125437 3513057355207841584547039)
    ·
      refine ⟨5269586032811762376820559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3513057355207841584547039 5269586032811762376820559)
      ·
        refine ⟨7904379049217643565230839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5269586032811762376820559 7904379049217643565230839)
        ·
          refine ⟨11856568573826465347846259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7904379049217643565230839 11856568573826465347846259)
          ·
            refine ⟨17784852860739698021769389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11856568573826465347846259 17784852860739698021769389)
            ·
              refine ⟨6669319822777386758163521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17784852860739698021769389 6669319822777386758163521)
              ·
                refine ⟨5001989867083040068622641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6669319822777386758163521 5001989867083040068622641)
                ·
                  refine ⟨3751492400312280051466981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5001989867083040068622641 3751492400312280051466981)
                  ·
                    refine ⟨703404825058552509650059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3751492400312280051466981 703404825058552509650059)
                    ·
                      rfl

theorem cell22_2054814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_2054814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054814 prefixEnd_2054814 := by exact prefixLift 2054814
  have htrace : WordTrace (prefixWord ++ tailWord_2054814) baseStart_2054814 baseEnd_2054814 := by
    simpa [prefixWord, tailWord_2054814, baseEnd_2054814] using wordTrace_append hprefix tailTrace_2054814
  have hstable : (prefixWord ++ tailWord_2054814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054814).length < 2 ^ (prefixWord ++ tailWord_2054814).sum := by decide
  have hdescent : baseEnd_2054814 < baseStart_2054814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054855 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 3, 7]
def baseStart_2054855 : Nat := 118140960795 + 2054855 * 2 ^ 59
def prefixEnd_2054855 : Nat := 4983230072969 + 3 ^ 40 * 2054855 * 2
def baseEnd_2054855 : Nat := 703418860196442069374933

theorem tailTrace_2054855 : CollatzResearch.WordTrace tailWord_2054855 prefixEnd_2054855 703418860196442069374933 := by
  unfold tailWord_2054855
  simp only [CollatzResearch.WordTrace]
  refine ⟨74946718970618751139246019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49964479313745834092830679 74946718970618751139246019)
  ·
    refine ⟨112420078455928126708869029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74946718970618751139246019 112420078455928126708869029)
    ·
      refine ⟨21078764710486523757912943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112420078455928126708869029 21078764710486523757912943)
      ·
        refine ⟨31618147065729785636869415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21078764710486523757912943 31618147065729785636869415)
        ·
          refine ⟨47427220598594678455304123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31618147065729785636869415 47427220598594678455304123)
          ·
            refine ⟨71140830897892017682956185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47427220598594678455304123 71140830897892017682956185)
            ·
              refine ⟨53355623173419013262217139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71140830897892017682956185 53355623173419013262217139)
              ·
                refine ⟨80033434760128519893325709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53355623173419013262217139 80033434760128519893325709)
                ·
                  refine ⟨30012538035048194959997141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80033434760128519893325709 30012538035048194959997141)
                  ·
                    refine ⟨703418860196442069374933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30012538035048194959997141 703418860196442069374933)
                    ·
                      rfl

theorem cell22_2054855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_2054855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054855 prefixEnd_2054855 := by exact prefixLift 2054855
  have htrace : WordTrace (prefixWord ++ tailWord_2054855) baseStart_2054855 baseEnd_2054855 := by
    simpa [prefixWord, tailWord_2054855, baseEnd_2054855] using wordTrace_append hprefix tailTrace_2054855
  have hstable : (prefixWord ++ tailWord_2054855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054855).length < 2 ^ (prefixWord ++ tailWord_2054855).sum := by decide
  have hdescent : baseEnd_2054855 < baseStart_2054855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054962 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_2054962 : Nat := 118140960795 + 2054962 * 2 ^ 59
def prefixEnd_2054962 : Nat := 4983230072969 + 3 ^ 40 * 2054962 * 2
def baseEnd_2054962 : Nat := 703455488483129456949605

theorem tailTrace_2054962 : CollatzResearch.WordTrace tailWord_2054962 prefixEnd_2054962 703455488483129456949605 := by
  unfold tailWord_2054962
  simp only [CollatzResearch.WordTrace]
  refine ⟨18737655395307777103347785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49967081054154072275594093 18737655395307777103347785)
  ·
    refine ⟨14053241546480832827510839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18737655395307777103347785 14053241546480832827510839)
    ·
      refine ⟨21079862319721249241266259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14053241546480832827510839 21079862319721249241266259)
      ·
        refine ⟨31619793479581873861899389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21079862319721249241266259 31619793479581873861899389)
        ·
          refine ⟨11857422554843202698212271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31619793479581873861899389 11857422554843202698212271)
          ·
            refine ⟨17786133832264804047318407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11857422554843202698212271 17786133832264804047318407)
            ·
              refine ⟨26679200748397206070977611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17786133832264804047318407 26679200748397206070977611)
              ·
                refine ⟨40018801122595809106466417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26679200748397206070977611 40018801122595809106466417)
                ·
                  refine ⟨30014100841946856829849813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40018801122595809106466417 30014100841946856829849813)
                  ·
                    refine ⟨703455488483129456949605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30014100841946856829849813 703455488483129456949605)
                    ·
                      rfl

theorem cell22_2054962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_2054962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054962 prefixEnd_2054962 := by exact prefixLift 2054962
  have htrace : WordTrace (prefixWord ++ tailWord_2054962) baseStart_2054962 baseEnd_2054962 := by
    simpa [prefixWord, tailWord_2054962, baseEnd_2054962] using wordTrace_append hprefix tailTrace_2054962
  have hstable : (prefixWord ++ tailWord_2054962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054962).length < 2 ^ (prefixWord ++ tailWord_2054962).sum := by decide
  have hdescent : baseEnd_2054962 < baseStart_2054962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054992 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 7]
def baseStart_2054992 : Nat := 118140960795 + 2054992 * 2 ^ 59
def prefixEnd_2054992 : Nat := 4983230072969 + 3 ^ 40 * 2054992 * 2
def baseEnd_2054992 : Nat := 234488586032073126233171

theorem tailTrace_2054992 : CollatzResearch.WordTrace tailWord_2054992 prefixEnd_2054992 234488586032073126233171 := by
  unfold tailWord_2054992
  simp only [CollatzResearch.WordTrace]
  refine ⟨37475857885561211768491615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49967810514081615691322153 37475857885561211768491615)
  ·
    refine ⟨56213786828341817652737423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37475857885561211768491615 56213786828341817652737423)
    ·
      refine ⟨84320680242512726479106135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56213786828341817652737423 84320680242512726479106135)
      ·
        refine ⟨126481020363769089718659203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84320680242512726479106135 126481020363769089718659203)
        ·
          refine ⟨189721530545653634577988805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126481020363769089718659203 189721530545653634577988805)
          ·
            refine ⟨35572786977310056483372901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189721530545653634577988805 35572786977310056483372901)
            ·
              refine ⟨6669897558245635590632419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35572786977310056483372901 6669897558245635590632419)
              ·
                refine ⟨10004846337368453385948629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669897558245635590632419 10004846337368453385948629)
                ·
                  refine ⟨234488586032073126233171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10004846337368453385948629 234488586032073126233171)
                  ·
                    rfl

theorem cell22_2054992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_2054992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2054992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2054992 prefixEnd_2054992 := by exact prefixLift 2054992
  have htrace : WordTrace (prefixWord ++ tailWord_2054992) baseStart_2054992 baseEnd_2054992 := by
    simpa [prefixWord, tailWord_2054992, baseEnd_2054992] using wordTrace_append hprefix tailTrace_2054992
  have hstable : (prefixWord ++ tailWord_2054992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054992).length < 2 ^ (prefixWord ++ tailWord_2054992).sum := by decide
  have hdescent : baseEnd_2054992 < baseStart_2054992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055007 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 1, 7]
def baseStart_2055007 : Nat := 118140960795 + 2055007 * 2 ^ 59
def prefixEnd_2055007 : Nat := 4983230072969 + 3 ^ 40 * 2055007 * 2
def baseEnd_2055007 : Nat := 703470892902764339574467

theorem tailTrace_2055007 : CollatzResearch.WordTrace tailWord_2055007 prefixEnd_2055007 703470892902764339574467 := by
  unfold tailWord_2055007
  simp only [CollatzResearch.WordTrace]
  refine ⟨74952262866068081098779275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49968175244045387399186183 74952262866068081098779275)
  ·
    refine ⟨112428394299102121648168913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74952262866068081098779275 112428394299102121648168913)
    ·
      refine ⟨84321295724326591236126685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112428394299102121648168913 84321295724326591236126685)
      ·
        refine ⟨31620485896622471713547507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84321295724326591236126685 31620485896622471713547507)
        ·
          refine ⟨47430728844933707570321261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31620485896622471713547507 47430728844933707570321261)
          ·
            refine ⟨17786523316850140338870473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47430728844933707570321261 17786523316850140338870473)
            ·
              refine ⟨13339892487637605254152855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17786523316850140338870473 13339892487637605254152855)
              ·
                refine ⟨20009838731456407881229283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13339892487637605254152855 20009838731456407881229283)
                ·
                  refine ⟨30014758097184611821843925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20009838731456407881229283 30014758097184611821843925)
                  ·
                    refine ⟨703470892902764339574467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30014758097184611821843925 703470892902764339574467)
                    ·
                      rfl

theorem cell22_2055007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_2055007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055007 prefixEnd_2055007 := by exact prefixLift 2055007
  have htrace : WordTrace (prefixWord ++ tailWord_2055007) baseStart_2055007 baseEnd_2055007 := by
    simpa [prefixWord, tailWord_2055007, baseEnd_2055007] using wordTrace_append hprefix tailTrace_2055007
  have hstable : (prefixWord ++ tailWord_2055007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055007).length < 2 ^ (prefixWord ++ tailWord_2055007).sum := by decide
  have hdescent : baseEnd_2055007 < baseStart_2055007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055039 : List Nat := [1, 1, 2, 2, 1, 1, 4, 5, 1, 4]
def baseStart_2055039 : Nat := 118140960795 + 2055039 * 2 ^ 59
def prefixEnd_2055039 : Nat := 4983230072969 + 3 ^ 40 * 2055039 * 2
def baseEnd_2055039 : Nat := 703481847156726922774369

theorem tailTrace_2055039 : CollatzResearch.WordTrace tailWord_2055039 prefixEnd_2055039 703481847156726922774369 := by
  unfold tailWord_2055039
  simp only [CollatzResearch.WordTrace]
  refine ⟨74953430001952150563944171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49968953334634767042629447 74953430001952150563944171)
  ·
    refine ⟨112430145002928225845916257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74953430001952150563944171 112430145002928225845916257)
    ·
      refine ⟨84322608752196169384437193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112430145002928225845916257 84322608752196169384437193)
      ·
        refine ⟨63241956564147127038327895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84322608752196169384437193 63241956564147127038327895)
        ·
          refine ⟨94862934846220690557491843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63241956564147127038327895 94862934846220690557491843)
          ·
            refine ⟨142294402269331035836237765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94862934846220690557491843 142294402269331035836237765)
            ·
              refine ⟨26680200425499569219294581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142294402269331035836237765 26680200425499569219294581)
              ·
                refine ⟨2501268789890584614308867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26680200425499569219294581 2501268789890584614308867)
                ·
                  refine ⟨3751903184835876921463301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501268789890584614308867 3751903184835876921463301)
                  ·
                    refine ⟨703481847156726922774369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3751903184835876921463301 703481847156726922774369)
                    ·
                      rfl

theorem cell22_2055039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_2055039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055039 prefixEnd_2055039 := by exact prefixLift 2055039
  have htrace : WordTrace (prefixWord ++ tailWord_2055039) baseStart_2055039 baseEnd_2055039 := by
    simpa [prefixWord, tailWord_2055039, baseEnd_2055039] using wordTrace_append hprefix tailTrace_2055039
  have hstable : (prefixWord ++ tailWord_2055039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055039).length < 2 ^ (prefixWord ++ tailWord_2055039).sum := by decide
  have hdescent : baseEnd_2055039 < baseStart_2055039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055094 : List Nat := [5, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_2055094 : Nat := 118140960795 + 2055094 * 2 ^ 59
def prefixEnd_2055094 : Nat := 4983230072969 + 3 ^ 40 * 2055094 * 2
def baseEnd_2055094 : Nat := 234500224926908370883067

theorem tailTrace_2055094 : CollatzResearch.WordTrace tailWord_2055094 prefixEnd_2055094 234500224926908370883067 := by
  unfold tailWord_2055094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4684714751047055934824771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49970290677835263304797557 4684714751047055934824771)
  ·
    refine ⟨7027072126570583902237157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4684714751047055934824771 7027072126570583902237157)
    ·
      refine ⟨1317576023731984481669467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7027072126570583902237157 1317576023731984481669467)
      ·
        refine ⟨1976364035597976722504201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317576023731984481669467 1976364035597976722504201)
        ·
          refine ⟨1482273026698482541878151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1976364035597976722504201 1482273026698482541878151)
          ·
            refine ⟨2223409540047723812817227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482273026698482541878151 2223409540047723812817227)
            ·
              refine ⟨3335114310071585719225841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223409540047723812817227 3335114310071585719225841)
              ·
                refine ⟨2501335732553689289419381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3335114310071585719225841 2501335732553689289419381)
                ·
                  refine ⟨234500224926908370883067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2501335732553689289419381 234500224926908370883067)
                  ·
                    rfl

theorem cell22_2055094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_2055094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055094 prefixEnd_2055094 := by exact prefixLift 2055094
  have htrace : WordTrace (prefixWord ++ tailWord_2055094) baseStart_2055094 baseEnd_2055094 := by
    simpa [prefixWord, tailWord_2055094, baseEnd_2055094] using wordTrace_append hprefix tailTrace_2055094
  have hstable : (prefixWord ++ tailWord_2055094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055094).length < 2 ^ (prefixWord ++ tailWord_2055094).sum := by decide
  have hdescent : baseEnd_2055094 < baseStart_2055094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055133 : List Nat := [1, 4, 3, 1, 2, 3, 2, 6]
def baseStart_2055133 : Nat := 118140960795 + 2055133 * 2 ^ 59
def prefixEnd_2055133 : Nat := 4983230072969 + 3 ^ 40 * 2055133 * 2
def baseEnd_2055133 : Nat := 78168225030860223436009

theorem tailTrace_2055133 : CollatzResearch.WordTrace tailWord_2055133 prefixEnd_2055133 78168225030860223436009 := by
  unfold tailWord_2055133
  simp only [CollatzResearch.WordTrace]
  refine ⟨74956858463611604617866053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49971238975741069745244035 74956858463611604617866053)
  ·
    refine ⟨14054410961927175865849885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74956858463611604617866053 14054410961927175865849885)
    ·
      refine ⟨5270404110722690949693707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14054410961927175865849885 5270404110722690949693707)
      ·
        refine ⟨7905606166084036424540561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5270404110722690949693707 7905606166084036424540561)
        ·
          refine ⟨5929204624563027318405421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7905606166084036424540561 5929204624563027318405421)
          ·
            refine ⟨2223451734211135244402033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5929204624563027318405421 2223451734211135244402033)
            ·
              refine ⟨1667588800658351433301525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223451734211135244402033 1667588800658351433301525)
              ·
                refine ⟨78168225030860223436009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1667588800658351433301525 78168225030860223436009)
                ·
                  rfl

theorem cell22_2055133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 6].length) (baseStart_2055133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055133 prefixEnd_2055133 := by exact prefixLift 2055133
  have htrace : WordTrace (prefixWord ++ tailWord_2055133) baseStart_2055133 baseEnd_2055133 := by
    simpa [prefixWord, tailWord_2055133, baseEnd_2055133] using wordTrace_append hprefix tailTrace_2055133
  have hstable : (prefixWord ++ tailWord_2055133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055133).length < 2 ^ (prefixWord ++ tailWord_2055133).sum := by decide
  have hdescent : baseEnd_2055133 < baseStart_2055133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055144 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 7]
def baseStart_2055144 : Nat := 118140960795 + 2055144 * 2 ^ 59
def prefixEnd_2055144 : Nat := 4983230072969 + 3 ^ 40 * 2055144 * 2
def baseEnd_2055144 : Nat := 234505930267513882966349

theorem tailTrace_2055144 : CollatzResearch.WordTrace tailWord_2055144 prefixEnd_2055144 234505930267513882966349 := by
  unfold tailWord_2055144
  simp only [CollatzResearch.WordTrace]
  refine ⟨37478629833285876748258243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49971506444381168997677657 37478629833285876748258243)
  ·
    refine ⟨56217944749928815122387365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37478629833285876748258243 56217944749928815122387365)
    ·
      refine ⟨10540864640611652835447631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56217944749928815122387365 10540864640611652835447631)
      ·
        refine ⟨15811296960917479253171447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10540864640611652835447631 15811296960917479253171447)
        ·
          refine ⟨23716945441376218879757171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15811296960917479253171447 23716945441376218879757171)
          ·
            refine ⟨35575418162064328319635757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23716945441376218879757171 35575418162064328319635757)
            ·
              refine ⟨13340781810774123119863409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35575418162064328319635757 13340781810774123119863409)
              ·
                refine ⟨10005586358080592339897557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13340781810774123119863409 10005586358080592339897557)
                ·
                  refine ⟨234505930267513882966349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10005586358080592339897557 234505930267513882966349)
                  ·
                    rfl

theorem cell22_2055144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_2055144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055144 prefixEnd_2055144 := by exact prefixLift 2055144
  have htrace : WordTrace (prefixWord ++ tailWord_2055144) baseStart_2055144 baseEnd_2055144 := by
    simpa [prefixWord, tailWord_2055144, baseEnd_2055144] using wordTrace_append hprefix tailTrace_2055144
  have hstable : (prefixWord ++ tailWord_2055144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055144).length < 2 ^ (prefixWord ++ tailWord_2055144).sum := by decide
  have hdescent : baseEnd_2055144 < baseStart_2055144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055156 : List Nat := [2, 6, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2055156 : Nat := 118140960795 + 2055156 * 2 ^ 59
def prefixEnd_2055156 : Nat := 4983230072969 + 3 ^ 40 * 2055156 * 2
def baseEnd_2055156 : Nat := 234507299549259205866337

theorem tailTrace_2055156 : CollatzResearch.WordTrace tailWord_2055156 prefixEnd_2055156 234507299549259205866337 := by
  unfold tailWord_2055156
  simp only [CollatzResearch.WordTrace]
  refine ⟨37478848671264139772976661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49971798228352186363968881 37478848671264139772976661)
  ·
    refine ⟨1756821031465506551858281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37478848671264139772976661 1756821031465506551858281)
    ·
      refine ⟨1317615773599129913893711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1756821031465506551858281 1317615773599129913893711)
      ·
        refine ⟨1976423660398694870840567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317615773599129913893711 1976423660398694870840567)
        ·
          refine ⟨2964635490598042306260851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976423660398694870840567 2964635490598042306260851)
          ·
            refine ⟨4446953235897063459391277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2964635490598042306260851 4446953235897063459391277)
            ·
              refine ⟨1667607463461398797271729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4446953235897063459391277 1667607463461398797271729)
              ·
                refine ⟨1250705597596049097953797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667607463461398797271729 1250705597596049097953797)
                ·
                  refine ⟨234507299549259205866337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1250705597596049097953797 234507299549259205866337)
                  ·
                    rfl

theorem cell22_2055156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2055156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055156 prefixEnd_2055156 := by exact prefixLift 2055156
  have htrace : WordTrace (prefixWord ++ tailWord_2055156) baseStart_2055156 baseEnd_2055156 := by
    simpa [prefixWord, tailWord_2055156, baseEnd_2055156] using wordTrace_append hprefix tailTrace_2055156
  have hstable : (prefixWord ++ tailWord_2055156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055156).length < 2 ^ (prefixWord ++ tailWord_2055156).sum := by decide
  have hdescent : baseEnd_2055156 < baseStart_2055156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055178 : List Nat := [3, 1, 2, 2, 3, 1, 4, 1, 5]
def baseStart_2055178 : Nat := 118140960795 + 2055178 * 2 ^ 59
def prefixEnd_2055178 : Nat := 4983230072969 + 3 ^ 40 * 2055178 * 2
def baseEnd_2055178 : Nat := 234509809899125631182981

theorem tailTrace_2055178 : CollatzResearch.WordTrace tailWord_2055178 prefixEnd_2055178 234509809899125631182981 := by
  unfold tailWord_2055178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18739624937112144325813547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49972333165632384868836125 18739624937112144325813547)
  ·
    refine ⟨28109437405668216488720321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18739624937112144325813547 28109437405668216488720321)
    ·
      refine ⟨21082078054251162366540241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28109437405668216488720321 21082078054251162366540241)
      ·
        refine ⟨15811558540688371774905181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21082078054251162366540241 15811558540688371774905181)
        ·
          refine ⟨5929334452758139415589443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15811558540688371774905181 5929334452758139415589443)
          ·
            refine ⟨8894001679137209123384165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929334452758139415589443 8894001679137209123384165)
            ·
              refine ⟨1667625314838226710634531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8894001679137209123384165 1667625314838226710634531)
              ·
                refine ⟨2501437972257340065951797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1667625314838226710634531 2501437972257340065951797)
                ·
                  refine ⟨234509809899125631182981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2501437972257340065951797 234509809899125631182981)
                  ·
                    rfl

theorem cell22_2055178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_2055178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055178 prefixEnd_2055178 := by exact prefixLift 2055178
  have htrace : WordTrace (prefixWord ++ tailWord_2055178) baseStart_2055178 baseEnd_2055178 := by
    simpa [prefixWord, tailWord_2055178, baseEnd_2055178] using wordTrace_append hprefix tailTrace_2055178
  have hstable : (prefixWord ++ tailWord_2055178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055178).length < 2 ^ (prefixWord ++ tailWord_2055178).sum := by decide
  have hdescent : baseEnd_2055178 < baseStart_2055178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055219 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 3, 6]
def baseStart_2055219 : Nat := 118140960795 + 2055219 * 2 ^ 59
def prefixEnd_2055219 : Nat := 4983230072969 + 3 ^ 40 * 2055219 * 2
def baseEnd_2055219 : Nat := 703543464835266453273817

theorem tailTrace_2055219 : CollatzResearch.WordTrace tailWord_2055219 prefixEnd_2055219 703543464835266453273817 := by
  unfold tailWord_2055219
  simp only [CollatzResearch.WordTrace]
  refine ⟨74959995141300041305496711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49973330094200027536997807 74959995141300041305496711)
  ·
    refine ⟨112439992711950061958245067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74959995141300041305496711 112439992711950061958245067)
    ·
      refine ⟨168659989067925092937367601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112439992711950061958245067 168659989067925092937367601)
      ·
        refine ⟨126494991800943819703025701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168659989067925092937367601 126494991800943819703025701)
        ·
          refine ⟨23717810962676966194317319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126494991800943819703025701 23717810962676966194317319)
          ·
            refine ⟨35576716444015449291475979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23717810962676966194317319 35576716444015449291475979)
            ·
              refine ⟨53365074666023173937213969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35576716444015449291475979 53365074666023173937213969)
              ·
                refine ⟨40023805999517380452910477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53365074666023173937213969 40023805999517380452910477)
                ·
                  refine ⟨15008927249819017669841429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40023805999517380452910477 15008927249819017669841429)
                  ·
                    refine ⟨703543464835266453273817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15008927249819017669841429 703543464835266453273817)
                    ·
                      rfl

theorem cell22_2055219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_2055219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055219 prefixEnd_2055219 := by exact prefixLift 2055219
  have htrace : WordTrace (prefixWord ++ tailWord_2055219) baseStart_2055219 baseEnd_2055219 := by
    simpa [prefixWord, tailWord_2055219, baseEnd_2055219] using wordTrace_append hprefix tailTrace_2055219
  have hstable : (prefixWord ++ tailWord_2055219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055219).length < 2 ^ (prefixWord ++ tailWord_2055219).sum := by decide
  have hdescent : baseEnd_2055219 < baseStart_2055219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055296 : List Nat := [2, 1, 1, 2, 1, 3, 2, 5, 5]
def baseStart_2055296 : Nat := 118140960795 + 2055296 * 2 ^ 59
def prefixEnd_2055296 : Nat := 4983230072969 + 3 ^ 40 * 2055296 * 2
def baseEnd_2055296 : Nat := 234523274502954639699527

theorem tailTrace_2055296 : CollatzResearch.WordTrace tailWord_2055296 prefixEnd_2055296 234523274502954639699527 := by
  unfold tailWord_2055296
  simp only [CollatzResearch.WordTrace]
  refine ⟨37481401781010541728024871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49975202374680722304033161 37481401781010541728024871)
  ·
    refine ⟨56222102671515812592037307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37481401781010541728024871 56222102671515812592037307)
    ·
      refine ⟨84333154007273718888055961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56222102671515812592037307 84333154007273718888055961)
      ·
        refine ⟨63249865505455289166041971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84333154007273718888055961 63249865505455289166041971)
        ·
          refine ⟨94874798258182933749062957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63249865505455289166041971 94874798258182933749062957)
          ·
            refine ⟨35578049346818600155898609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94874798258182933749062957 35578049346818600155898609)
            ·
              refine ⟨26683537010113950116923957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35578049346818600155898609 26683537010113950116923957)
              ·
                refine ⟨2501581594698182823461621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26683537010113950116923957 2501581594698182823461621)
                ·
                  refine ⟨234523274502954639699527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2501581594698182823461621 234523274502954639699527)
                  ·
                    rfl

theorem cell22_2055296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 5].length) (baseStart_2055296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055296 prefixEnd_2055296 := by exact prefixLift 2055296
  have htrace : WordTrace (prefixWord ++ tailWord_2055296) baseStart_2055296 baseEnd_2055296 := by
    simpa [prefixWord, tailWord_2055296, baseEnd_2055296] using wordTrace_append hprefix tailTrace_2055296
  have hstable : (prefixWord ++ tailWord_2055296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055296).length < 2 ^ (prefixWord ++ tailWord_2055296).sum := by decide
  have hdescent : baseEnd_2055296 < baseStart_2055296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055392 : List Nat := [2, 1, 1, 3, 1, 6, 2, 2, 4]
def baseStart_2055392 : Nat := 118140960795 + 2055392 * 2 ^ 59
def prefixEnd_2055392 : Nat := 4983230072969 + 3 ^ 40 * 2055392 * 2
def baseEnd_2055392 : Nat := 234534228756917222899429

theorem tailTrace_2055392 : CollatzResearch.WordTrace tailWord_2055392 prefixEnd_2055392 234534228756917222899429 := by
  unfold tailWord_2055392
  simp only [CollatzResearch.WordTrace]
  refine ⟨37483152484836645925772215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49977536646448861234362953 37483152484836645925772215)
  ·
    refine ⟨56224728727254968888658323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37483152484836645925772215 56224728727254968888658323)
    ·
      refine ⟨84337093090882453332987485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56224728727254968888658323 84337093090882453332987485)
      ·
        refine ⟨31626409909080919999870307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84337093090882453332987485 31626409909080919999870307)
        ·
          refine ⟨47439614863621379999805461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31626409909080919999870307 47439614863621379999805461)
          ·
            refine ⟨2223731946732252187490881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47439614863621379999805461 2223731946732252187490881)
            ·
              refine ⟨1667798960049189140618161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223731946732252187490881 1667798960049189140618161)
              ·
                refine ⟨1250849220036891855463621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667798960049189140618161 1250849220036891855463621)
                ·
                  refine ⟨234534228756917222899429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1250849220036891855463621 234534228756917222899429)
                  ·
                    rfl

theorem cell22_2055392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 4].length) (baseStart_2055392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055392 prefixEnd_2055392 := by exact prefixLift 2055392
  have htrace : WordTrace (prefixWord ++ tailWord_2055392) baseStart_2055392 baseEnd_2055392 := by
    simpa [prefixWord, tailWord_2055392, baseEnd_2055392] using wordTrace_append hprefix tailTrace_2055392
  have hstable : (prefixWord ++ tailWord_2055392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055392).length < 2 ^ (prefixWord ++ tailWord_2055392).sum := by decide
  have hdescent : baseEnd_2055392 < baseStart_2055392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055403 : List Nat := [1, 1, 1, 1, 2, 8, 1, 7]
def baseStart_2055403 : Nat := 118140960795 + 2055403 * 2 ^ 59
def prefixEnd_2055403 : Nat := 4983230072969 + 3 ^ 40 * 2055403 * 2
def baseEnd_2055403 : Nat := 78178494643950145185917

theorem tailTrace_2055403 : CollatzResearch.WordTrace tailWord_2055403 prefixEnd_2055403 78178494643950145185917 := by
  unfold tailWord_2055403
  simp only [CollatzResearch.WordTrace]
  refine ⟨74966706172633440730194863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49977804115088960486796575 74966706172633440730194863)
  ·
    refine ⟨112450059258950161095292295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74966706172633440730194863 112450059258950161095292295)
    ·
      refine ⟨168675088888425241642938443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112450059258950161095292295 168675088888425241642938443)
      ·
        refine ⟨253012633332637862464407665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168675088888425241642938443 253012633332637862464407665)
        ·
          refine ⟨189759474999478396848305749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253012633332637862464407665 189759474999478396848305749)
          ·
            refine ⟨2223743847650137463066083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 189759474999478396848305749 2223743847650137463066083)
            ·
              refine ⟨3335615771475206194599125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223743847650137463066083 3335615771475206194599125)
              ·
                refine ⟨78178494643950145185917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3335615771475206194599125 78178494643950145185917)
                ·
                  rfl

theorem cell22_2055403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 7].length) (baseStart_2055403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055403 prefixEnd_2055403 := by exact prefixLift 2055403
  have htrace : WordTrace (prefixWord ++ tailWord_2055403) baseStart_2055403 baseEnd_2055403 := by
    simpa [prefixWord, tailWord_2055403, baseEnd_2055403] using wordTrace_append hprefix tailTrace_2055403
  have hstable : (prefixWord ++ tailWord_2055403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055403).length < 2 ^ (prefixWord ++ tailWord_2055403).sum := by decide
  have hdescent : baseEnd_2055403 < baseStart_2055403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055420 : List Nat := [2, 2, 2, 1, 5, 1, 3, 6]
def baseStart_2055420 : Nat := 118140960795 + 2055420 * 2 ^ 59
def prefixEnd_2055420 : Nat := 4983230072969 + 3 ^ 40 * 2055420 * 2
def baseEnd_2055420 : Nat := 78179141249218769888689

theorem tailTrace_2055420 : CollatzResearch.WordTrace tailWord_2055420 prefixEnd_2055420 78179141249218769888689 := by
  unfold tailWord_2055420
  simp only [CollatzResearch.WordTrace]
  refine ⟨37483663106785926316781857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49978217475714568422375809 37483663106785926316781857)
  ·
    refine ⟨28112747330089444737586393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37483663106785926316781857 28112747330089444737586393)
    ·
      refine ⟨21084560497567083553189795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28112747330089444737586393 21084560497567083553189795)
      ·
        refine ⟨31626840746350625329784693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21084560497567083553189795 31626840746350625329784693)
        ·
          refine ⟨2965016319970371124667315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31626840746350625329784693 2965016319970371124667315)
          ·
            refine ⟨4447524479955556687000973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965016319970371124667315 4447524479955556687000973)
            ·
              refine ⟨1667821679983333757625365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4447524479955556687000973 1667821679983333757625365)
              ·
                refine ⟨78179141249218769888689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1667821679983333757625365 78179141249218769888689)
                ·
                  rfl

theorem cell22_2055420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 6].length) (baseStart_2055420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055420 prefixEnd_2055420 := by exact prefixLift 2055420
  have htrace : WordTrace (prefixWord ++ tailWord_2055420) baseStart_2055420 baseEnd_2055420 := by
    simpa [prefixWord, tailWord_2055420, baseEnd_2055420] using wordTrace_append hprefix tailTrace_2055420
  have hstable : (prefixWord ++ tailWord_2055420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055420).length < 2 ^ (prefixWord ++ tailWord_2055420).sum := by decide
  have hdescent : baseEnd_2055420 < baseStart_2055420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055422 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_2055422 : Nat := 118140960795 + 2055422 * 2 ^ 59
def prefixEnd_2055422 : Nat := 4983230072969 + 3 ^ 40 * 2055422 * 2
def baseEnd_2055422 : Nat := 703612955883841590448195

theorem tailTrace_2055422 : CollatzResearch.WordTrace tailWord_2055422 prefixEnd_2055422 703612955883841590448195 := by
  unfold tailWord_2055422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9370924894945575871892065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49978266106376404650091013 9370924894945575871892065)
  ·
    refine ⟨7028193671209181903919049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9370924894945575871892065 7028193671209181903919049)
    ·
      refine ⟨5271145253406886427939287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7028193671209181903919049 5271145253406886427939287)
      ·
        refine ⟨7906717880110329641908931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271145253406886427939287 7906717880110329641908931)
        ·
          refine ⟨11860076820165494462863397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7906717880110329641908931 11860076820165494462863397)
          ·
            refine ⟨2223764403781030211786887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11860076820165494462863397 2223764403781030211786887)
            ·
              refine ⟨3335646605671545317680331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223764403781030211786887 3335646605671545317680331)
              ·
                refine ⟨5003469908507317976520497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3335646605671545317680331 5003469908507317976520497)
                ·
                  refine ⟨3752602431380488482390373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5003469908507317976520497 3752602431380488482390373)
                  ·
                    refine ⟨703612955883841590448195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3752602431380488482390373 703612955883841590448195)
                    ·
                      rfl

theorem cell22_2055422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_2055422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055422 prefixEnd_2055422 := by exact prefixLift 2055422
  have htrace : WordTrace (prefixWord ++ tailWord_2055422) baseStart_2055422 baseEnd_2055422 := by
    simpa [prefixWord, tailWord_2055422, baseEnd_2055422] using wordTrace_append hprefix tailTrace_2055422
  have hstable : (prefixWord ++ tailWord_2055422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055422).length < 2 ^ (prefixWord ++ tailWord_2055422).sum := by decide
  have hdescent : baseEnd_2055422 < baseStart_2055422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055448 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 7]
def baseStart_2055448 : Nat := 118140960795 + 2055448 * 2 ^ 59
def prefixEnd_2055448 : Nat := 4983230072969 + 3 ^ 40 * 2055448 * 2
def baseEnd_2055448 : Nat := 234540618738395396432705

theorem tailTrace_2055448 : CollatzResearch.WordTrace tailWord_2055448 prefixEnd_2055448 234540618738395396432705 := by
  unfold tailWord_2055448
  simp only [CollatzResearch.WordTrace]
  refine ⟨37484173728735206707791499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49978898304980275610388665 37484173728735206707791499)
  ·
    refine ⟨56226260593102810061687249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37484173728735206707791499 56226260593102810061687249)
    ·
      refine ⟨42169695444827107546265437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56226260593102810061687249 42169695444827107546265437)
      ·
        refine ⟨15813635791810165329849539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42169695444827107546265437 15813635791810165329849539)
        ·
          refine ⟨23720453687715247994774309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15813635791810165329849539 23720453687715247994774309)
          ·
            refine ⟨4447585066446608999020183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23720453687715247994774309 4447585066446608999020183)
            ·
              refine ⟨6671377599669913498530275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4447585066446608999020183 6671377599669913498530275)
              ·
                refine ⟨10007066399504870247795413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6671377599669913498530275 10007066399504870247795413)
                ·
                  refine ⟨234540618738395396432705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10007066399504870247795413 234540618738395396432705)
                  ·
                    rfl

theorem cell22_2055448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_2055448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055448 prefixEnd_2055448 := by exact prefixLift 2055448
  have htrace : WordTrace (prefixWord ++ tailWord_2055448) baseStart_2055448 baseEnd_2055448 := by
    simpa [prefixWord, tailWord_2055448, baseEnd_2055448] using wordTrace_append hprefix tailTrace_2055448
  have hstable : (prefixWord ++ tailWord_2055448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055448).length < 2 ^ (prefixWord ++ tailWord_2055448).sum := by decide
  have hdescent : baseEnd_2055448 < baseStart_2055448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055452 : List Nat := [2, 2, 3, 1, 1, 1, 4, 4, 1, 3]
def baseStart_2055452 : Nat := 118140960795 + 2055452 * 2 ^ 59
def prefixEnd_2055452 : Nat := 4983230072969 + 3 ^ 40 * 2055452 * 2
def baseEnd_2055452 : Nat := 703623225496931512198103

theorem tailTrace_2055452 : CollatzResearch.WordTrace tailWord_2055452 prefixEnd_2055452 703623225496931512198103 := by
  unfold tailWord_2055452
  simp only [CollatzResearch.WordTrace]
  refine ⟨37484246674727961049364305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49978995566303948065819073 37484246674727961049364305)
  ·
    refine ⟨28113185006045970787023229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37484246674727961049364305 28113185006045970787023229)
    ·
      refine ⟨10542444377267239045133711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28113185006045970787023229 10542444377267239045133711)
      ·
        refine ⟨15813666565900858567700567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10542444377267239045133711 15813666565900858567700567)
        ·
          refine ⟨23720499848851287851550851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15813666565900858567700567 23720499848851287851550851)
          ·
            refine ⟨35580749773276931777326277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23720499848851287851550851 35580749773276931777326277)
            ·
              refine ⟨6671390582489424708248677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35580749773276931777326277 6671390582489424708248677)
              ·
                refine ⟨1250885734216767132796627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6671390582489424708248677 1250885734216767132796627)
                ·
                  refine ⟨1876328601325150699194941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250885734216767132796627 1876328601325150699194941)
                  ·
                    refine ⟨703623225496931512198103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1876328601325150699194941 703623225496931512198103)
                    ·
                      rfl

theorem cell22_2055452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_2055452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055452 prefixEnd_2055452 := by exact prefixLift 2055452
  have htrace : WordTrace (prefixWord ++ tailWord_2055452) baseStart_2055452 baseEnd_2055452 := by
    simpa [prefixWord, tailWord_2055452, baseEnd_2055452] using wordTrace_append hprefix tailTrace_2055452
  have hstable : (prefixWord ++ tailWord_2055452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055452).length < 2 ^ (prefixWord ++ tailWord_2055452).sum := by decide
  have hdescent : baseEnd_2055452 < baseStart_2055452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055495 : List Nat := [1, 1, 4, 1, 2, 3, 2, 3, 1, 4]
def baseStart_2055495 : Nat := 118140960795 + 2055495 * 2 ^ 59
def prefixEnd_2055495 : Nat := 4983230072969 + 3 ^ 40 * 2055495 * 2
def baseEnd_2055495 : Nat := 703637945275693733372971

theorem tailTrace_2055495 : CollatzResearch.WordTrace tailWord_2055495 prefixEnd_2055495 703637945275693733372971 := by
  unfold tailWord_2055495
  simp only [CollatzResearch.WordTrace]
  refine ⟨74970061688300140442543939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49980041125533426961695959 74970061688300140442543939)
  ·
    refine ⟨112455092532450210663815909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74970061688300140442543939 112455092532450210663815909)
    ·
      refine ⟨21085329849834414499465483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112455092532450210663815909 21085329849834414499465483)
      ·
        refine ⟨31627994774751621749198225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21085329849834414499465483 31627994774751621749198225)
        ·
          refine ⟨23720996081063716311898669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31627994774751621749198225 23720996081063716311898669)
          ·
            refine ⟨8895373530398893616962001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23720996081063716311898669 8895373530398893616962001)
            ·
              refine ⟨6671530147799170212721501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8895373530398893616962001 6671530147799170212721501)
              ·
                refine ⟨2501823805424688829770563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6671530147799170212721501 2501823805424688829770563)
                ·
                  refine ⟨3752735708137033244655845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501823805424688829770563 3752735708137033244655845)
                  ·
                    refine ⟨703637945275693733372971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3752735708137033244655845 703637945275693733372971)
                    ·
                      rfl

theorem cell22_2055495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_2055495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055495 prefixEnd_2055495 := by exact prefixLift 2055495
  have htrace : WordTrace (prefixWord ++ tailWord_2055495) baseStart_2055495 baseEnd_2055495 := by
    simpa [prefixWord, tailWord_2055495, baseEnd_2055495] using wordTrace_append hprefix tailTrace_2055495
  have hstable : (prefixWord ++ tailWord_2055495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055495).length < 2 ^ (prefixWord ++ tailWord_2055495).sum := by decide
  have hdescent : baseEnd_2055495 < baseStart_2055495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055538 : List Nat := [3, 2, 1, 2, 1, 2, 1, 10]
def baseStart_2055538 : Nat := 118140960795 + 2055538 * 2 ^ 59
def prefixEnd_2055538 : Nat := 4983230072969 + 3 ^ 40 * 2055538 * 2
def baseEnd_2055538 : Nat := 78183629450495106060871

theorem tailTrace_2055538 : CollatzResearch.WordTrace tailWord_2055538 prefixEnd_2055538 78183629450495106060871 := by
  unfold tailWord_2055538
  simp only [CollatzResearch.WordTrace]
  refine ⟨18742907506786089696589817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49981086684762905857572845 18742907506786089696589817)
  ·
    refine ⟨14057180630089567272442363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18742907506786089696589817 14057180630089567272442363)
    ·
      refine ⟨21085770945134350908663545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14057180630089567272442363 21085770945134350908663545)
      ·
        refine ⟨15814328208850763181497659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21085770945134350908663545 15814328208850763181497659)
        ·
          refine ⟨23721492313276144772246489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15814328208850763181497659 23721492313276144772246489)
          ·
            refine ⟨17791119234957108579184867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23721492313276144772246489 17791119234957108579184867)
            ·
              refine ⟨26686678852435662868777301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17791119234957108579184867 26686678852435662868777301)
              ·
                refine ⟨78183629450495106060871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26686678852435662868777301 78183629450495106060871)
                ·
                  rfl

theorem cell22_2055538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_2055538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055538 prefixEnd_2055538 := by exact prefixLift 2055538
  have htrace : WordTrace (prefixWord ++ tailWord_2055538) baseStart_2055538 baseEnd_2055538 := by
    simpa [prefixWord, tailWord_2055538, baseEnd_2055538] using wordTrace_append hprefix tailTrace_2055538
  have hstable : (prefixWord ++ tailWord_2055538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055538).length < 2 ^ (prefixWord ++ tailWord_2055538).sum := by decide
  have hdescent : baseEnd_2055538 < baseStart_2055538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055561 : List Nat := [1, 2, 1, 1, 8, 1, 2, 2, 4]
def baseStart_2055561 : Nat := 118140960795 + 2055561 * 2 ^ 59
def prefixEnd_2055561 : Nat := 4983230072969 + 3 ^ 40 * 2055561 * 2
def baseEnd_2055561 : Nat := 234553512808163853740923

theorem tailTrace_2055561 : CollatzResearch.WordTrace tailWord_2055561 prefixEnd_2055561 234553512808163853740923 := by
  unfold tailWord_2055561
  simp only [CollatzResearch.WordTrace]
  refine ⟨74972468906061033714446537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49981645937374022476297691 74972468906061033714446537)
  ·
    refine ⟨56229351679545775285834903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74972468906061033714446537 56229351679545775285834903)
    ·
      refine ⟨84344027519318662928752355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56229351679545775285834903 84344027519318662928752355)
      ·
        refine ⟨126516041278977994393128533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84344027519318662928752355 126516041278977994393128533)
        ·
          refine ⟨1482609858738023371794475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 126516041278977994393128533 1482609858738023371794475)
          ·
            refine ⟨2223914788107035057691713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482609858738023371794475 2223914788107035057691713)
            ·
              refine ⟨1667936091080276293268785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223914788107035057691713 1667936091080276293268785)
              ·
                refine ⟨1250952068310207219951589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667936091080276293268785 1250952068310207219951589)
                ·
                  refine ⟨234553512808163853740923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1250952068310207219951589 234553512808163853740923)
                  ·
                    rfl

theorem cell22_2055561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 4].length) (baseStart_2055561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055561 prefixEnd_2055561 := by exact prefixLift 2055561
  have htrace : WordTrace (prefixWord ++ tailWord_2055561) baseStart_2055561 baseEnd_2055561 := by
    simpa [prefixWord, tailWord_2055561, baseEnd_2055561] using wordTrace_append hprefix tailTrace_2055561
  have hstable : (prefixWord ++ tailWord_2055561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055561).length < 2 ^ (prefixWord ++ tailWord_2055561).sum := by decide
  have hdescent : baseEnd_2055561 < baseStart_2055561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055572 : List Nat := [2, 4, 2, 1, 2, 3, 1, 7]
def baseStart_2055572 : Nat := 118140960795 + 2055572 * 2 ^ 59
def prefixEnd_2055572 : Nat := 4983230072969 + 3 ^ 40 * 2055572 * 2
def baseEnd_2055572 : Nat := 78184922661032355466415

theorem tailTrace_2055572 : CollatzResearch.WordTrace tailWord_2055572 prefixEnd_2055572 78184922661032355466415 := by
  unfold tailWord_2055572
  simp only [CollatzResearch.WordTrace]
  refine ⟨37486435054510591296548485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49981913406014121728731313 37486435054510591296548485)
  ·
    refine ⟨7028706572720735868102841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37486435054510591296548485 7028706572720735868102841)
    ·
      refine ⟨5271529929540551901077131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7028706572720735868102841 5271529929540551901077131)
      ·
        refine ⟨7907294894310827851615697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271529929540551901077131 7907294894310827851615697)
        ·
          refine ⟨5930471170733120888711773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7907294894310827851615697 5930471170733120888711773)
          ·
            refine ⟨2223926689024920333266915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5930471170733120888711773 2223926689024920333266915)
            ·
              refine ⟨3335890033537380499900373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223926689024920333266915 3335890033537380499900373)
              ·
                refine ⟨78184922661032355466415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3335890033537380499900373 78184922661032355466415)
                ·
                  rfl

theorem cell22_2055572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 7].length) (baseStart_2055572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055572 prefixEnd_2055572 := by exact prefixLift 2055572
  have htrace : WordTrace (prefixWord ++ tailWord_2055572) baseStart_2055572 baseEnd_2055572 := by
    simpa [prefixWord, tailWord_2055572, baseEnd_2055572] using wordTrace_append hprefix tailTrace_2055572
  have hstable : (prefixWord ++ tailWord_2055572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055572).length < 2 ^ (prefixWord ++ tailWord_2055572).sum := by decide
  have hdescent : baseEnd_2055572 < baseStart_2055572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055630 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_2055630 : Nat := 118140960795 + 2055630 * 2 ^ 59
def prefixEnd_2055630 : Nat := 4983230072969 + 3 ^ 40 * 2055630 * 2
def baseEnd_2055630 : Nat := 703684158534598381247557

theorem tailTrace_2055630 : CollatzResearch.WordTrace tailWord_2055630 prefixEnd_2055630 703684158534598381247557 := by
  unfold tailWord_2055630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9371873192851382312338543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49983323695207372332472229 9371873192851382312338543)
  ·
    refine ⟨14057809789277073468507815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9371873192851382312338543 14057809789277073468507815)
    ·
      refine ⟨21086714683915610202761723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14057809789277073468507815 21086714683915610202761723)
      ·
        refine ⟨31630072025873415304142585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21086714683915610202761723 31630072025873415304142585)
        ·
          refine ⟨23722554019405061478106939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31630072025873415304142585 23722554019405061478106939)
          ·
            refine ⟨35583831029107592217160409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23722554019405061478106939 35583831029107592217160409)
            ·
              refine ⟨26687873271830694162870307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35583831029107592217160409 26687873271830694162870307)
              ·
                refine ⟨40031809907746041244305461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26687873271830694162870307 40031809907746041244305461)
                ·
                  refine ⟨3752982178851191366653637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40031809907746041244305461 3752982178851191366653637)
                  ·
                    refine ⟨703684158534598381247557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3752982178851191366653637 703684158534598381247557)
                    ·
                      rfl

theorem cell22_2055630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_2055630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055630 prefixEnd_2055630 := by exact prefixLift 2055630
  have htrace : WordTrace (prefixWord ++ tailWord_2055630) baseStart_2055630 baseEnd_2055630 := by
    simpa [prefixWord, tailWord_2055630, baseEnd_2055630] using wordTrace_append hprefix tailTrace_2055630
  have hstable : (prefixWord ++ tailWord_2055630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055630).length < 2 ^ (prefixWord ++ tailWord_2055630).sum := by decide
  have hdescent : baseEnd_2055630 < baseStart_2055630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055643 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]
def baseStart_2055643 : Nat := 118140960795 + 2055643 * 2 ^ 59
def prefixEnd_2055643 : Nat := 4983230072969 + 3 ^ 40 * 2055643 * 2
def baseEnd_2055643 : Nat := 703688608700270680672517

theorem tailTrace_2055643 : CollatzResearch.WordTrace tailWord_2055643 prefixEnd_2055643 703688608700270680672517 := by
  unfold tailWord_2055643
  simp only [CollatzResearch.WordTrace]
  refine ⟨74975459691763961718931583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49983639794509307812621055 74975459691763961718931583)
  ·
    refine ⟨112463189537645942578397375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74975459691763961718931583 112463189537645942578397375)
    ·
      refine ⟨168694784306468913867596063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112463189537645942578397375 168694784306468913867596063)
      ·
        refine ⟨253042176459703370801394095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168694784306468913867596063 253042176459703370801394095)
        ·
          refine ⟨379563264689555056202091143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253042176459703370801394095 379563264689555056202091143)
          ·
            refine ⟨569344897034332584303136715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379563264689555056202091143 569344897034332584303136715)
            ·
              refine ⟨854017345551498876454705073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569344897034332584303136715 854017345551498876454705073)
              ·
                refine ⟨640513009163624157341028805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854017345551498876454705073 640513009163624157341028805)
                ·
                  refine ⟨120096189218179529501442901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640513009163624157341028805 120096189218179529501442901)
                  ·
                    refine ⟨703688608700270680672517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 120096189218179529501442901 703688608700270680672517)
                    ·
                      rfl

theorem cell22_2055643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_2055643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055643 prefixEnd_2055643 := by exact prefixLift 2055643
  have htrace : WordTrace (prefixWord ++ tailWord_2055643) baseStart_2055643 baseEnd_2055643 := by
    simpa [prefixWord, tailWord_2055643, baseEnd_2055643] using wordTrace_append hprefix tailTrace_2055643
  have hstable : (prefixWord ++ tailWord_2055643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055643).length < 2 ^ (prefixWord ++ tailWord_2055643).sum := by decide
  have hdescent : baseEnd_2055643 < baseStart_2055643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055647 : List Nat := [1, 1, 2, 3, 3, 1, 4, 2, 1, 4]
def baseStart_2055647 : Nat := 118140960795 + 2055647 * 2 ^ 59
def prefixEnd_2055647 : Nat := 4983230072969 + 3 ^ 40 * 2055647 * 2
def baseEnd_2055647 : Nat := 703689977982016003572505

theorem tailTrace_2055647 : CollatzResearch.WordTrace tailWord_2055647 prefixEnd_2055647 703689977982016003572505 := by
  unfold tailWord_2055647
  simp only [CollatzResearch.WordTrace]
  refine ⟨74975605583749470402077195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49983737055832980268051463 74975605583749470402077195)
  ·
    refine ⟨112463408375624205603115793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74975605583749470402077195 112463408375624205603115793)
    ·
      refine ⟨84347556281718154202336845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112463408375624205603115793 84347556281718154202336845)
      ·
        refine ⟨31630333605644307825876317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84347556281718154202336845 31630333605644307825876317)
        ·
          refine ⟨11861375102116615434703619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31630333605644307825876317 11861375102116615434703619)
          ·
            refine ⟨17792062653174923152055429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11861375102116615434703619 17792062653174923152055429)
            ·
              refine ⟨3336011747470298091010393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17792062653174923152055429 3336011747470298091010393)
              ·
                refine ⟨2502008810602723568257795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3336011747470298091010393 2502008810602723568257795)
                ·
                  refine ⟨3753013215904085352386693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2502008810602723568257795 3753013215904085352386693)
                  ·
                    refine ⟨703689977982016003572505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3753013215904085352386693 703689977982016003572505)
                    ·
                      rfl

theorem cell22_2055647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_2055647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055647 prefixEnd_2055647 := by exact prefixLift 2055647
  have htrace : WordTrace (prefixWord ++ tailWord_2055647) baseStart_2055647 baseEnd_2055647 := by
    simpa [prefixWord, tailWord_2055647, baseEnd_2055647] using wordTrace_append hprefix tailTrace_2055647
  have hstable : (prefixWord ++ tailWord_2055647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055647).length < 2 ^ (prefixWord ++ tailWord_2055647).sum := by decide
  have hdescent : baseEnd_2055647 < baseStart_2055647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055675 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 2, 4]
def baseStart_2055675 : Nat := 118140960795 + 2055675 * 2 ^ 59
def prefixEnd_2055675 : Nat := 4983230072969 + 3 ^ 40 * 2055675 * 2
def baseEnd_2055675 : Nat := 703699562954233263872419

theorem tailTrace_2055675 : CollatzResearch.WordTrace tailWord_2055675 prefixEnd_2055675 703699562954233263872419 := by
  unfold tailWord_2055675
  simp only [CollatzResearch.WordTrace]
  refine ⟨74976626827648031184096479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49984417885098687456064319 74976626827648031184096479)
  ·
    refine ⟨112464940241472046776144719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74976626827648031184096479 112464940241472046776144719)
    ·
      refine ⟨168697410362208070164217079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112464940241472046776144719 168697410362208070164217079)
      ·
        refine ⟨253046115543312105246325619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168697410362208070164217079 253046115543312105246325619)
        ·
          refine ⟨379569173314968157869488429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253046115543312105246325619 379569173314968157869488429)
          ·
            refine ⟨142338439993113059201058161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379569173314968157869488429 142338439993113059201058161)
            ·
              refine ⟨106753829994834794400793621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142338439993113059201058161 106753829994834794400793621)
              ·
                refine ⟨5004085781007880987537201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106753829994834794400793621 5004085781007880987537201)
                ·
                  refine ⟨3753064335755910740652901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5004085781007880987537201 3753064335755910740652901)
                  ·
                    refine ⟨703699562954233263872419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3753064335755910740652901 703699562954233263872419)
                    ·
                      rfl

theorem cell22_2055675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 4].length) (baseStart_2055675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055675 prefixEnd_2055675 := by exact prefixLift 2055675
  have htrace : WordTrace (prefixWord ++ tailWord_2055675) baseStart_2055675 baseEnd_2055675 := by
    simpa [prefixWord, tailWord_2055675, baseEnd_2055675] using wordTrace_append hprefix tailTrace_2055675
  have hstable : (prefixWord ++ tailWord_2055675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055675).length < 2 ^ (prefixWord ++ tailWord_2055675).sum := by decide
  have hdescent : baseEnd_2055675 < baseStart_2055675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055677 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_2055677 : Nat := 118140960795 + 2055677 * 2 ^ 59
def prefixEnd_2055677 : Nat := 4983230072969 + 3 ^ 40 * 2055677 * 2
def baseEnd_2055677 : Nat := 703700247595105925322413

theorem tailTrace_2055677 : CollatzResearch.WordTrace tailWord_2055677 prefixEnd_2055677 703700247595105925322413 := by
  unfold tailWord_2055677
  simp only [CollatzResearch.WordTrace]
  refine ⟨74976699773640785525669285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49984466515760523683779523 74976699773640785525669285)
  ·
    refine ⟨14058131207557647286062991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74976699773640785525669285 14058131207557647286062991)
    ·
      refine ⟨21087196811336470929094487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14058131207557647286062991 21087196811336470929094487)
      ·
        refine ⟨31630795217004706393641731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21087196811336470929094487 31630795217004706393641731)
        ·
          refine ⟨47446192825507059590462597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31630795217004706393641731 47446192825507059590462597)
          ·
            refine ⟨8896161154782573673211737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47446192825507059590462597 8896161154782573673211737)
            ·
              refine ⟨6672120866086930254908803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8896161154782573673211737 6672120866086930254908803)
              ·
                refine ⟨10008181299130395382363205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6672120866086930254908803 10008181299130395382363205)
                ·
                  refine ⟨1876533993586949134193101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10008181299130395382363205 1876533993586949134193101)
                  ·
                    refine ⟨703700247595105925322413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1876533993586949134193101 703700247595105925322413)
                    ·
                      rfl

theorem cell22_2055677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_2055677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055677 prefixEnd_2055677 := by exact prefixLift 2055677
  have htrace : WordTrace (prefixWord ++ tailWord_2055677) baseStart_2055677 baseEnd_2055677 := by
    simpa [prefixWord, tailWord_2055677, baseEnd_2055677] using wordTrace_append hprefix tailTrace_2055677
  have hstable : (prefixWord ++ tailWord_2055677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055677).length < 2 ^ (prefixWord ++ tailWord_2055677).sum := by decide
  have hdescent : baseEnd_2055677 < baseStart_2055677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055690 : List Nat := [3, 1, 2, 2, 2, 2, 1, 9]
def baseStart_2055690 : Nat := 118140960795 + 2055690 * 2 ^ 59
def prefixEnd_2055690 : Nat := 4983230072969 + 3 ^ 40 * 2055690 * 2
def baseEnd_2055690 : Nat := 78189410862308691638597

theorem tailTrace_2055690 : CollatzResearch.WordTrace tailWord_2055690 prefixEnd_2055690 78189410862308691638597 := by
  unfold tailWord_2055690
  simp only [CollatzResearch.WordTrace]
  refine ⟨18744293480648422186473131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49984782615062459163928349 18744293480648422186473131)
  ·
    refine ⟨28116440220972633279709697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18744293480648422186473131 28116440220972633279709697)
    ·
      refine ⟨21087330165729474959782273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28116440220972633279709697 21087330165729474959782273)
      ·
        refine ⟨15815497624297106219836705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21087330165729474959782273 15815497624297106219836705)
        ·
          refine ⟨11861623218222829664877529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15815497624297106219836705 11861623218222829664877529)
          ·
            refine ⟨8896217413667122248658147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11861623218222829664877529 8896217413667122248658147)
            ·
              refine ⟨13344326120500683372987221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8896217413667122248658147 13344326120500683372987221)
              ·
                refine ⟨78189410862308691638597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13344326120500683372987221 78189410862308691638597)
                ·
                  rfl

theorem cell22_2055690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_2055690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055690 prefixEnd_2055690 := by exact prefixLift 2055690
  have htrace : WordTrace (prefixWord ++ tailWord_2055690) baseStart_2055690 baseEnd_2055690 := by
    simpa [prefixWord, tailWord_2055690, baseEnd_2055690] using wordTrace_append hprefix tailTrace_2055690
  have hstable : (prefixWord ++ tailWord_2055690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055690).length < 2 ^ (prefixWord ++ tailWord_2055690).sum := by decide
  have hdescent : baseEnd_2055690 < baseStart_2055690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055831 : List Nat := [1, 1, 3, 3, 2, 4, 1, 3, 4]
def baseStart_2055831 : Nat := 118140960795 + 2055831 * 2 ^ 59
def prefixEnd_2055831 : Nat := 4983230072969 + 3 ^ 40 * 2055831 * 2
def baseEnd_2055831 : Nat := 234584321647433618990647

theorem tailTrace_2055831 : CollatzResearch.WordTrace tailWord_2055831 prefixEnd_2055831 234584321647433618990647 := by
  unfold tailWord_2055831
  simp only [CollatzResearch.WordTrace]
  refine ⟨74982316615082869826775347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49988211076721913217850231 74982316615082869826775347)
  ·
    refine ⟨112473474922624304740163021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74982316615082869826775347 112473474922624304740163021)
    ·
      refine ⟨42177553095984114277561133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112473474922624304740163021 42177553095984114277561133)
      ·
        refine ⟨15816582410994042854085425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42177553095984114277561133 15816582410994042854085425)
        ·
          refine ⟨11862436808245532140564069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15816582410994042854085425 11862436808245532140564069)
          ·
            refine ⟨2224206901546037276355763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11862436808245532140564069 2224206901546037276355763)
            ·
              refine ⟨3336310352319055914533645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2224206901546037276355763 3336310352319055914533645)
              ·
                refine ⟨1251116382119645967950117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3336310352319055914533645 1251116382119645967950117)
                ·
                  refine ⟨234584321647433618990647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1251116382119645967950117 234584321647433618990647)
                  ·
                    rfl

theorem cell22_2055831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 4].length) (baseStart_2055831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055831 prefixEnd_2055831 := by exact prefixLift 2055831
  have htrace : WordTrace (prefixWord ++ tailWord_2055831) baseStart_2055831 baseEnd_2055831 := by
    simpa [prefixWord, tailWord_2055831, baseEnd_2055831] using wordTrace_append hprefix tailTrace_2055831
  have hstable : (prefixWord ++ tailWord_2055831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055831).length < 2 ^ (prefixWord ++ tailWord_2055831).sum := by decide
  have hdescent : baseEnd_2055831 < baseStart_2055831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055844 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_2055844 : Nat := 118140960795 + 2055844 * 2 ^ 59
def prefixEnd_2055844 : Nat := 4983230072969 + 3 ^ 40 * 2055844 * 2
def baseEnd_2055844 : Nat := 703757415107973156396901

theorem tailTrace_2055844 : CollatzResearch.WordTrace tailWord_2055844 prefixEnd_2055844 703757415107973156396901 := by
  unfold tailWord_2055844
  simp only [CollatzResearch.WordTrace]
  refine ⟨37491395382017886523499293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49988527176023848697999057 37491395382017886523499293)
  ·
    refine ⟨14059273268256707446312235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37491395382017886523499293 14059273268256707446312235)
    ·
      refine ⟨21088909902385061169468353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14059273268256707446312235 21088909902385061169468353)
      ·
        refine ⟨15816682426788795877101265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21088909902385061169468353 15816682426788795877101265)
        ·
          refine ⟨11862511820091596907825949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15816682426788795877101265 11862511820091596907825949)
          ·
            refine ⟨4448441932534348840434731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11862511820091596907825949 4448441932534348840434731)
            ·
              refine ⟨6672662898801523260652097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448441932534348840434731 6672662898801523260652097)
              ·
                refine ⟨5004497174101142445489073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6672662898801523260652097 5004497174101142445489073)
                ·
                  refine ⟨3753372880575856834116805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5004497174101142445489073 3753372880575856834116805)
                  ·
                    refine ⟨703757415107973156396901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3753372880575856834116805 703757415107973156396901)
                    ·
                      rfl

theorem cell22_2055844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_2055844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055844 prefixEnd_2055844 := by exact prefixLift 2055844
  have htrace : WordTrace (prefixWord ++ tailWord_2055844) baseStart_2055844 baseEnd_2055844 := by
    simpa [prefixWord, tailWord_2055844, baseEnd_2055844] using wordTrace_append hprefix tailTrace_2055844
  have hstable : (prefixWord ++ tailWord_2055844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055844).length < 2 ^ (prefixWord ++ tailWord_2055844).sum := by decide
  have hdescent : baseEnd_2055844 < baseStart_2055844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055863 : List Nat := [1, 1, 3, 1, 5, 3, 2, 1, 2, 3]
def baseStart_2055863 : Nat := 118140960795 + 2055863 * 2 ^ 59
def prefixEnd_2055863 : Nat := 4983230072969 + 3 ^ 40 * 2055863 * 2
def baseEnd_2055863 : Nat := 703763919196263440171843

theorem tailTrace_2055863 : CollatzResearch.WordTrace tailWord_2055863 prefixEnd_2055863 703763919196263440171843 := by
  unfold tailWord_2055863
  simp only [CollatzResearch.WordTrace]
  refine ⟨74983483750966939291940243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49988989167311292861293495 74983483750966939291940243)
  ·
    refine ⟨112475225626450408937910365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74983483750966939291940243 112475225626450408937910365)
    ·
      refine ⟨42178209609918903351716387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112475225626450408937910365 42178209609918903351716387)
      ·
        refine ⟨63267314414878355027574581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42178209609918903351716387 63267314414878355027574581)
        ·
          refine ⟨5931310726394845783835117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63267314414878355027574581 5931310726394845783835117)
          ·
            refine ⟨2224241522398067168938169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5931310726394845783835117 2224241522398067168938169)
            ·
              refine ⟨1668181141798550376703627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2224241522398067168938169 1668181141798550376703627)
              ·
                refine ⟨2502271712697825565055441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668181141798550376703627 2502271712697825565055441)
                ·
                  refine ⟨1876703784523369173791581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2502271712697825565055441 1876703784523369173791581)
                  ·
                    refine ⟨703763919196263440171843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1876703784523369173791581 703763919196263440171843)
                    ·
                      rfl

theorem cell22_2055863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_2055863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055863 prefixEnd_2055863 := by exact prefixLift 2055863
  have htrace : WordTrace (prefixWord ++ tailWord_2055863) baseStart_2055863 baseEnd_2055863 := by
    simpa [prefixWord, tailWord_2055863, baseEnd_2055863] using wordTrace_append hprefix tailTrace_2055863
  have hstable : (prefixWord ++ tailWord_2055863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055863).length < 2 ^ (prefixWord ++ tailWord_2055863).sum := by decide
  have hdescent : baseEnd_2055863 < baseStart_2055863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055878 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2055878 : Nat := 118140960795 + 2055878 * 2 ^ 59
def prefixEnd_2055878 : Nat := 4983230072969 + 3 ^ 40 * 2055878 * 2
def baseEnd_2055878 : Nat := 703769054002808401046797

theorem tailTrace_2055878 : CollatzResearch.WordTrace tailWord_2055878 prefixEnd_2055878 703769054002808401046797 := by
  unfold tailWord_2055878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2343250963934768651679259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49989353897275064569157525 2343250963934768651679259)
  ·
    refine ⟨3514876445902152977518889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2343250963934768651679259 3514876445902152977518889)
    ·
      refine ⟨2636157334426614733139167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3514876445902152977518889 2636157334426614733139167)
      ·
        refine ⟨3954236001639922099708751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636157334426614733139167 3954236001639922099708751)
        ·
          refine ⟨5931354002459883149563127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3954236001639922099708751 5931354002459883149563127)
          ·
            refine ⟨8897031003689824724344691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5931354002459883149563127 8897031003689824724344691)
            ·
              refine ⟨13345546505534737086517037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8897031003689824724344691 13345546505534737086517037)
              ·
                refine ⟨5004579939575526407443889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13345546505534737086517037 5004579939575526407443889)
                ·
                  refine ⟨3753434954681644805582917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5004579939575526407443889 3753434954681644805582917)
                  ·
                    refine ⟨703769054002808401046797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3753434954681644805582917 703769054002808401046797)
                    ·
                      rfl

theorem cell22_2055878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2055878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055878 prefixEnd_2055878 := by exact prefixLift 2055878
  have htrace : WordTrace (prefixWord ++ tailWord_2055878) baseStart_2055878 baseEnd_2055878 := by
    simpa [prefixWord, tailWord_2055878, baseEnd_2055878] using wordTrace_append hprefix tailTrace_2055878
  have hstable : (prefixWord ++ tailWord_2055878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055878).length < 2 ^ (prefixWord ++ tailWord_2055878).sum := by decide
  have hdescent : baseEnd_2055878 < baseStart_2055878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055994 : List Nat := [3, 1, 1, 1, 5, 2, 1, 8]
def baseStart_2055994 : Nat := 118140960795 + 2055994 * 2 ^ 59
def prefixEnd_2055994 : Nat := 4983230072969 + 3 ^ 40 * 2055994 * 2
def baseEnd_2055994 : Nat := 78200973685935862794049

theorem tailTrace_2055994 : CollatzResearch.WordTrace tailWord_2055994 prefixEnd_2055994 78200973685935862794049 := by
  unfold tailWord_2055994
  simp only [CollatzResearch.WordTrace]
  refine ⟨18747065428373087166239759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49992174475661565776639357 18747065428373087166239759)
  ·
    refine ⟨28120598142559630749359639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18747065428373087166239759 28120598142559630749359639)
    ·
      refine ⟨42180897213839446124039459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28120598142559630749359639 42180897213839446124039459)
      ·
        refine ⟨63271345820759169186059189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42180897213839446124039459 63271345820759169186059189)
        ·
          refine ⟨5931688670696172111193049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63271345820759169186059189 5931688670696172111193049)
          ·
            refine ⟨4448766503022129083394787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5931688670696172111193049 4448766503022129083394787)
            ·
              refine ⟨6673149754533193625092181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448766503022129083394787 6673149754533193625092181)
              ·
                refine ⟨78200973685935862794049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6673149754533193625092181 78200973685935862794049)
                ·
                  rfl

theorem cell22_2055994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_2055994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2055994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2055994 prefixEnd_2055994 := by exact prefixLift 2055994
  have htrace : WordTrace (prefixWord ++ tailWord_2055994) baseStart_2055994 baseEnd_2055994 := by
    simpa [prefixWord, tailWord_2055994, baseEnd_2055994] using wordTrace_append hprefix tailTrace_2055994
  have hstable : (prefixWord ++ tailWord_2055994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055994).length < 2 ^ (prefixWord ++ tailWord_2055994).sum := by decide
  have hdescent : baseEnd_2055994 < baseStart_2055994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056013 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2056013 : Nat := 118140960795 + 2056013 * 2 ^ 59
def prefixEnd_2056013 : Nat := 4983230072969 + 3 ^ 40 * 2056013 * 2
def baseEnd_2056013 : Nat := 703815267261713048921383

theorem tailTrace_2056013 : CollatzResearch.WordTrace tailWord_2056013 prefixEnd_2056013 703815267261713048921383 := by
  unfold tailWord_2056013
  simp only [CollatzResearch.WordTrace]
  refine ⟨74988954700423514909900693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49992636466949009939933795 74988954700423514909900693)
  ·
    refine ⟨3515107251582352261401595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74988954700423514909900693 3515107251582352261401595)
    ·
      refine ⟨5272660877373528392102393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3515107251582352261401595 5272660877373528392102393)
      ·
        refine ⟨3954495658030146294076795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5272660877373528392102393 3954495658030146294076795)
        ·
          refine ⟨5931743487045219441115193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3954495658030146294076795 5931743487045219441115193)
          ·
            refine ⟨4448807615283914580836395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5931743487045219441115193 4448807615283914580836395)
            ·
              refine ⟨6673211422925871871254593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448807615283914580836395 6673211422925871871254593)
              ·
                refine ⟨5004908567194403903440945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6673211422925871871254593 5004908567194403903440945)
                ·
                  refine ⟨3753681425395802927580709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5004908567194403903440945 3753681425395802927580709)
                  ·
                    refine ⟨703815267261713048921383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3753681425395802927580709 703815267261713048921383)
                    ·
                      rfl

theorem cell22_2056013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2056013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056013 prefixEnd_2056013 := by exact prefixLift 2056013
  have htrace : WordTrace (prefixWord ++ tailWord_2056013) baseStart_2056013 baseEnd_2056013 := by
    simpa [prefixWord, tailWord_2056013, baseEnd_2056013] using wordTrace_append hprefix tailTrace_2056013
  have hstable : (prefixWord ++ tailWord_2056013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056013).length < 2 ^ (prefixWord ++ tailWord_2056013).sum := by decide
  have hdescent : baseEnd_2056013 < baseStart_2056013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056088 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 2, 5]
def baseStart_2056088 : Nat := 118140960795 + 2056088 * 2 ^ 59
def prefixEnd_2056088 : Nat := 4983230072969 + 3 ^ 40 * 2056088 * 2
def baseEnd_2056088 : Nat := 703840941294437853296153

theorem tailTrace_2056088 : CollatzResearch.WordTrace tailWord_2056088 prefixEnd_2056088 703840941294437853296153 := by
  unfold tailWord_2056088
  simp only [CollatzResearch.WordTrace]
  refine ⟨37495845087575901359440459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49994460116767868479253945 37495845087575901359440459)
  ·
    refine ⟨56243767631363852039160689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37495845087575901359440459 56243767631363852039160689)
    ·
      refine ⟨42182825723522889029370517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56243767631363852039160689 42182825723522889029370517)
      ·
        refine ⟨1977319955790135423251743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42182825723522889029370517 1977319955790135423251743)
        ·
          refine ⟨2965979933685203134877615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1977319955790135423251743 2965979933685203134877615)
          ·
            refine ⟨4448969900527804702316423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965979933685203134877615 4448969900527804702316423)
            ·
              refine ⟨6673454850791707053474635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448969900527804702316423 6673454850791707053474635)
              ·
                refine ⟨10010182276187560580211953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673454850791707053474635 10010182276187560580211953)
                ·
                  refine ⟨7507636707140670435158965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10010182276187560580211953 7507636707140670435158965)
                  ·
                    refine ⟨703840941294437853296153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7507636707140670435158965 703840941294437853296153)
                    ·
                      rfl

theorem cell22_2056088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_2056088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056088 prefixEnd_2056088 := by exact prefixLift 2056088
  have htrace : WordTrace (prefixWord ++ tailWord_2056088) baseStart_2056088 baseEnd_2056088 := by
    simpa [prefixWord, tailWord_2056088, baseEnd_2056088] using wordTrace_append hprefix tailTrace_2056088
  have hstable : (prefixWord ++ tailWord_2056088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056088).length < 2 ^ (prefixWord ++ tailWord_2056088).sum := by decide
  have hdescent : baseEnd_2056088 < baseStart_2056088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056163 : List Nat := [1, 1, 1, 6, 1, 4, 2, 6]
def baseStart_2056163 : Nat := 118140960795 + 2056163 * 2 ^ 59
def prefixEnd_2056163 : Nat := 4983230072969 + 3 ^ 40 * 2056163 * 2
def baseEnd_2056163 : Nat := 78207401703018073074547

theorem tailTrace_2056163 : CollatzResearch.WordTrace tailWord_2056163 prefixEnd_2056163 78207401703018073074547 := by
  unfold tailWord_2056163
  simp only [CollatzResearch.WordTrace]
  refine ⟨74994425649880090527861143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49996283766586727018574095 74994425649880090527861143)
  ·
    refine ⟨112491638474820135791791715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74994425649880090527861143 112491638474820135791791715)
    ·
      refine ⟨168737457712230203687687573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112491638474820135791791715 168737457712230203687687573)
      ·
        refine ⟨7909568330260790797860355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 168737457712230203687687573 7909568330260790797860355)
        ·
          refine ⟨11864352495391186196790533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7909568330260790797860355 11864352495391186196790533)
          ·
            refine ⟨2224566092885847411898225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11864352495391186196790533 2224566092885847411898225)
            ·
              refine ⟨1668424569664385558923669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2224566092885847411898225 1668424569664385558923669)
              ·
                refine ⟨78207401703018073074547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1668424569664385558923669 78207401703018073074547)
                ·
                  rfl

theorem cell22_2056163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 6].length) (baseStart_2056163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056163 prefixEnd_2056163 := by exact prefixLift 2056163
  have htrace : WordTrace (prefixWord ++ tailWord_2056163) baseStart_2056163 baseEnd_2056163 := by
    simpa [prefixWord, tailWord_2056163, baseEnd_2056163] using wordTrace_append hprefix tailTrace_2056163
  have hstable : (prefixWord ++ tailWord_2056163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056163).length < 2 ^ (prefixWord ++ tailWord_2056163).sum := by decide
  have hdescent : baseEnd_2056163 < baseStart_2056163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056206 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_2056206 : Nat := 118140960795 + 2056206 * 2 ^ 59
def prefixEnd_2056206 : Nat := 4983230072969 + 3 ^ 40 * 2056206 * 2
def baseEnd_2056206 : Nat := 703881335105924878845791

theorem tailTrace_2056206 : CollatzResearch.WordTrace tailWord_2056206 prefixEnd_2056206 703881335105924878845791 := by
  unfold tailWord_2056206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9374499248590538608959559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49997329325816205914450981 9374499248590538608959559)
  ·
    refine ⟨14061748872885807913439339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9374499248590538608959559 14061748872885807913439339)
    ·
      refine ⟨21092623309328711870159009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14061748872885807913439339 21092623309328711870159009)
      ·
        refine ⟨15819467481996533902619257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21092623309328711870159009 15819467481996533902619257)
        ·
          refine ⟨11864600611497400426964443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15819467481996533902619257 11864600611497400426964443)
          ·
            refine ⟨17796900917246100640446665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11864600611497400426964443 17796900917246100640446665)
            ·
              refine ⟨13347675687934575480334999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17796900917246100640446665 13347675687934575480334999)
              ·
                refine ⟨20021513531901863220502499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13347675687934575480334999 20021513531901863220502499)
                ·
                  refine ⟨30032270297852794830753749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20021513531901863220502499 30032270297852794830753749)
                  ·
                    refine ⟨703881335105924878845791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30032270297852794830753749 703881335105924878845791)
                    ·
                      rfl

theorem cell22_2056206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_2056206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056206 prefixEnd_2056206 := by exact prefixLift 2056206
  have htrace : WordTrace (prefixWord ++ tailWord_2056206) baseStart_2056206 baseEnd_2056206 := by
    simpa [prefixWord, tailWord_2056206, baseEnd_2056206] using wordTrace_append hprefix tailTrace_2056206
  have hstable : (prefixWord ++ tailWord_2056206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056206).length < 2 ^ (prefixWord ++ tailWord_2056206).sum := by decide
  have hdescent : baseEnd_2056206 < baseStart_2056206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056266 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_2056266 : Nat := 118140960795 + 2056266 * 2 ^ 59
def prefixEnd_2056266 : Nat := 4983230072969 + 3 ^ 40 * 2056266 * 2
def baseEnd_2056266 : Nat := 703901874332104722345607

theorem tailTrace_2056266 : CollatzResearch.WordTrace tailWord_2056266 prefixEnd_2056266 703901874332104722345607 := by
  unfold tailWord_2056266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18749545592126734779715163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49998788245671292745907101 18749545592126734779715163)
  ·
    refine ⟨28124318388190102169572745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18749545592126734779715163 28124318388190102169572745)
    ·
      refine ⟨21093238791142576627179559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28124318388190102169572745 21093238791142576627179559)
      ·
        refine ⟨31639858186713864940769339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21093238791142576627179559 31639858186713864940769339)
        ·
          refine ⟨47459787280070797411154009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31639858186713864940769339 47459787280070797411154009)
          ·
            refine ⟨35594840460053098058365507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47459787280070797411154009 35594840460053098058365507)
            ·
              refine ⟨53392260690079647087548261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35594840460053098058365507 53392260690079647087548261)
              ·
                refine ⟨10011048879389933828915299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53392260690079647087548261 10011048879389933828915299)
                ·
                  refine ⟨15016573319084900743372949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10011048879389933828915299 15016573319084900743372949)
                  ·
                    refine ⟨703901874332104722345607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15016573319084900743372949 703901874332104722345607)
                    ·
                      rfl

theorem cell22_2056266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_2056266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056266 prefixEnd_2056266 := by exact prefixLift 2056266
  have htrace : WordTrace (prefixWord ++ tailWord_2056266) baseStart_2056266 baseEnd_2056266 := by
    simpa [prefixWord, tailWord_2056266, baseEnd_2056266] using wordTrace_append hprefix tailTrace_2056266
  have hstable : (prefixWord ++ tailWord_2056266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056266).length < 2 ^ (prefixWord ++ tailWord_2056266).sum := by decide
  have hdescent : baseEnd_2056266 < baseStart_2056266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056285 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2056285 : Nat := 118140960795 + 2056285 * 2 ^ 59
def prefixEnd_2056285 : Nat := 4983230072969 + 3 ^ 40 * 2056285 * 2
def baseEnd_2056285 : Nat := 703908378420395006120549

theorem tailTrace_2056285 : CollatzResearch.WordTrace tailWord_2056285 prefixEnd_2056285 703908378420395006120549 := by
  unfold tailWord_2056285
  simp only [CollatzResearch.WordTrace]
  refine ⟨74998875355438105363802309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49999250236958736909201539 74998875355438105363802309)
  ·
    refine ⟨14062289129144644755712933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74998875355438105363802309 14062289129144644755712933)
    ·
      refine ⟨2636679211714620891696175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14062289129144644755712933 2636679211714620891696175)
      ·
        refine ⟨3955018817571931337544263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636679211714620891696175 3955018817571931337544263)
        ·
          refine ⟨5932528226357897006316395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3955018817571931337544263 5932528226357897006316395)
          ·
            refine ⟨8898792339536845509474593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5932528226357897006316395 8898792339536845509474593)
            ·
              refine ⟨6674094254652634132105945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8898792339536845509474593 6674094254652634132105945)
              ·
                refine ⟨5005570690989475599079459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6674094254652634132105945 5005570690989475599079459)
                ·
                  refine ⟨7508356036484213398619189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005570690989475599079459 7508356036484213398619189)
                  ·
                    refine ⟨703908378420395006120549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7508356036484213398619189 703908378420395006120549)
                    ·
                      rfl

theorem cell22_2056285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2056285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056285 prefixEnd_2056285 := by exact prefixLift 2056285
  have htrace : WordTrace (prefixWord ++ tailWord_2056285) baseStart_2056285 baseEnd_2056285 := by
    simpa [prefixWord, tailWord_2056285, baseEnd_2056285] using wordTrace_append hprefix tailTrace_2056285
  have hstable : (prefixWord ++ tailWord_2056285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056285).length < 2 ^ (prefixWord ++ tailWord_2056285).sum := by decide
  have hdescent : baseEnd_2056285 < baseStart_2056285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056298 : List Nat := [3, 1, 3, 2, 3, 1, 9]
def baseStart_2056298 : Nat := 118140960795 + 2056298 * 2 ^ 59
def prefixEnd_2056298 : Nat := 4983230072969 + 3 ^ 40 * 2056298 * 2
def baseEnd_2056298 : Nat := 26070845503187677983167

theorem tailTrace_2056298 : CollatzResearch.WordTrace tailWord_2056298 prefixEnd_2056298 26070845503187677983167 := by
  unfold tailWord_2056298
  simp only [CollatzResearch.WordTrace]
  refine ⟨18749837376097752146006387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49999566336260672389350365 18749837376097752146006387)
  ·
    refine ⟨28124756064146628219009581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18749837376097752146006387 28124756064146628219009581)
    ·
      refine ⟨10546783524054985582128593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28124756064146628219009581 10546783524054985582128593)
      ·
        refine ⟨7910087643041239186596445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10546783524054985582128593 7910087643041239186596445)
        ·
          refine ⟨2966282866140464694973667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7910087643041239186596445 2966282866140464694973667)
          ·
            refine ⟨4449424299210697042460501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2966282866140464694973667 4449424299210697042460501)
            ·
              refine ⟨26070845503187677983167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4449424299210697042460501 26070845503187677983167)
              ·
                rfl

theorem cell22_2056298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 9].length) (baseStart_2056298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056298 prefixEnd_2056298 := by exact prefixLift 2056298
  have htrace : WordTrace (prefixWord ++ tailWord_2056298) baseStart_2056298 baseEnd_2056298 := by
    simpa [prefixWord, tailWord_2056298, baseEnd_2056298] using wordTrace_append hprefix tailTrace_2056298
  have hstable : (prefixWord ++ tailWord_2056298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056298).length < 2 ^ (prefixWord ++ tailWord_2056298).sum := by decide
  have hdescent : baseEnd_2056298 < baseStart_2056298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056330 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 3, 3]
def baseStart_2056330 : Nat := 118140960795 + 2056330 * 2 ^ 59
def prefixEnd_2056330 : Nat := 4983230072969 + 3 ^ 40 * 2056330 * 2
def baseEnd_2056330 : Nat := 703923782840029888745411

theorem tailTrace_2056330 : CollatzResearch.WordTrace tailWord_2056330 prefixEnd_2056330 703923782840029888745411 := by
  unfold tailWord_2056330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18750129160068769512297611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50000344426850052032793629 18750129160068769512297611)
  ·
    refine ⟨28125193740103154268446417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18750129160068769512297611 28125193740103154268446417)
    ·
      refine ⟨21093895305077365701334813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28125193740103154268446417 21093895305077365701334813)
      ·
        refine ⟨7910210739404012138000555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21093895305077365701334813 7910210739404012138000555)
        ·
          refine ⟨11865316109106018207000833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7910210739404012138000555 11865316109106018207000833)
          ·
            refine ⟨8898987081829513655250625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11865316109106018207000833 8898987081829513655250625)
            ·
              refine ⟨6674240311372135241437969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8898987081829513655250625 6674240311372135241437969)
              ·
                refine ⟨5005680233529101431078477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6674240311372135241437969 5005680233529101431078477)
                ·
                  refine ⟨1877130087573413036654429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5005680233529101431078477 1877130087573413036654429)
                  ·
                    refine ⟨703923782840029888745411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1877130087573413036654429 703923782840029888745411)
                    ·
                      rfl

theorem cell22_2056330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_2056330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056330 prefixEnd_2056330 := by exact prefixLift 2056330
  have htrace : WordTrace (prefixWord ++ tailWord_2056330) baseStart_2056330 baseEnd_2056330 := by
    simpa [prefixWord, tailWord_2056330, baseEnd_2056330] using wordTrace_append hprefix tailTrace_2056330
  have hstable : (prefixWord ++ tailWord_2056330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056330).length < 2 ^ (prefixWord ++ tailWord_2056330).sum := by decide
  have hdescent : baseEnd_2056330 < baseStart_2056330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056433 : List Nat := [1, 2, 2, 2, 2, 1, 5, 7]
def baseStart_2056433 : Nat := 118140960795 + 2056433 * 2 ^ 59
def prefixEnd_2056433 : Nat := 4983230072969 + 3 ^ 40 * 2056433 * 2
def baseEnd_2056433 : Nat := 78217671316107994824455

theorem tailTrace_2056433 : CollatzResearch.WordTrace tailWord_2056433 prefixEnd_2056433 78217671316107994824455 := by
  unfold tailWord_2056433
  simp only [CollatzResearch.WordTrace]
  refine ⟨75004273358901926640189953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50002848905934617760126635 75004273358901926640189953)
  ·
    refine ⟨56253205019176444980142465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75004273358901926640189953 56253205019176444980142465)
    ·
      refine ⟨42189903764382333735106849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56253205019176444980142465 42189903764382333735106849)
      ·
        refine ⟨31642427823286750301330137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42189903764382333735106849 31642427823286750301330137)
        ·
          refine ⟨23731820867465062725997603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31642427823286750301330137 23731820867465062725997603)
          ·
            refine ⟨35597731301197594088996405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23731820867465062725997603 35597731301197594088996405)
            ·
              refine ⟨3337287309487274445843413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35597731301197594088996405 3337287309487274445843413)
              ·
                refine ⟨78217671316107994824455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3337287309487274445843413 78217671316107994824455)
                ·
                  rfl

theorem cell22_2056433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 7].length) (baseStart_2056433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056433 prefixEnd_2056433 := by exact prefixLift 2056433
  have htrace : WordTrace (prefixWord ++ tailWord_2056433) baseStart_2056433 baseEnd_2056433 := by
    simpa [prefixWord, tailWord_2056433, baseEnd_2056433] using wordTrace_append hprefix tailTrace_2056433
  have hstable : (prefixWord ++ tailWord_2056433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056433).length < 2 ^ (prefixWord ++ tailWord_2056433).sum := by decide
  have hdescent : baseEnd_2056433 < baseStart_2056433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056482 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_2056482 : Nat := 118140960795 + 2056482 * 2 ^ 59
def prefixEnd_2056482 : Nat := 4983230072969 + 3 ^ 40 * 2056482 * 2
def baseEnd_2056482 : Nat := 703975815546352158944945

theorem tailTrace_2056482 : CollatzResearch.WordTrace tailWord_2056482 prefixEnd_2056482 703975815546352158944945 := by
  unfold tailWord_2056482
  simp only [CollatzResearch.WordTrace]
  refine ⟨18751515133931102002180925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50004040357149605339149133 18751515133931102002180925)
  ·
    refine ⟨7031818175224163250817847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18751515133931102002180925 7031818175224163250817847)
    ·
      refine ⟨10547727262836244876226771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7031818175224163250817847 10547727262836244876226771)
      ·
        refine ⟨15821590894254367314340157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10547727262836244876226771 15821590894254367314340157)
        ·
          refine ⟨5933096585345387742877559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15821590894254367314340157 5933096585345387742877559)
          ·
            refine ⟨8899644878018081614316339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933096585345387742877559 8899644878018081614316339)
            ·
              refine ⟨13349467317027122421474509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8899644878018081614316339 13349467317027122421474509)
              ·
                refine ⟨5006050243885170908052941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13349467317027122421474509 5006050243885170908052941)
                ·
                  refine ⟨1877268841456939090519853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5006050243885170908052941 1877268841456939090519853)
                  ·
                    refine ⟨703975815546352158944945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1877268841456939090519853 703975815546352158944945)
                    ·
                      rfl

theorem cell22_2056482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_2056482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056482 prefixEnd_2056482 := by exact prefixLift 2056482
  have htrace : WordTrace (prefixWord ++ tailWord_2056482) baseStart_2056482 baseEnd_2056482 := by
    simpa [prefixWord, tailWord_2056482, baseEnd_2056482] using wordTrace_append hprefix tailTrace_2056482
  have hstable : (prefixWord ++ tailWord_2056482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056482).length < 2 ^ (prefixWord ++ tailWord_2056482).sum := by decide
  have hdescent : baseEnd_2056482 < baseStart_2056482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056602 : List Nat := [3, 1, 1, 4, 1, 4, 1, 7]
def baseStart_2056602 : Nat := 118140960795 + 2056602 * 2 ^ 59
def prefixEnd_2056602 : Nat := 4983230072969 + 3 ^ 40 * 2056602 * 2
def baseEnd_2056602 : Nat := 78224099333190205104953

theorem tailTrace_2056602 : CollatzResearch.WordTrace tailWord_2056602 prefixEnd_2056602 78224099333190205104953 := by
  unfold tailWord_2056602
  simp only [CollatzResearch.WordTrace]
  refine ⟨18752609323822417125773015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50006958196859779002061373 18752609323822417125773015)
  ·
    refine ⟨28128913985733625688659523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18752609323822417125773015 28128913985733625688659523)
    ·
      refine ⟨42193370978600438532989285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28128913985733625688659523 42193370978600438532989285)
      ·
        refine ⟨7911257058487582224935491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42193370978600438532989285 7911257058487582224935491)
        ·
          refine ⟨11866885587731373337403237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7911257058487582224935491 11866885587731373337403237)
          ·
            refine ⟨2225041047699632500763107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11866885587731373337403237 2225041047699632500763107)
            ·
              refine ⟨3337561571549448751144661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225041047699632500763107 3337561571549448751144661)
              ·
                refine ⟨78224099333190205104953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3337561571549448751144661 78224099333190205104953)
                ·
                  rfl

theorem cell22_2056602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_2056602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056602 prefixEnd_2056602 := by exact prefixLift 2056602
  have htrace : WordTrace (prefixWord ++ tailWord_2056602) baseStart_2056602 baseEnd_2056602 := by
    simpa [prefixWord, tailWord_2056602, baseEnd_2056602] using wordTrace_append hprefix tailTrace_2056602
  have hstable : (prefixWord ++ tailWord_2056602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056602).length < 2 ^ (prefixWord ++ tailWord_2056602).sum := by decide
  have hdescent : baseEnd_2056602 < baseStart_2056602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056606 : List Nat := [4, 3, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_2056606 : Nat := 118140960795 + 2056606 * 2 ^ 59
def prefixEnd_2056606 : Nat := 4983230072969 + 3 ^ 40 * 2056606 * 2
def baseEnd_2056606 : Nat := 704018263280457168844565

theorem tailTrace_2056606 : CollatzResearch.WordTrace tailWord_2056606 prefixEnd_2056606 704018263280457168844565 := by
  unfold tailWord_2056606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9376322898409397148279709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50007055458183451457491781 9376322898409397148279709)
  ·
    refine ⟨3516121086903523930604891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9376322898409397148279709 3516121086903523930604891)
    ·
      refine ⟨5274181630355285895907337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3516121086903523930604891 5274181630355285895907337)
      ·
        refine ⟨3955636222766464421930503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5274181630355285895907337 3955636222766464421930503)
        ·
          refine ⟨5933454334149696632895755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3955636222766464421930503 5933454334149696632895755)
          ·
            refine ⟨8900181501224544949343633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933454334149696632895755 8900181501224544949343633)
            ·
              refine ⟨6675136125918408712007725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8900181501224544949343633 6675136125918408712007725)
              ·
                refine ⟨2503176047219403267002897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6675136125918408712007725 2503176047219403267002897)
                ·
                  refine ⟨1877382035414552450252173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2503176047219403267002897 1877382035414552450252173)
                  ·
                    refine ⟨704018263280457168844565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1877382035414552450252173 704018263280457168844565)
                    ·
                      rfl

theorem cell22_2056606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_2056606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056606 prefixEnd_2056606 := by exact prefixLift 2056606
  have htrace : WordTrace (prefixWord ++ tailWord_2056606) baseStart_2056606 baseEnd_2056606 := by
    simpa [prefixWord, tailWord_2056606, baseEnd_2056606] using wordTrace_append hprefix tailTrace_2056606
  have hstable : (prefixWord ++ tailWord_2056606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056606).length < 2 ^ (prefixWord ++ tailWord_2056606).sum := by decide
  have hdescent : baseEnd_2056606 < baseStart_2056606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056621 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_2056621 : Nat := 118140960795 + 2056621 * 2 ^ 59
def prefixEnd_2056621 : Nat := 4983230072969 + 3 ^ 40 * 2056621 * 2
def baseEnd_2056621 : Nat := 704023398087002129719519

theorem tailTrace_2056621 : CollatzResearch.WordTrace tailWord_2056621 prefixEnd_2056621 704023398087002129719519 := by
  unfold tailWord_2056621
  simp only [CollatzResearch.WordTrace]
  refine ⟨75011130282220834748033717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50007420188147223165355811 75011130282220834748033717)
  ·
    refine ⟨7032293463958203257628161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75011130282220834748033717 7032293463958203257628161)
    ·
      refine ⟨5274220097968652443221121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7032293463958203257628161 5274220097968652443221121)
      ·
        refine ⟨3955665073476489332415841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5274220097968652443221121 3955665073476489332415841)
        ·
          refine ⟨2966748805107366999311881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3955665073476489332415841 2966748805107366999311881)
          ·
            refine ⟨2225061603830525249483911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2966748805107366999311881 2225061603830525249483911)
            ·
              refine ⟨3337592405745787874225867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225061603830525249483911 3337592405745787874225867)
              ·
                refine ⟨5006388608618681811338801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337592405745787874225867 5006388608618681811338801)
                ·
                  refine ⟨3754791456464011358504101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5006388608618681811338801 3754791456464011358504101)
                  ·
                    refine ⟨704023398087002129719519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3754791456464011358504101 704023398087002129719519)
                    ·
                      rfl

theorem cell22_2056621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_2056621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056621 prefixEnd_2056621 := by exact prefixLift 2056621
  have htrace : WordTrace (prefixWord ++ tailWord_2056621) baseStart_2056621 baseEnd_2056621 := by
    simpa [prefixWord, tailWord_2056621, baseEnd_2056621] using wordTrace_append hprefix tailTrace_2056621
  have hstable : (prefixWord ++ tailWord_2056621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056621).length < 2 ^ (prefixWord ++ tailWord_2056621).sum := by decide
  have hdescent : baseEnd_2056621 < baseStart_2056621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056647 : List Nat := [1, 1, 4, 1, 1, 4, 3, 2, 5]
def baseStart_2056647 : Nat := 118140960795 + 2056647 * 2 ^ 59
def prefixEnd_2056647 : Nat := 4983230072969 + 3 ^ 40 * 2056647 * 2
def baseEnd_2056647 : Nat := 234677432806115576189813

theorem tailTrace_2056647 : CollatzResearch.WordTrace tailWord_2056647 prefixEnd_2056647 234677432806115576189813 := by
  unfold tailWord_2056647
  simp only [CollatzResearch.WordTrace]
  refine ⟨75012078580126641188480195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50008052386751094125653463 75012078580126641188480195)
  ·
    refine ⟨112518117870189961782720293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75012078580126641188480195 112518117870189961782720293)
    ·
      refine ⟨21097147100660617834260055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112518117870189961782720293 21097147100660617834260055)
      ·
        refine ⟨31645720650990926751390083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21097147100660617834260055 31645720650990926751390083)
        ·
          refine ⟨47468580976486390127085125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31645720650990926751390083 47468580976486390127085125)
          ·
            refine ⟨8900358933091198148828461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47468580976486390127085125 8900358933091198148828461)
            ·
              refine ⟨3337634599909199305810673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8900358933091198148828461 3337634599909199305810673)
              ·
                refine ⟨2503225949931899479358005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3337634599909199305810673 2503225949931899479358005)
                ·
                  refine ⟨234677432806115576189813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2503225949931899479358005 234677432806115576189813)
                  ·
                    rfl

theorem cell22_2056647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 5].length) (baseStart_2056647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056647 prefixEnd_2056647 := by exact prefixLift 2056647
  have htrace : WordTrace (prefixWord ++ tailWord_2056647) baseStart_2056647 baseEnd_2056647 := by
    simpa [prefixWord, tailWord_2056647, baseEnd_2056647] using wordTrace_append hprefix tailTrace_2056647
  have hstable : (prefixWord ++ tailWord_2056647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056647).length < 2 ^ (prefixWord ++ tailWord_2056647).sum := by decide
  have hdescent : baseEnd_2056647 < baseStart_2056647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056694 : List Nat := [5, 1, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_2056694 : Nat := 118140960795 + 2056694 * 2 ^ 59
def prefixEnd_2056694 : Nat := 4983230072969 + 3 ^ 40 * 2056694 * 2
def baseEnd_2056694 : Nat := 704048387478854272644295

theorem tailTrace_2056694 : CollatzResearch.WordTrace tailWord_2056694 prefixEnd_2056694 704048387478854272644295 := by
  unfold tailWord_2056694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4688362050684773013465071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50009195207304245476960757 4688362050684773013465071)
  ·
    refine ⟨7032543076027159520197607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4688362050684773013465071 7032543076027159520197607)
    ·
      refine ⟨10548814614040739280296411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7032543076027159520197607 10548814614040739280296411)
      ·
        refine ⟨15823221921061108920444617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10548814614040739280296411 15823221921061108920444617)
        ·
          refine ⟨11867416440795831690333463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15823221921061108920444617 11867416440795831690333463)
          ·
            refine ⟨17801124661193747535500195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11867416440795831690333463 17801124661193747535500195)
            ·
              refine ⟨26701686991790621303250293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17801124661193747535500195 26701686991790621303250293)
              ·
                refine ⟨2503283155480370747179715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26701686991790621303250293 2503283155480370747179715)
                ·
                  refine ⟨3754924733220556120769573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503283155480370747179715 3754924733220556120769573)
                  ·
                    refine ⟨704048387478854272644295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3754924733220556120769573 704048387478854272644295)
                    ·
                      rfl

theorem cell22_2056694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_2056694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056694 prefixEnd_2056694 := by exact prefixLift 2056694
  have htrace : WordTrace (prefixWord ++ tailWord_2056694) baseStart_2056694 baseEnd_2056694 := by
    simpa [prefixWord, tailWord_2056694, baseEnd_2056694] using wordTrace_append hprefix tailTrace_2056694
  have hstable : (prefixWord ++ tailWord_2056694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056694).length < 2 ^ (prefixWord ++ tailWord_2056694).sum := by decide
  have hdescent : baseEnd_2056694 < baseStart_2056694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056707 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 4, 3]
def baseStart_2056707 : Nat := 118140960795 + 2056707 * 2 ^ 59
def prefixEnd_2056707 : Nat := 4983230072969 + 3 ^ 40 * 2056707 * 2
def baseEnd_2056707 : Nat := 704052837644526572069255

theorem tailTrace_2056707 : CollatzResearch.WordTrace tailWord_2056707 prefixEnd_2056707 704052837644526572069255 := by
  unfold tailWord_2056707
  simp only [CollatzResearch.WordTrace]
  refine ⟨75014266959909271435664375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50009511306606180957109583 75014266959909271435664375)
  ·
    refine ⟨112521400439863907153496563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75014266959909271435664375 112521400439863907153496563)
    ·
      refine ⟨168782100659795860730244845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112521400439863907153496563 168782100659795860730244845)
      ·
        refine ⟨63293287747423447773841817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168782100659795860730244845 63293287747423447773841817)
        ·
          refine ⟨47469965810567585830381363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63293287747423447773841817 47469965810567585830381363)
          ·
            refine ⟨71204948715851378745572045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47469965810567585830381363 71204948715851378745572045)
            ·
              refine ⟨26701855768444267029589517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71204948715851378745572045 26701855768444267029589517)
              ·
                refine ⟨10013195913166600136096069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26701855768444267029589517 10013195913166600136096069)
                ·
                  refine ⟨1877474233718737525518013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10013195913166600136096069 1877474233718737525518013)
                  ·
                    refine ⟨704052837644526572069255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1877474233718737525518013 704052837644526572069255)
                    ·
                      rfl

theorem cell22_2056707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 3].length) (baseStart_2056707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056707 prefixEnd_2056707 := by exact prefixLift 2056707
  have htrace : WordTrace (prefixWord ++ tailWord_2056707) baseStart_2056707 baseEnd_2056707 := by
    simpa [prefixWord, tailWord_2056707, baseEnd_2056707] using wordTrace_append hprefix tailTrace_2056707
  have hstable : (prefixWord ++ tailWord_2056707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056707).length < 2 ^ (prefixWord ++ tailWord_2056707).sum := by decide
  have hdescent : baseEnd_2056707 < baseStart_2056707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056739 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 2, 4]
def baseStart_2056739 : Nat := 118140960795 + 2056739 * 2 ^ 59
def prefixEnd_2056739 : Nat := 4983230072969 + 3 ^ 40 * 2056739 * 2
def baseEnd_2056739 : Nat := 704063791898489155269157

theorem tailTrace_2056739 : CollatzResearch.WordTrace tailWord_2056739 prefixEnd_2056739 704063791898489155269157 := by
  unfold tailWord_2056739
  simp only [CollatzResearch.WordTrace]
  refine ⟨75015434095793340900829271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50010289397195560600552847 75015434095793340900829271)
  ·
    refine ⟨112523151143690011351243907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75015434095793340900829271 112523151143690011351243907)
    ·
      refine ⟨168784726715535017026865861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112523151143690011351243907 168784726715535017026865861)
      ·
        refine ⟨31647136259162815692537349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168784726715535017026865861 31647136259162815692537349)
        ·
          refine ⟨5933838048593027942350753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31647136259162815692537349 5933838048593027942350753)
          ·
            refine ⟨4450378536444770956763065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5933838048593027942350753 4450378536444770956763065)
            ·
              refine ⟨3337783902333578217572299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450378536444770956763065 3337783902333578217572299)
              ·
                refine ⟨5006675853500367326358449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337783902333578217572299 5006675853500367326358449)
                ·
                  refine ⟨3755006890125275494768837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5006675853500367326358449 3755006890125275494768837)
                  ·
                    refine ⟨704063791898489155269157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3755006890125275494768837 704063791898489155269157)
                    ·
                      rfl

theorem cell22_2056739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 4].length) (baseStart_2056739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056739 prefixEnd_2056739 := by exact prefixLift 2056739
  have htrace : WordTrace (prefixWord ++ tailWord_2056739) baseStart_2056739 baseEnd_2056739 := by
    simpa [prefixWord, tailWord_2056739, baseEnd_2056739] using wordTrace_append hprefix tailTrace_2056739
  have hstable : (prefixWord ++ tailWord_2056739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056739).length < 2 ^ (prefixWord ++ tailWord_2056739).sum := by decide
  have hdescent : baseEnd_2056739 < baseStart_2056739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056758 : List Nat := [5, 1, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_2056758 : Nat := 118140960795 + 2056758 * 2 ^ 59
def prefixEnd_2056758 : Nat := 4983230072969 + 3 ^ 40 * 2056758 * 2
def baseEnd_2056758 : Nat := 704070295986779439044099

theorem tailTrace_2056758 : CollatzResearch.WordTrace tailWord_2056758 prefixEnd_2056758 704070295986779439044099 := by
  unfold tailWord_2056758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4688507942670281696610683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50010751388483004763847285 4688507942670281696610683)
  ·
    refine ⟨7032761914005422544916025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4688507942670281696610683 7032761914005422544916025)
    ·
      refine ⟨5274571435504066908687019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7032761914005422544916025 5274571435504066908687019)
      ·
        refine ⟨7911857153256100363030529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5274571435504066908687019 7911857153256100363030529)
        ·
          refine ⟨5933892864942075272272897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7911857153256100363030529 5933892864942075272272897)
          ·
            refine ⟨4450419648706556454204673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5933892864942075272272897 4450419648706556454204673)
            ·
              refine ⟨3337814736529917340653505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450419648706556454204673 3337814736529917340653505)
              ·
                refine ⟨2503361052397438005490129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3337814736529917340653505 2503361052397438005490129)
                ·
                  refine ⟨1877520789298078504117597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2503361052397438005490129 1877520789298078504117597)
                  ·
                    refine ⟨704070295986779439044099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1877520789298078504117597 704070295986779439044099)
                    ·
                      rfl

theorem cell22_2056758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_2056758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056758 prefixEnd_2056758 := by exact prefixLift 2056758
  have htrace : WordTrace (prefixWord ++ tailWord_2056758) baseStart_2056758 baseEnd_2056758 := by
    simpa [prefixWord, tailWord_2056758, baseEnd_2056758] using wordTrace_append hprefix tailTrace_2056758
  have hstable : (prefixWord ++ tailWord_2056758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056758).length < 2 ^ (prefixWord ++ tailWord_2056758).sum := by decide
  have hdescent : baseEnd_2056758 < baseStart_2056758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056814 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_2056814 : Nat := 118140960795 + 2056814 * 2 ^ 59
def prefixEnd_2056814 : Nat := 4983230072969 + 3 ^ 40 * 2056814 * 2
def baseEnd_2056814 : Nat := 704089465931213959643927

theorem tailTrace_2056814 : CollatzResearch.WordTrace tailWord_2056814 prefixEnd_2056814 704089465931213959643927 := by
  unfold tailWord_2056814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9377271196315203588726187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50012113047014419139872997 9377271196315203588726187)
  ·
    refine ⟨14065906794472805383089281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9377271196315203588726187 14065906794472805383089281)
    ·
      refine ⟨10549430095854604037316961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14065906794472805383089281 10549430095854604037316961)
      ·
        refine ⟨7912072571890953027987721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10549430095854604037316961 7912072571890953027987721)
        ·
          refine ⟨5934054428918214770990791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7912072571890953027987721 5934054428918214770990791)
          ·
            refine ⟨8901081643377322156486187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934054428918214770990791 8901081643377322156486187)
            ·
              refine ⟨13351622465065983234729281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8901081643377322156486187 13351622465065983234729281)
              ·
                refine ⟨10013716848799487426046961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13351622465065983234729281 10013716848799487426046961)
                ·
                  refine ⟨7510287636599615569535221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10013716848799487426046961 7510287636599615569535221)
                  ·
                    refine ⟨704089465931213959643927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7510287636599615569535221 704089465931213959643927)
                    ·
                      rfl

theorem cell22_2056814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_2056814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056814 prefixEnd_2056814 := by exact prefixLift 2056814
  have htrace : WordTrace (prefixWord ++ tailWord_2056814) baseStart_2056814 baseEnd_2056814 := by
    simpa [prefixWord, tailWord_2056814, baseEnd_2056814] using wordTrace_append hprefix tailTrace_2056814
  have hstable : (prefixWord ++ tailWord_2056814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056814).length < 2 ^ (prefixWord ++ tailWord_2056814).sum := by decide
  have hdescent : baseEnd_2056814 < baseStart_2056814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056816 : List Nat := [2, 1, 1, 1, 7, 2, 1, 2, 5]
def baseStart_2056816 : Nat := 118140960795 + 2056816 * 2 ^ 59
def prefixEnd_2056816 : Nat := 4983230072969 + 3 ^ 40 * 2056816 * 2
def baseEnd_2056816 : Nat := 234696716857362207031307

theorem tailTrace_2056816 : CollatzResearch.WordTrace tailWord_2056816 prefixEnd_2056816 234696716857362207031307 := by
  unfold tailWord_2056816
  simp only [CollatzResearch.WordTrace]
  refine ⟨37509121258257191525691151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50012161677676255367588201 37509121258257191525691151)
  ·
    refine ⟨56263681887385787288536727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37509121258257191525691151 56263681887385787288536727)
    ·
      refine ⟨84395522831078680932805091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56263681887385787288536727 84395522831078680932805091)
      ·
        refine ⟨126593284246618021399207637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84395522831078680932805091 126593284246618021399207637)
        ·
          refine ⟨2967030099530109876543929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 126593284246618021399207637 2967030099530109876543929)
          ·
            refine ⟨2225272574647582407407947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2967030099530109876543929 2225272574647582407407947)
            ·
              refine ⟨3337908861971373611111921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225272574647582407407947 3337908861971373611111921)
              ·
                refine ⟨2503431646478530208333941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3337908861971373611111921 2503431646478530208333941)
                ·
                  refine ⟨234696716857362207031307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2503431646478530208333941 234696716857362207031307)
                  ·
                    rfl

theorem cell22_2056816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 5].length) (baseStart_2056816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056816 prefixEnd_2056816 := by exact prefixLift 2056816
  have htrace : WordTrace (prefixWord ++ tailWord_2056816) baseStart_2056816 baseEnd_2056816 := by
    simpa [prefixWord, tailWord_2056816, baseEnd_2056816] using wordTrace_append hprefix tailTrace_2056816
  have hstable : (prefixWord ++ tailWord_2056816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056816).length < 2 ^ (prefixWord ++ tailWord_2056816).sum := by decide
  have hdescent : baseEnd_2056816 < baseStart_2056816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056846 : List Nat := [4, 1, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_2056846 : Nat := 118140960795 + 2056846 * 2 ^ 59
def prefixEnd_2056846 : Nat := 4983230072969 + 3 ^ 40 * 2056846 * 2
def baseEnd_2056846 : Nat := 704100420185176542843829

theorem tailTrace_2056846 : CollatzResearch.WordTrace tailWord_2056846 prefixEnd_2056846 704100420185176542843829 := by
  unfold tailWord_2056846
  simp only [CollatzResearch.WordTrace]
  refine ⟨9377417088300712271871799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50012891137603798783316261 9377417088300712271871799)
  ·
    refine ⟨14066125632451068407807699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9377417088300712271871799 14066125632451068407807699)
    ·
      refine ⟨21099188448676602611711549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14066125632451068407807699 21099188448676602611711549)
      ·
        refine ⟨7912195668253725979391831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21099188448676602611711549 7912195668253725979391831)
        ·
          refine ⟨11868293502380588969087747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7912195668253725979391831 11868293502380588969087747)
          ·
            refine ⟨17802440253570883453631621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11868293502380588969087747 17802440253570883453631621)
            ·
              refine ⟨3337957547544540647555929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17802440253570883453631621 3337957547544540647555929)
              ·
                refine ⟨2503468160658405485666947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3337957547544540647555929 2503468160658405485666947)
                ·
                  refine ⟨3755202240987608228500421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503468160658405485666947 3755202240987608228500421)
                  ·
                    refine ⟨704100420185176542843829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3755202240987608228500421 704100420185176542843829)
                    ·
                      rfl

theorem cell22_2056846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_2056846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056846 prefixEnd_2056846 := by exact prefixLift 2056846
  have htrace : WordTrace (prefixWord ++ tailWord_2056846) baseStart_2056846 baseEnd_2056846 := by
    simpa [prefixWord, tailWord_2056846, baseEnd_2056846] using wordTrace_append hprefix tailTrace_2056846
  have hstable : (prefixWord ++ tailWord_2056846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056846).length < 2 ^ (prefixWord ++ tailWord_2056846).sum := by decide
  have hdescent : baseEnd_2056846 < baseStart_2056846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056857 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 1, 6]
def baseStart_2056857 : Nat := 118140960795 + 2056857 * 2 ^ 59
def prefixEnd_2056857 : Nat := 4983230072969 + 3 ^ 40 * 2056857 * 2
def baseEnd_2056857 : Nat := 704104185709976180818795

theorem tailTrace_2056857 : CollatzResearch.WordTrace tailWord_2056857 prefixEnd_2056857 704104185709976180818795 := by
  unfold tailWord_2056857
  simp only [CollatzResearch.WordTrace]
  refine ⟨75019737909365847053624825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50013158606243898035749883 75019737909365847053624825)
  ·
    refine ⟨56264803432024385290218619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75019737909365847053624825 56264803432024385290218619)
    ·
      refine ⟨84397205148036577935327929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56264803432024385290218619 84397205148036577935327929)
      ·
        refine ⟨63297903861027433451495947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84397205148036577935327929 63297903861027433451495947)
        ·
          refine ⟨94946855791541150177243921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63297903861027433451495947 94946855791541150177243921)
          ·
            refine ⟨71210141843655862632932941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94946855791541150177243921 71210141843655862632932941)
            ·
              refine ⟨26703803191370948487349853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71210141843655862632932941 26703803191370948487349853)
              ·
                refine ⟨10013926196764105682756195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26703803191370948487349853 10013926196764105682756195)
                ·
                  refine ⟨15020889295146158524134293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10013926196764105682756195 15020889295146158524134293)
                  ·
                    refine ⟨704104185709976180818795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15020889295146158524134293 704104185709976180818795)
                    ·
                      rfl

theorem cell22_2056857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_2056857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056857 prefixEnd_2056857 := by exact prefixLift 2056857
  have htrace : WordTrace (prefixWord ++ tailWord_2056857) baseStart_2056857 baseEnd_2056857 := by
    simpa [prefixWord, tailWord_2056857, baseEnd_2056857] using wordTrace_append hprefix tailTrace_2056857
  have hstable : (prefixWord ++ tailWord_2056857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056857).length < 2 ^ (prefixWord ++ tailWord_2056857).sum := by decide
  have hdescent : baseEnd_2056857 < baseStart_2056857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056861 : List Nat := [1, 4, 2, 1, 1, 1, 5, 3, 4]
def baseStart_2056861 : Nat := 118140960795 + 2056861 * 2 ^ 59
def prefixEnd_2056861 : Nat := 4983230072969 + 3 ^ 40 * 2056861 * 2
def baseEnd_2056861 : Nat := 234701851663907167906261

theorem tailTrace_2056861 : CollatzResearch.WordTrace tailWord_2056861 prefixEnd_2056861 234701851663907167906261 := by
  unfold tailWord_2056861
  simp only [CollatzResearch.WordTrace]
  refine ⟨75019883801351355736770437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50013255867567570491180291 75019883801351355736770437)
  ·
    refine ⟨14066228212753379200644457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75019883801351355736770437 14066228212753379200644457)
    ·
      refine ⟨10549671159565034400483343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14066228212753379200644457 10549671159565034400483343)
      ·
        refine ⟨15824506739347551600725015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10549671159565034400483343 15824506739347551600725015)
        ·
          refine ⟨23736760109021327401087523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15824506739347551600725015 23736760109021327401087523)
          ·
            refine ⟨35605140163531991101631285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23736760109021327401087523 35605140163531991101631285)
            ·
              refine ⟨3337981890331124165777933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35605140163531991101631285 3337981890331124165777933)
              ·
                refine ⟨1251743208874171562166725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3337981890331124165777933 1251743208874171562166725)
                ·
                  refine ⟨234701851663907167906261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1251743208874171562166725 234701851663907167906261)
                  ·
                    rfl

theorem cell22_2056861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_2056861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056861 prefixEnd_2056861 := by exact prefixLift 2056861
  have htrace : WordTrace (prefixWord ++ tailWord_2056861) baseStart_2056861 baseEnd_2056861 := by
    simpa [prefixWord, tailWord_2056861, baseEnd_2056861] using wordTrace_append hprefix tailTrace_2056861
  have hstable : (prefixWord ++ tailWord_2056861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056861).length < 2 ^ (prefixWord ++ tailWord_2056861).sum := by decide
  have hdescent : baseEnd_2056861 < baseStart_2056861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056878 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_2056878 : Nat := 118140960795 + 2056878 * 2 ^ 59
def prefixEnd_2056878 : Nat := 4983230072969 + 3 ^ 40 * 2056878 * 2
def baseEnd_2056878 : Nat := 234703791479713042014577

theorem tailTrace_2056878 : CollatzResearch.WordTrace tailWord_2056878 prefixEnd_2056878 234703791479713042014577 := by
  unfold tailWord_2056878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9377562980286220955017411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50013669228193178426759525 9377562980286220955017411)
  ·
    refine ⟨14066344470429331432526117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9377562980286220955017411 14066344470429331432526117)
    ·
      refine ⟨2637439588205499643598647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14066344470429331432526117 2637439588205499643598647)
      ·
        refine ⟨3956159382308249465397971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2637439588205499643598647 3956159382308249465397971)
        ·
          refine ⟨5934239073462374198096957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3956159382308249465397971 5934239073462374198096957)
          ·
            refine ⟨2225339652548390324286359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5934239073462374198096957 2225339652548390324286359)
            ·
              refine ⟨3338009478822585486429539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225339652548390324286359 3338009478822585486429539)
              ·
                refine ⟨5007014218233878229644309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338009478822585486429539 5007014218233878229644309)
                ·
                  refine ⟨234703791479713042014577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5007014218233878229644309 234703791479713042014577)
                  ·
                    rfl

theorem cell22_2056878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_2056878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056878 prefixEnd_2056878 := by exact prefixLift 2056878
  have htrace : WordTrace (prefixWord ++ tailWord_2056878) baseStart_2056878 baseEnd_2056878 := by
    simpa [prefixWord, tailWord_2056878, baseEnd_2056878] using wordTrace_append hprefix tailTrace_2056878
  have hstable : (prefixWord ++ tailWord_2056878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056878).length < 2 ^ (prefixWord ++ tailWord_2056878).sum := by decide
  have hdescent : baseEnd_2056878 < baseStart_2056878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056893 : List Nat := [1, 4, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_2056893 : Nat := 118140960795 + 2056893 * 2 ^ 59
def prefixEnd_2056893 : Nat := 4983230072969 + 3 ^ 40 * 2056893 * 2
def baseEnd_2056893 : Nat := 704116509245684086918685

theorem tailTrace_2056893 : CollatzResearch.WordTrace tailWord_2056893 prefixEnd_2056893 704116509245684086918685 := by
  unfold tailWord_2056893
  simp only [CollatzResearch.WordTrace]
  refine ⟨75021050937235425201935333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50014033958156950134623555 75021050937235425201935333)
  ·
    refine ⟨14066447050731642225362875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75021050937235425201935333 14066447050731642225362875)
    ·
      refine ⟨21099670576097463338044313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14066447050731642225362875 21099670576097463338044313)
      ·
        refine ⟨15824752932073097503533235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21099670576097463338044313 15824752932073097503533235)
        ·
          refine ⟨23737129398109646255299853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15824752932073097503533235 23737129398109646255299853)
          ·
            refine ⟨8901423524291117345737445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23737129398109646255299853 8901423524291117345737445)
            ·
              refine ⟨1669016910804584502325771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8901423524291117345737445 1669016910804584502325771)
              ·
                refine ⟨2503525366206876753488657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669016910804584502325771 2503525366206876753488657)
                ·
                  refine ⟨1877644024655157565116493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2503525366206876753488657 1877644024655157565116493)
                  ·
                    refine ⟨704116509245684086918685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1877644024655157565116493 704116509245684086918685)
                    ·
                      rfl

theorem cell22_2056893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_2056893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056893 prefixEnd_2056893 := by exact prefixLift 2056893
  have htrace : WordTrace (prefixWord ++ tailWord_2056893) baseStart_2056893 baseEnd_2056893 := by
    simpa [prefixWord, tailWord_2056893, baseEnd_2056893] using wordTrace_append hprefix tailTrace_2056893
  have hstable : (prefixWord ++ tailWord_2056893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056893).length < 2 ^ (prefixWord ++ tailWord_2056893).sum := by decide
  have hdescent : baseEnd_2056893 < baseStart_2056893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056897 : List Nat := [1, 2, 6, 2, 2, 1, 1, 2, 1, 4]
def baseStart_2056897 : Nat := 118140960795 + 2056897 * 2 ^ 59
def prefixEnd_2056897 : Nat := 4983230072969 + 3 ^ 40 * 2056897 * 2
def baseEnd_2056897 : Nat := 704117878527429409818673

theorem tailTrace_2056897 : CollatzResearch.WordTrace tailWord_2056897 prefixEnd_2056897 704117878527429409818673 := by
  unfold tailWord_2056897
  simp only [CollatzResearch.WordTrace]
  refine ⟨75021196829220933885080945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50014131219480622590053963 75021196829220933885080945)
  ·
    refine ⟨56265897621915700413810709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75021196829220933885080945 56265897621915700413810709)
    ·
      refine ⟨2637463951027298456897377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56265897621915700413810709 2637463951027298456897377)
      ·
        refine ⟨1978097963270473842673033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2637463951027298456897377 1978097963270473842673033)
        ·
          refine ⟨1483573472452855382004775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1978097963270473842673033 1483573472452855382004775)
          ·
            refine ⟨2225360208679283073007163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483573472452855382004775 2225360208679283073007163)
            ·
              refine ⟨3338040313018924609510745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225360208679283073007163 3338040313018924609510745)
              ·
                refine ⟨2503530234764193457133059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3338040313018924609510745 2503530234764193457133059)
                ·
                  refine ⟨3755295352146290185699589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503530234764193457133059 3755295352146290185699589)
                  ·
                    refine ⟨704117878527429409818673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3755295352146290185699589 704117878527429409818673)
                    ·
                      rfl

theorem cell22_2056897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_2056897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056897 prefixEnd_2056897 := by exact prefixLift 2056897
  have htrace : WordTrace (prefixWord ++ tailWord_2056897) baseStart_2056897 baseEnd_2056897 := by
    simpa [prefixWord, tailWord_2056897, baseEnd_2056897] using wordTrace_append hprefix tailTrace_2056897
  have hstable : (prefixWord ++ tailWord_2056897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056897).length < 2 ^ (prefixWord ++ tailWord_2056897).sum := by decide
  have hdescent : baseEnd_2056897 < baseStart_2056897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056981 : List Nat := [1, 3, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_2056981 : Nat := 118140960795 + 2056981 * 2 ^ 59
def prefixEnd_2056981 : Nat := 4983230072969 + 3 ^ 40 * 2056981 * 2
def baseEnd_2056981 : Nat := 704146633444081190718415

theorem tailTrace_2056981 : CollatzResearch.WordTrace tailWord_2056981 prefixEnd_2056981 704146633444081190718415 := by
  unfold tailWord_2056981
  simp only [CollatzResearch.WordTrace]
  refine ⟨75024260560916616231138797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50016173707277744154092531 75024260560916616231138797)
  ·
    refine ⟨28134097710343731086677049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75024260560916616231138797 28134097710343731086677049)
    ·
      refine ⟨21100573282757798315007787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28134097710343731086677049 21100573282757798315007787)
      ·
        refine ⟨31650859924136697472511681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21100573282757798315007787 31650859924136697472511681)
        ·
          refine ⟨23738144943102523104383761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31650859924136697472511681 23738144943102523104383761)
          ·
            refine ⟨17803608707326892328287821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23738144943102523104383761 17803608707326892328287821)
            ·
              refine ⟨6676353265247584623107933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17803608707326892328287821 6676353265247584623107933)
              ·
                refine ⟨2503632474467844233665475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6676353265247584623107933 2503632474467844233665475)
                ·
                  refine ⟨3755448711701766350498213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503632474467844233665475 3755448711701766350498213)
                  ·
                    refine ⟨704146633444081190718415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3755448711701766350498213 704146633444081190718415)
                    ·
                      rfl

theorem cell22_2056981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_2056981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2056981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2056981 prefixEnd_2056981 := by exact prefixLift 2056981
  have htrace : WordTrace (prefixWord ++ tailWord_2056981) baseStart_2056981 baseEnd_2056981 := by
    simpa [prefixWord, tailWord_2056981, baseEnd_2056981] using wordTrace_append hprefix tailTrace_2056981
  have hstable : (prefixWord ++ tailWord_2056981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056981).length < 2 ^ (prefixWord ++ tailWord_2056981).sum := by decide
  have hdescent : baseEnd_2056981 < baseStart_2056981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057009 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 3, 6]
def baseStart_2057009 : Nat := 118140960795 + 2057009 * 2 ^ 59
def prefixEnd_2057009 : Nat := 4983230072969 + 3 ^ 40 * 2057009 * 2
def baseEnd_2057009 : Nat := 704156218416298451018329

theorem tailTrace_2057009 : CollatzResearch.WordTrace tailWord_2057009 prefixEnd_2057009 704156218416298451018329 := by
  unfold tailWord_2057009
  simp only [CollatzResearch.WordTrace]
  refine ⟨75025281804815177013158081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50016854536543451342105387 75025281804815177013158081)
  ·
    refine ⟨56268961353611382759868561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75025281804815177013158081 56268961353611382759868561)
    ·
      refine ⟨42201721015208537069901421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56268961353611382759868561 42201721015208537069901421)
      ·
        refine ⟨15825645380703201401213033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42201721015208537069901421 15825645380703201401213033)
        ·
          refine ⟨11869234035527401050909775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15825645380703201401213033 11869234035527401050909775)
          ·
            refine ⟨17803851053291101576364663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11869234035527401050909775 17803851053291101576364663)
            ·
              refine ⟨26705776579936652364546995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17803851053291101576364663 26705776579936652364546995)
              ·
                refine ⟨40058664869904978546820493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26705776579936652364546995 40058664869904978546820493)
                ·
                  refine ⟨15021999326214366955057685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40058664869904978546820493 15021999326214366955057685)
                  ·
                    refine ⟨704156218416298451018329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15021999326214366955057685 704156218416298451018329)
                    ·
                      rfl

theorem cell22_2057009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_2057009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057009 prefixEnd_2057009 := by exact prefixLift 2057009
  have htrace : WordTrace (prefixWord ++ tailWord_2057009) baseStart_2057009 baseEnd_2057009 := by
    simpa [prefixWord, tailWord_2057009, baseEnd_2057009] using wordTrace_append hprefix tailTrace_2057009
  have hstable : (prefixWord ++ tailWord_2057009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057009).length < 2 ^ (prefixWord ++ tailWord_2057009).sum := by decide
  have hdescent : baseEnd_2057009 < baseStart_2057009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057011 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 1, 5]
def baseStart_2057011 : Nat := 118140960795 + 2057011 * 2 ^ 59
def prefixEnd_2057011 : Nat := 4983230072969 + 3 ^ 40 * 2057011 * 2
def baseEnd_2057011 : Nat := 704156903057171112468323

theorem tailTrace_2057011 : CollatzResearch.WordTrace tailWord_2057011 prefixEnd_2057011 704156903057171112468323 := by
  unfold tailWord_2057011
  simp only [CollatzResearch.WordTrace]
  refine ⟨75025354750807931354730887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50016903167205287569820591 75025354750807931354730887)
  ·
    refine ⟨112538032126211897032096331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75025354750807931354730887 112538032126211897032096331)
    ·
      refine ⟨168807048189317845548144497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112538032126211897032096331 168807048189317845548144497)
      ·
        refine ⟨126605286141988384161108373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168807048189317845548144497 126605286141988384161108373)
        ·
          refine ⟨5934622787905705507551955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126605286141988384161108373 5934622787905705507551955)
          ·
            refine ⟨8901934181858558261327933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934622787905705507551955 8901934181858558261327933)
            ·
              refine ⟨3338225318196959347997975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8901934181858558261327933 3338225318196959347997975)
              ·
                refine ⟨5007337977295439021996963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338225318196959347997975 5007337977295439021996963)
                ·
                  refine ⟨7511006965943158532995445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007337977295439021996963 7511006965943158532995445)
                  ·
                    refine ⟨704156903057171112468323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7511006965943158532995445 704156903057171112468323)
                    ·
                      rfl

theorem cell22_2057011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 5].length) (baseStart_2057011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057011 prefixEnd_2057011 := by exact prefixLift 2057011
  have htrace : WordTrace (prefixWord ++ tailWord_2057011) baseStart_2057011 baseEnd_2057011 := by
    simpa [prefixWord, tailWord_2057011, baseEnd_2057011] using wordTrace_append hprefix tailTrace_2057011
  have hstable : (prefixWord ++ tailWord_2057011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057011).length < 2 ^ (prefixWord ++ tailWord_2057011).sum := by decide
  have hdescent : baseEnd_2057011 < baseStart_2057011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057041 : List Nat := [1, 2, 2, 1, 6, 2, 8]
def baseStart_2057041 : Nat := 118140960795 + 2057041 * 2 ^ 59
def prefixEnd_2057041 : Nat := 4983230072969 + 3 ^ 40 * 2057041 * 2
def baseEnd_2057041 : Nat := 26080265654454112378453

theorem tailTrace_2057041 : CollatzResearch.WordTrace tailWord_2057041 prefixEnd_2057041 26080265654454112378453 := by
  unfold tailWord_2057041
  simp only [CollatzResearch.WordTrace]
  refine ⟨75026448940699246478322977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50017632627132830985548651 75026448940699246478322977)
  ·
    refine ⟨56269836705524434858742233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75026448940699246478322977 56269836705524434858742233)
    ·
      refine ⟨42202377529143326144056675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56269836705524434858742233 42202377529143326144056675)
      ·
        refine ⟨63303566293714989216085013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42202377529143326144056675 63303566293714989216085013)
        ·
          refine ⟨2967354670017890119503985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63303566293714989216085013 2967354670017890119503985)
          ·
            refine ⟨2225516002513417589627989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2967354670017890119503985 2225516002513417589627989)
            ·
              refine ⟨26080265654454112378453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2225516002513417589627989 26080265654454112378453)
              ·
                rfl

theorem cell22_2057041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 8].length) (baseStart_2057041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057041 prefixEnd_2057041 := by exact prefixLift 2057041
  have htrace : WordTrace (prefixWord ++ tailWord_2057041) baseStart_2057041 baseEnd_2057041 := by
    simpa [prefixWord, tailWord_2057041, baseEnd_2057041] using wordTrace_append hprefix tailTrace_2057041
  have hstable : (prefixWord ++ tailWord_2057041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057041).length < 2 ^ (prefixWord ++ tailWord_2057041).sum := by decide
  have hdescent : baseEnd_2057041 < baseStart_2057041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057058 : List Nat := [3, 3, 2, 1, 3, 1, 2, 7]
def baseStart_2057058 : Nat := 118140960795 + 2057058 * 2 ^ 59
def prefixEnd_2057058 : Nat := 4983230072969 + 3 ^ 40 * 2057058 * 2
def baseEnd_2057058 : Nat := 78241443568630961838131

theorem tailTrace_2057058 : CollatzResearch.WordTrace tailWord_2057058 prefixEnd_2057058 78241443568630961838131 := by
  unfold tailWord_2057058
  simp only [CollatzResearch.WordTrace]
  refine ⟨18756767245409414595422957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50018045987758438921127885 18756767245409414595422957)
  ·
    refine ⟨7033787717028530473283609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18756767245409414595422957 7033787717028530473283609)
    ·
      refine ⟨5275340787771397854962707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7033787717028530473283609 5275340787771397854962707)
      ·
        refine ⟨7913011181657096782444061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5275340787771397854962707 7913011181657096782444061)
        ·
          refine ⟨2967379193121411293416523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7913011181657096782444061 2967379193121411293416523)
          ·
            refine ⟨4451068789682116940124785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967379193121411293416523 4451068789682116940124785)
            ·
              refine ⟨3338301592261587705093589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4451068789682116940124785 3338301592261587705093589)
              ·
                refine ⟨78241443568630961838131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3338301592261587705093589 78241443568630961838131)
                ·
                  rfl

theorem cell22_2057058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_2057058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057058 prefixEnd_2057058 := by exact prefixLift 2057058
  have htrace : WordTrace (prefixWord ++ tailWord_2057058) baseStart_2057058 baseEnd_2057058 := by
    simpa [prefixWord, tailWord_2057058, baseEnd_2057058] using wordTrace_append hprefix tailTrace_2057058
  have hstable : (prefixWord ++ tailWord_2057058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057058).length < 2 ^ (prefixWord ++ tailWord_2057058).sum := by decide
  have hdescent : baseEnd_2057058 < baseStart_2057058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057146 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_2057146 : Nat := 118140960795 + 2057146 * 2 ^ 59
def prefixEnd_2057146 : Nat := 4983230072969 + 3 ^ 40 * 2057146 * 2
def baseEnd_2057146 : Nat := 704203116316075760342909

theorem tailTrace_2057146 : CollatzResearch.WordTrace tailWord_2057146 prefixEnd_2057146 704203116316075760342909 := by
  unfold tailWord_2057146
  simp only [CollatzResearch.WordTrace]
  refine ⟨18757569651329712352723823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50020185736879232940596861 18757569651329712352723823)
  ·
    refine ⟨28136354476994568529085735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18757569651329712352723823 28136354476994568529085735)
    ·
      refine ⟨42204531715491852793628603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28136354476994568529085735 42204531715491852793628603)
      ·
        refine ⟨63306797573237779190442905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42204531715491852793628603 63306797573237779190442905)
        ·
          refine ⟨47480098179928334392832179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63306797573237779190442905 47480098179928334392832179)
          ·
            refine ⟨71220147269892501589248269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47480098179928334392832179 71220147269892501589248269)
            ·
              refine ⟨26707555226209688095968101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71220147269892501589248269 26707555226209688095968101)
              ·
                refine ⟨5007666604914316517994019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26707555226209688095968101 5007666604914316517994019)
                ·
                  refine ⟨7511499907371474776991029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007666604914316517994019 7511499907371474776991029)
                  ·
                    refine ⟨704203116316075760342909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7511499907371474776991029 704203116316075760342909)
                    ·
                      rfl

theorem cell22_2057146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_2057146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057146 prefixEnd_2057146 := by exact prefixLift 2057146
  have htrace : WordTrace (prefixWord ++ tailWord_2057146) baseStart_2057146 baseEnd_2057146 := by
    simpa [prefixWord, tailWord_2057146, baseEnd_2057146] using wordTrace_append hprefix tailTrace_2057146
  have hstable : (prefixWord ++ tailWord_2057146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057146).length < 2 ^ (prefixWord ++ tailWord_2057146).sum := by decide
  have hdescent : baseEnd_2057146 < baseStart_2057146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057163 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 4, 3]
def baseStart_2057163 : Nat := 118140960795 + 2057163 * 2 ^ 59
def prefixEnd_2057163 : Nat := 4983230072969 + 3 ^ 40 * 2057163 * 2
def baseEnd_2057163 : Nat := 704208935763493382667857

theorem tailTrace_2057163 : CollatzResearch.WordTrace tailWord_2057163 prefixEnd_2057163 704208935763493382667857 := by
  unfold tailWord_2057163
  simp only [CollatzResearch.WordTrace]
  refine ⟨75030898646257261314264143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50020599097504840876176095 75030898646257261314264143)
  ·
    refine ⟨112546347969385891971396215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75030898646257261314264143 112546347969385891971396215)
    ·
      refine ⟨168819521954078837957094323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112546347969385891971396215 168819521954078837957094323)
      ·
        refine ⟨253229282931118256935641485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168819521954078837957094323 253229282931118256935641485)
        ·
          refine ⟨94960981099169346350865557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253229282931118256935641485 94960981099169346350865557)
          ·
            refine ⟨4451295989023563110196823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94960981099169346350865557 4451295989023563110196823)
            ·
              refine ⟨6676943983535344665295235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4451295989023563110196823 6676943983535344665295235)
              ·
                refine ⟨10015415975303016997942853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676943983535344665295235 10015415975303016997942853)
                ·
                  refine ⟨1877890495369315687114285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10015415975303016997942853 1877890495369315687114285)
                  ·
                    refine ⟨704208935763493382667857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1877890495369315687114285 704208935763493382667857)
                    ·
                      rfl

theorem cell22_2057163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 3].length) (baseStart_2057163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057163 prefixEnd_2057163 := by exact prefixLift 2057163
  have htrace : WordTrace (prefixWord ++ tailWord_2057163) baseStart_2057163 baseEnd_2057163 := by
    simpa [prefixWord, tailWord_2057163, baseEnd_2057163] using wordTrace_append hprefix tailTrace_2057163
  have hstable : (prefixWord ++ tailWord_2057163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057163).length < 2 ^ (prefixWord ++ tailWord_2057163).sum := by decide
  have hdescent : baseEnd_2057163 < baseStart_2057163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057221 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 7]
def baseStart_2057221 : Nat := 118140960795 + 2057221 * 2 ^ 59
def prefixEnd_2057221 : Nat := 4983230072969 + 3 ^ 40 * 2057221 * 2
def baseEnd_2057221 : Nat := 234742930116266854905893

theorem tailTrace_2057221 : CollatzResearch.WordTrace tailWord_2057221 prefixEnd_2057221 234742930116266854905893 := by
  unfold tailWord_2057221
  simp only [CollatzResearch.WordTrace]
  refine ⟨75033014080047137219875517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50022009386698091479917011 75033014080047137219875517)
  ·
    refine ⟨28137380280017676457453319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75033014080047137219875517 28137380280017676457453319)
    ·
      refine ⟨42206070420026514686179979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28137380280017676457453319 42206070420026514686179979)
      ·
        refine ⟨63309105630039772029269969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42206070420026514686179979 63309105630039772029269969)
        ·
          refine ⟨47481829222529829021952477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63309105630039772029269969 47481829222529829021952477)
          ·
            refine ⟨17805685958448685883232179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47481829222529829021952477 17805685958448685883232179)
            ·
              refine ⟨26708528937673028824848269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17805685958448685883232179 26708528937673028824848269)
              ·
                refine ⟨10015698351627385809318101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26708528937673028824848269 10015698351627385809318101)
                ·
                  refine ⟨234742930116266854905893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10015698351627385809318101 234742930116266854905893)
                  ·
                    rfl

theorem cell22_2057221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_2057221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057221 prefixEnd_2057221 := by exact prefixLift 2057221
  have htrace : WordTrace (prefixWord ++ tailWord_2057221) baseStart_2057221 baseEnd_2057221 := by
    simpa [prefixWord, tailWord_2057221, baseEnd_2057221] using wordTrace_append hprefix tailTrace_2057221
  have hstable : (prefixWord ++ tailWord_2057221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057221).length < 2 ^ (prefixWord ++ tailWord_2057221).sum := by decide
  have hdescent : baseEnd_2057221 < baseStart_2057221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057225 : List Nat := [1, 2, 1, 1, 3, 1, 1, 8, 1, 3]
def baseStart_2057225 : Nat := 118140960795 + 2057225 * 2 ^ 59
def prefixEnd_2057225 : Nat := 4983230072969 + 3 ^ 40 * 2057225 * 2
def baseEnd_2057225 : Nat := 704230159630545887617667

theorem tailTrace_2057225 : CollatzResearch.WordTrace tailWord_2057225 prefixEnd_2057225 704230159630545887617667 := by
  unfold tailWord_2057225
  simp only [CollatzResearch.WordTrace]
  refine ⟨75033159972032645903021129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50022106648021763935347419 75033159972032645903021129)
  ·
    refine ⟨56274869979024484427265847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75033159972032645903021129 56274869979024484427265847)
    ·
      refine ⟨84412304968536726640898771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56274869979024484427265847 84412304968536726640898771)
      ·
        refine ⟨126618457452805089961348157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84412304968536726640898771 126618457452805089961348157)
        ·
          refine ⟨47481921544801908735505559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126618457452805089961348157 47481921544801908735505559)
          ·
            refine ⟨71222882317202863103258339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47481921544801908735505559 71222882317202863103258339)
            ·
              refine ⟨106834323475804294654887509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71222882317202863103258339 106834323475804294654887509)
              ·
                refine ⟨1251964728232081577986963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 106834323475804294654887509 1251964728232081577986963)
                ·
                  refine ⟨1877947092348122366980445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251964728232081577986963 1877947092348122366980445)
                  ·
                    refine ⟨704230159630545887617667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1877947092348122366980445 704230159630545887617667)
                    ·
                      rfl

theorem cell22_2057225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 1, 3].length) (baseStart_2057225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057225 prefixEnd_2057225 := by exact prefixLift 2057225
  have htrace : WordTrace (prefixWord ++ tailWord_2057225) baseStart_2057225 baseEnd_2057225 := by
    simpa [prefixWord, tailWord_2057225, baseEnd_2057225] using wordTrace_append hprefix tailTrace_2057225
  have hstable : (prefixWord ++ tailWord_2057225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057225).length < 2 ^ (prefixWord ++ tailWord_2057225).sum := by decide
  have hdescent : baseEnd_2057225 < baseStart_2057225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057349 : List Nat := [1, 3, 1, 1, 6, 1, 3, 1, 2, 3]
def baseStart_2057349 : Nat := 118140960795 + 2057349 * 2 ^ 59
def prefixEnd_2057349 : Nat := 4983230072969 + 3 ^ 40 * 2057349 * 2
def baseEnd_2057349 : Nat := 704272607364650897517287

theorem tailTrace_2057349 : CollatzResearch.WordTrace tailWord_2057349 prefixEnd_2057349 704272607364650897517287 := by
  unfold tailWord_2057349
  simp only [CollatzResearch.WordTrace]
  refine ⟨75037682623583415080535101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50025121749055610053690067 75037682623583415080535101)
  ·
    refine ⟨28139130983843780655200663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75037682623583415080535101 28139130983843780655200663)
    ·
      refine ⟨42208696475765670982800995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28139130983843780655200663 42208696475765670982800995)
      ·
        refine ⟨63313044713648506474201493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42208696475765670982800995 63313044713648506474201493)
        ·
          refine ⟨2967798970952273740978195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63313044713648506474201493 2967798970952273740978195)
          ·
            refine ⟨4451698456428410611467293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967798970952273740978195 4451698456428410611467293)
            ·
              refine ⟨1669386921160653979300235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4451698456428410611467293 1669386921160653979300235)
              ·
                refine ⟨2504080381740980968950353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669386921160653979300235 2504080381740980968950353)
                ·
                  refine ⟨1878060286305735726712765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2504080381740980968950353 1878060286305735726712765)
                  ·
                    refine ⟨704272607364650897517287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1878060286305735726712765 704272607364650897517287)
                    ·
                      rfl

theorem cell22_2057349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_2057349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057349 prefixEnd_2057349 := by exact prefixLift 2057349
  have htrace : WordTrace (prefixWord ++ tailWord_2057349) baseStart_2057349 baseEnd_2057349 := by
    simpa [prefixWord, tailWord_2057349, baseEnd_2057349] using wordTrace_append hprefix tailTrace_2057349
  have hstable : (prefixWord ++ tailWord_2057349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057349).length < 2 ^ (prefixWord ++ tailWord_2057349).sum := by decide
  have hdescent : baseEnd_2057349 < baseStart_2057349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057362 : List Nat := [3, 2, 3, 1, 1, 4, 2, 6]
def baseStart_2057362 : Nat := 118140960795 + 2057362 * 2 ^ 59
def prefixEnd_2057362 : Nat := 4983230072969 + 3 ^ 40 * 2057362 * 2
def baseEnd_2057362 : Nat := 78253006392258132993583

theorem tailTrace_2057362 : CollatzResearch.WordTrace tailWord_2057362 prefixEnd_2057362 78253006392258132993583 := by
  unfold tailWord_2057362
  simp only [CollatzResearch.WordTrace]
  refine ⟨18759539193134079575189585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50025437848357545533838893 18759539193134079575189585)
  ·
    refine ⟨14069654394850559681392189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18759539193134079575189585 14069654394850559681392189)
    ·
      refine ⟨5276120398068959880522071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14069654394850559681392189 5276120398068959880522071)
      ·
        refine ⟨7914180597103439820783107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5276120398068959880522071 7914180597103439820783107)
        ·
          refine ⟨11871270895655159731174661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7914180597103439820783107 11871270895655159731174661)
          ·
            refine ⟨2225863292935342449595249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11871270895655159731174661 2225863292935342449595249)
            ·
              refine ⟨1669397469701506837196437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2225863292935342449595249 1669397469701506837196437)
              ·
                refine ⟨78253006392258132993583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1669397469701506837196437 78253006392258132993583)
                ·
                  rfl

theorem cell22_2057362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_2057362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057362 prefixEnd_2057362 := by exact prefixLift 2057362
  have htrace : WordTrace (prefixWord ++ tailWord_2057362) baseStart_2057362 baseEnd_2057362 := by
    simpa [prefixWord, tailWord_2057362, baseEnd_2057362] using wordTrace_append hprefix tailTrace_2057362
  have hstable : (prefixWord ++ tailWord_2057362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057362).length < 2 ^ (prefixWord ++ tailWord_2057362).sum := by decide
  have hdescent : baseEnd_2057362 < baseStart_2057362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057373 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 9]
def baseStart_2057373 : Nat := 118140960795 + 2057373 * 2 ^ 59
def prefixEnd_2057373 : Nat := 4983230072969 + 3 ^ 40 * 2057373 * 2
def baseEnd_2057373 : Nat := 234760274351707611639071

theorem tailTrace_2057373 : CollatzResearch.WordTrace tailWord_2057373 prefixEnd_2057373 234760274351707611639071 := by
  unfold tailWord_2057373
  simp only [CollatzResearch.WordTrace]
  refine ⟨75038557975496467179408773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50025705316997644786272515 75038557975496467179408773)
  ·
    refine ⟨14069729620405587596139145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75038557975496467179408773 14069729620405587596139145)
    ·
      refine ⟨10552297215304190697104359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14069729620405587596139145 10552297215304190697104359)
      ·
        refine ⟨15828445822956286045656539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10552297215304190697104359 15828445822956286045656539)
        ·
          refine ⟨23742668734434429068484809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15828445822956286045656539 23742668734434429068484809)
          ·
            refine ⟨17807001550825821801363607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23742668734434429068484809 17807001550825821801363607)
            ·
              refine ⟨26710502326238732702045411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17807001550825821801363607 26710502326238732702045411)
              ·
                refine ⟨40065753489358099053068117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26710502326238732702045411 40065753489358099053068117)
                ·
                  refine ⟨234760274351707611639071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40065753489358099053068117 234760274351707611639071)
                  ·
                    rfl

theorem cell22_2057373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_2057373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057373 prefixEnd_2057373 := by exact prefixLift 2057373
  have htrace : WordTrace (prefixWord ++ tailWord_2057373) baseStart_2057373 baseEnd_2057373 := by
    simpa [prefixWord, tailWord_2057373, baseEnd_2057373] using wordTrace_append hprefix tailTrace_2057373
  have hstable : (prefixWord ++ tailWord_2057373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057373).length < 2 ^ (prefixWord ++ tailWord_2057373).sum := by decide
  have hdescent : baseEnd_2057373 < baseStart_2057373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057388 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_2057388 : Nat := 118140960795 + 2057388 * 2 ^ 59
def prefixEnd_2057388 : Nat := 4983230072969 + 3 ^ 40 * 2057388 * 2
def baseEnd_2057388 : Nat := 704285957861667795792167

theorem tailTrace_2057388 : CollatzResearch.WordTrace tailWord_2057388 prefixEnd_2057388 704285957861667795792167 := by
  unfold tailWord_2057388
  simp only [CollatzResearch.WordTrace]
  refine ⟨37519552535221062370602409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50026070046961416494136545 37519552535221062370602409)
  ·
    refine ⟨28139664401415796777951807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37519552535221062370602409 28139664401415796777951807)
    ·
      refine ⟨42209496602123695166927711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28139664401415796777951807 42209496602123695166927711)
      ·
        refine ⟨63314244903185542750391567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42209496602123695166927711 63314244903185542750391567)
        ·
          refine ⟨94971367354778314125587351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63314244903185542750391567 94971367354778314125587351)
          ·
            refine ⟨142457051032167471188381027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94971367354778314125587351 142457051032167471188381027)
            ·
              refine ⟨213685576548251206782571541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142457051032167471188381027 213685576548251206782571541)
              ·
                refine ⟨10016511400699275317933041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213685576548251206782571541 10016511400699275317933041)
                ·
                  refine ⟨7512383550524456488449781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10016511400699275317933041 7512383550524456488449781)
                  ·
                    refine ⟨704285957861667795792167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7512383550524456488449781 704285957861667795792167)
                    ·
                      rfl

theorem cell22_2057388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_2057388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057388 prefixEnd_2057388 := by exact prefixLift 2057388
  have htrace : WordTrace (prefixWord ++ tailWord_2057388) baseStart_2057388 baseEnd_2057388 := by
    simpa [prefixWord, tailWord_2057388, baseEnd_2057388] using wordTrace_append hprefix tailTrace_2057388
  have hstable : (prefixWord ++ tailWord_2057388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057388).length < 2 ^ (prefixWord ++ tailWord_2057388).sum := by decide
  have hdescent : baseEnd_2057388 < baseStart_2057388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057452 : List Nat := [2, 2, 1, 1, 2, 5, 1, 4, 4]
def baseStart_2057452 : Nat := 118140960795 + 2057452 * 2 ^ 59
def prefixEnd_2057452 : Nat := 4983230072969 + 3 ^ 40 * 2057452 * 2
def baseEnd_2057452 : Nat := 234769288789864320730657

theorem tailTrace_2057452 : CollatzResearch.WordTrace tailWord_2057452 prefixEnd_2057452 234769288789864320730657 := by
  unfold tailWord_2057452
  simp only [CollatzResearch.WordTrace]
  refine ⟨37520719671105131835767305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50027626228140175781023073 37520719671105131835767305)
  ·
    refine ⟨28140539753328848876825479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37520719671105131835767305 28140539753328848876825479)
    ·
      refine ⟨42210809629993273315238219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28140539753328848876825479 42210809629993273315238219)
      ·
        refine ⟨63316214444989909972857329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42210809629993273315238219 63316214444989909972857329)
        ·
          refine ⟨47487160833742432479642997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63316214444989909972857329 47487160833742432479642997)
          ·
            refine ⟨4451921328163353044966531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47487160833742432479642997 4451921328163353044966531)
            ·
              refine ⟨6677881992245029567449797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4451921328163353044966531 6677881992245029567449797)
              ·
                refine ⟨1252102873545943043896837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6677881992245029567449797 1252102873545943043896837)
                ·
                  refine ⟨234769288789864320730657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1252102873545943043896837 234769288789864320730657)
                  ·
                    rfl

theorem cell22_2057452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_2057452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057452 prefixEnd_2057452 := by exact prefixLift 2057452
  have htrace : WordTrace (prefixWord ++ tailWord_2057452) baseStart_2057452 baseEnd_2057452 := by
    simpa [prefixWord, tailWord_2057452, baseEnd_2057452] using wordTrace_append hprefix tailTrace_2057452
  have hstable : (prefixWord ++ tailWord_2057452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057452).length < 2 ^ (prefixWord ++ tailWord_2057452).sum := by decide
  have hdescent : baseEnd_2057452 < baseStart_2057452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057501 : List Nat := [1, 4, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_2057501 : Nat := 118140960795 + 2057501 * 2 ^ 59
def prefixEnd_2057501 : Nat := 4983230072969 + 3 ^ 40 * 2057501 * 2
def baseEnd_2057501 : Nat := 704324640070973167716821

theorem tailTrace_2057501 : CollatzResearch.WordTrace tailWord_2057501 prefixEnd_2057501 704324640070973167716821 := by
  unfold tailWord_2057501
  simp only [CollatzResearch.WordTrace]
  refine ⟨75043226519032745040068357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50028817679355163360045571 75043226519032745040068357)
  ·
    refine ⟨14070604972318639695012817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75043226519032745040068357 14070604972318639695012817)
    ·
      refine ⟨10552953729238979771259613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14070604972318639695012817 10552953729238979771259613)
      ·
        refine ⟨3957357648464617414222355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10552953729238979771259613 3957357648464617414222355)
        ·
          refine ⟨5936036472696926121333533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3957357648464617414222355 5936036472696926121333533)
          ·
            refine ⟨2226013677261347295500075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5936036472696926121333533 2226013677261347295500075)
            ·
              refine ⟨3339020515892020943250113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226013677261347295500075 3339020515892020943250113)
              ·
                refine ⟨2504265386919015707437585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3339020515892020943250113 2504265386919015707437585)
                ·
                  refine ⟨1878199040189261780578189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2504265386919015707437585 1878199040189261780578189)
                  ·
                    refine ⟨704324640070973167716821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1878199040189261780578189 704324640070973167716821)
                    ·
                      rfl

theorem cell22_2057501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_2057501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057501 prefixEnd_2057501 := by exact prefixLift 2057501
  have htrace : WordTrace (prefixWord ++ tailWord_2057501) baseStart_2057501 baseEnd_2057501 := by
    simpa [prefixWord, tailWord_2057501, baseEnd_2057501] using wordTrace_append hprefix tailTrace_2057501
  have hstable : (prefixWord ++ tailWord_2057501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057501).length < 2 ^ (prefixWord ++ tailWord_2057501).sum := by decide
  have hdescent : baseEnd_2057501 < baseStart_2057501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057576 : List Nat := [2, 1, 4, 2, 3, 2, 2, 1, 5]
def baseStart_2057576 : Nat := 118140960795 + 2057576 * 2 ^ 59
def prefixEnd_2057576 : Nat := 4983230072969 + 3 ^ 40 * 2057576 * 2
def baseEnd_2057576 : Nat := 234783438034565990697197

theorem tailTrace_2057576 : CollatzResearch.WordTrace tailWord_2057576 prefixEnd_2057576 234783438034565990697197 := by
  unfold tailWord_2057576
  simp only [CollatzResearch.WordTrace]
  refine ⟨37522980996880516424524291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50030641329174021899365721 37522980996880516424524291)
  ·
    refine ⟨56284471495320774636786437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37522980996880516424524291 56284471495320774636786437)
    ·
      refine ⟨10553338405372645244397457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56284471495320774636786437 10553338405372645244397457)
      ·
        refine ⟨7915003804029483933298093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10553338405372645244397457 7915003804029483933298093)
        ·
          refine ⟨2968126426511056474986785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7915003804029483933298093 2968126426511056474986785)
          ·
            refine ⟨2226094819883292356240089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2968126426511056474986785 2226094819883292356240089)
            ·
              refine ⟨1669571114912469267180067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2226094819883292356240089 1669571114912469267180067)
              ·
                refine ⟨2504356672368703900770101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669571114912469267180067 2504356672368703900770101)
                ·
                  refine ⟨234783438034565990697197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2504356672368703900770101 234783438034565990697197)
                  ·
                    rfl

theorem cell22_2057576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 5].length) (baseStart_2057576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057576 prefixEnd_2057576 := by exact prefixLift 2057576
  have htrace : WordTrace (prefixWord ++ tailWord_2057576) baseStart_2057576 baseEnd_2057576 := by
    simpa [prefixWord, tailWord_2057576, baseEnd_2057576] using wordTrace_append hprefix tailTrace_2057576
  have hstable : (prefixWord ++ tailWord_2057576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057576).length < 2 ^ (prefixWord ++ tailWord_2057576).sum := by decide
  have hdescent : baseEnd_2057576 < baseStart_2057576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057589 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_2057589 : Nat := 118140960795 + 2057589 * 2 ^ 59
def prefixEnd_2057589 : Nat := 4983230072969 + 3 ^ 40 * 2057589 * 2
def baseEnd_2057589 : Nat := 704354764269370271516551

theorem tailTrace_2057589 : CollatzResearch.WordTrace tailWord_2057589 prefixEnd_2057589 704354764269370271516551 := by
  unfold tailWord_2057589
  simp only [CollatzResearch.WordTrace]
  refine ⟨75046436142713936069271821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50030957428475957379514547 75046436142713936069271821)
  ·
    refine ⟨28142413553517726025976933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75046436142713936069271821 28142413553517726025976933)
    ·
      refine ⟨5276702541284573629870675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28142413553517726025976933 5276702541284573629870675)
      ·
        refine ⟨7915053811926860444806013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5276702541284573629870675 7915053811926860444806013)
        ·
          refine ⟨2968145179472572666802255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7915053811926860444806013 2968145179472572666802255)
          ·
            refine ⟨4452217769208859000203383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968145179472572666802255 4452217769208859000203383)
            ·
              refine ⟨6678326653813288500305075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4452217769208859000203383 6678326653813288500305075)
              ·
                refine ⟨10017489980719932750457613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6678326653813288500305075 10017489980719932750457613)
                ·
                  refine ⟨3756558742769974781421605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10017489980719932750457613 3756558742769974781421605)
                  ·
                    refine ⟨704354764269370271516551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3756558742769974781421605 704354764269370271516551)
                    ·
                      rfl

theorem cell22_2057589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_2057589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057589 prefixEnd_2057589 := by exact prefixLift 2057589
  have htrace : WordTrace (prefixWord ++ tailWord_2057589) baseStart_2057589 baseEnd_2057589 := by
    simpa [prefixWord, tailWord_2057589, baseEnd_2057589] using wordTrace_append hprefix tailTrace_2057589
  have hstable : (prefixWord ++ tailWord_2057589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057589).length < 2 ^ (prefixWord ++ tailWord_2057589).sum := by decide
  have hdescent : baseEnd_2057589 < baseStart_2057589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057600 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 1, 6]
def baseStart_2057600 : Nat := 118140960795 + 2057600 * 2 ^ 59
def prefixEnd_2057600 : Nat := 4983230072969 + 3 ^ 40 * 2057600 * 2
def baseEnd_2057600 : Nat := 704358529794169909491517

theorem tailTrace_2057600 : CollatzResearch.WordTrace tailWord_2057600 prefixEnd_2057600 704358529794169909491517 := by
  unfold tailWord_2057600
  simp only [CollatzResearch.WordTrace]
  refine ⟨37523418672837042473961127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50031224897116056631948169 37523418672837042473961127)
  ·
    refine ⟨56285128009255563710941691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37523418672837042473961127 56285128009255563710941691)
    ·
      refine ⟨84427692013883345566412537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56285128009255563710941691 84427692013883345566412537)
      ·
        refine ⟨63320769010412509174809403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84427692013883345566412537 63320769010412509174809403)
        ·
          refine ⟨94981153515618763762214105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63320769010412509174809403 94981153515618763762214105)
          ·
            refine ⟨71235865136714072821660579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94981153515618763762214105 71235865136714072821660579)
            ·
              refine ⟨106853797705071109232490869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71235865136714072821660579 106853797705071109232490869)
              ·
                refine ⟨10017543534850416490546019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106853797705071109232490869 10017543534850416490546019)
                ·
                  refine ⟨15026315302275624735819029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10017543534850416490546019 15026315302275624735819029)
                  ·
                    refine ⟨704358529794169909491517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15026315302275624735819029 704358529794169909491517)
                    ·
                      rfl

theorem cell22_2057600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_2057600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057600 prefixEnd_2057600 := by exact prefixLift 2057600
  have htrace : WordTrace (prefixWord ++ tailWord_2057600) baseStart_2057600 baseEnd_2057600 := by
    simpa [prefixWord, tailWord_2057600, baseEnd_2057600] using wordTrace_append hprefix tailTrace_2057600
  have hstable : (prefixWord ++ tailWord_2057600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057600).length < 2 ^ (prefixWord ++ tailWord_2057600).sum := by decide
  have hdescent : baseEnd_2057600 < baseStart_2057600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057724 : List Nat := [2, 2, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_2057724 : Nat := 118140960795 + 2057724 * 2 ^ 59
def prefixEnd_2057724 : Nat := 4983230072969 + 3 ^ 40 * 2057724 * 2
def baseEnd_2057724 : Nat := 704400977528274919391137

theorem tailTrace_2057724 : CollatzResearch.WordTrace tailWord_2057724 prefixEnd_2057724 704400977528274919391137 := by
  unfold tailWord_2057724
  simp only [CollatzResearch.WordTrace]
  refine ⟨37525679998612427062718113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50034239998149902750290817 37525679998612427062718113)
  ·
    refine ⟨28144259998959320297038585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37525679998612427062718113 28144259998959320297038585)
    ·
      refine ⟨21108194999219490222778939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28144259998959320297038585 21108194999219490222778939)
      ·
        refine ⟨31662292498829235334168409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21108194999219490222778939 31662292498829235334168409)
        ·
          refine ⟨23746719374121926500626307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31662292498829235334168409 23746719374121926500626307)
          ·
            refine ⟨35620079061182889750939461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23746719374121926500626307 35620079061182889750939461)
            ·
              refine ⟨6678764823971791828301149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35620079061182889750939461 6678764823971791828301149)
              ·
                refine ⟨2504536808989421935612931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6678764823971791828301149 2504536808989421935612931)
                ·
                  refine ⟨3756805213484132903419397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504536808989421935612931 3756805213484132903419397)
                  ·
                    refine ⟨704400977528274919391137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3756805213484132903419397 704400977528274919391137)
                    ·
                      rfl

theorem cell22_2057724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_2057724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057724 prefixEnd_2057724 := by exact prefixLift 2057724
  have htrace : WordTrace (prefixWord ++ tailWord_2057724) baseStart_2057724 baseEnd_2057724 := by
    simpa [prefixWord, tailWord_2057724, baseEnd_2057724] using wordTrace_append hprefix tailTrace_2057724
  have hstable : (prefixWord ++ tailWord_2057724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057724).length < 2 ^ (prefixWord ++ tailWord_2057724).sum := by decide
  have hdescent : baseEnd_2057724 < baseStart_2057724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057788 : List Nat := [2, 2, 2, 2, 4, 1, 2, 2, 2, 3]
def baseStart_2057788 : Nat := 118140960795 + 2057788 * 2 ^ 59
def prefixEnd_2057788 : Nat := 4983230072969 + 3 ^ 40 * 2057788 * 2
def baseEnd_2057788 : Nat := 704422886036200085790941

theorem tailTrace_2057788 : CollatzResearch.WordTrace tailWord_2057788 prefixEnd_2057788 704422886036200085790941 := by
  unfold tailWord_2057788
  simp only [CollatzResearch.WordTrace]
  refine ⟨37526847134496496527883009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50035796179328662037177345 37526847134496496527883009)
  ·
    refine ⟨28145135350872372395912257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37526847134496496527883009 28145135350872372395912257)
    ·
      refine ⟨21108851513154279296934193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28145135350872372395912257 21108851513154279296934193)
      ·
        refine ⟨15831638634865709472700645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21108851513154279296934193 15831638634865709472700645)
        ·
          refine ⟨2968432244037320526131371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15831638634865709472700645 2968432244037320526131371)
          ·
            refine ⟨4452648366055980789197057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968432244037320526131371 4452648366055980789197057)
            ·
              refine ⟨3339486274541985591897793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4452648366055980789197057 3339486274541985591897793)
              ·
                refine ⟨2504614705906489193923345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3339486274541985591897793 2504614705906489193923345)
                ·
                  refine ⟨1878461029429866895442509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2504614705906489193923345 1878461029429866895442509)
                  ·
                    refine ⟨704422886036200085790941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1878461029429866895442509 704422886036200085790941)
                    ·
                      rfl

theorem cell22_2057788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_2057788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057788 prefixEnd_2057788 := by exact prefixLift 2057788
  have htrace : WordTrace (prefixWord ++ tailWord_2057788) baseStart_2057788 baseEnd_2057788 := by
    simpa [prefixWord, tailWord_2057788, baseEnd_2057788] using wordTrace_append hprefix tailTrace_2057788
  have hstable : (prefixWord ++ tailWord_2057788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057788).length < 2 ^ (prefixWord ++ tailWord_2057788).sum := by decide
  have hdescent : baseEnd_2057788 < baseStart_2057788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057797 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_2057797 : Nat := 118140960795 + 2057797 * 2 ^ 59
def prefixEnd_2057797 : Nat := 4983230072969 + 3 ^ 40 * 2057797 * 2
def baseEnd_2057797 : Nat := 704425966920127062315913

theorem tailTrace_2057797 : CollatzResearch.WordTrace tailWord_2057797 prefixEnd_2057797 704425966920127062315913 := by
  unfold tailWord_2057797
  simp only [CollatzResearch.WordTrace]
  refine ⟨75054022525960387592843645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50036015017306925061895763 75054022525960387592843645)
  ·
    refine ⟨28145258447235145347316367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75054022525960387592843645 28145258447235145347316367)
    ·
      refine ⟨42217887670852718020974551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28145258447235145347316367 42217887670852718020974551)
      ·
        refine ⟨63326831506279077031461827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42217887670852718020974551 63326831506279077031461827)
        ·
          refine ⟨94990247259418615547192741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63326831506279077031461827 94990247259418615547192741)
          ·
            refine ⟨17810671361140990415098639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94990247259418615547192741 17810671361140990415098639)
            ·
              refine ⟨26716007041711485622647959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17810671361140990415098639 26716007041711485622647959)
              ·
                refine ⟨40074010562567228433971939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26716007041711485622647959 40074010562567228433971939)
                ·
                  refine ⟨60111015843850842650957909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40074010562567228433971939 60111015843850842650957909)
                  ·
                    refine ⟨704425966920127062315913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60111015843850842650957909 704425966920127062315913)
                    ·
                      rfl

theorem cell22_2057797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_2057797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057797 prefixEnd_2057797 := by exact prefixLift 2057797
  have htrace : WordTrace (prefixWord ++ tailWord_2057797) baseStart_2057797 baseEnd_2057797 := by
    simpa [prefixWord, tailWord_2057797, baseEnd_2057797] using wordTrace_append hprefix tailTrace_2057797
  have hstable : (prefixWord ++ tailWord_2057797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057797).length < 2 ^ (prefixWord ++ tailWord_2057797).sum := by decide
  have hdescent : baseEnd_2057797 < baseStart_2057797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057846 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_2057846 : Nat := 118140960795 + 2057846 * 2 ^ 59
def prefixEnd_2057846 : Nat := 4983230072969 + 3 ^ 40 * 2057846 * 2
def baseEnd_2057846 : Nat := 234814246873835755946921

theorem tailTrace_2057846 : CollatzResearch.WordTrace tailWord_2057846 prefixEnd_2057846 234814246873835755946921 := by
  unfold tailWord_2057846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4690988106423929310086087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50037206468521912640918261 4690988106423929310086087)
  ·
    refine ⟨7036482159635893965129131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4690988106423929310086087 7036482159635893965129131)
    ·
      refine ⟨10554723239453840947693697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7036482159635893965129131 10554723239453840947693697)
      ·
        refine ⟨7916042429590380710770273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10554723239453840947693697 7916042429590380710770273)
        ·
          refine ⟨5937031822192785533077705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7916042429590380710770273 5937031822192785533077705)
          ·
            refine ⟨4452773866644589149808279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5937031822192785533077705 4452773866644589149808279)
            ·
              refine ⟨6679160799966883724712419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4452773866644589149808279 6679160799966883724712419)
              ·
                refine ⟨10018741199950325587068629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6679160799966883724712419 10018741199950325587068629)
                ·
                  refine ⟨234814246873835755946921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10018741199950325587068629 234814246873835755946921)
                  ·
                    rfl

theorem cell22_2057846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_2057846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057846 prefixEnd_2057846 := by exact prefixLift 2057846
  have htrace : WordTrace (prefixWord ++ tailWord_2057846) baseStart_2057846 baseEnd_2057846 := by
    simpa [prefixWord, tailWord_2057846, baseEnd_2057846] using wordTrace_append hprefix tailTrace_2057846
  have hstable : (prefixWord ++ tailWord_2057846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057846).length < 2 ^ (prefixWord ++ tailWord_2057846).sum := by decide
  have hdescent : baseEnd_2057846 < baseStart_2057846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057904 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 4, 4]
def baseStart_2057904 : Nat := 118140960795 + 2057904 * 2 ^ 59
def prefixEnd_2057904 : Nat := 4983230072969 + 3 ^ 40 * 2057904 * 2
def baseEnd_2057904 : Nat := 704462595206814449890585

theorem tailTrace_2057904 : CollatzResearch.WordTrace tailWord_2057904 prefixEnd_2057904 704462595206814449890585 := by
  unfold tailWord_2057904
  simp only [CollatzResearch.WordTrace]
  refine ⟨37528962568286372433494383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50038616757715163244659177 37528962568286372433494383)
  ·
    refine ⟨56293443852429558650241575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37528962568286372433494383 56293443852429558650241575)
    ·
      refine ⟨84440165778644337975362363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56293443852429558650241575 84440165778644337975362363)
      ·
        refine ⟨126660248667966506963043545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84440165778644337975362363 126660248667966506963043545)
        ·
          refine ⟨94995186500974880222282659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126660248667966506963043545 94995186500974880222282659)
          ·
            refine ⟨142492779751462320333423989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94995186500974880222282659 142492779751462320333423989)
            ·
              refine ⟨13358698101699592531258499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142492779751462320333423989 13358698101699592531258499)
              ·
                refine ⟨20038047152549388796887749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13358698101699592531258499 20038047152549388796887749)
                ·
                  refine ⟨3757133841103010399416453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20038047152549388796887749 3757133841103010399416453)
                  ·
                    refine ⟨704462595206814449890585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3757133841103010399416453 704462595206814449890585)
                    ·
                      rfl

theorem cell22_2057904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_2057904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057904 prefixEnd_2057904 := by exact prefixLift 2057904
  have htrace : WordTrace (prefixWord ++ tailWord_2057904) baseStart_2057904 baseEnd_2057904 := by
    simpa [prefixWord, tailWord_2057904, baseEnd_2057904] using wordTrace_append hprefix tailTrace_2057904
  have hstable : (prefixWord ++ tailWord_2057904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057904).length < 2 ^ (prefixWord ++ tailWord_2057904).sum := by decide
  have hdescent : baseEnd_2057904 < baseStart_2057904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057906 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_2057906 : Nat := 118140960795 + 2057906 * 2 ^ 59
def prefixEnd_2057906 : Nat := 4983230072969 + 3 ^ 40 * 2057906 * 2
def baseEnd_2057906 : Nat := 704463279847687111340579

theorem tailTrace_2057906 : CollatzResearch.WordTrace tailWord_2057906 prefixEnd_2057906 704463279847687111340579 := by
  unfold tailWord_2057906
  simp only [CollatzResearch.WordTrace]
  refine ⟨18764499520641374802140393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50038665388376999472374381 18764499520641374802140393)
  ·
    refine ⟨14073374640481031101605295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18764499520641374802140393 14073374640481031101605295)
    ·
      refine ⟨21110061960721546652407943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14073374640481031101605295 21110061960721546652407943)
      ·
        refine ⟨31665092941082319978611915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21110061960721546652407943 31665092941082319978611915)
        ·
          refine ⟨47497639411623479967917873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31665092941082319978611915 47497639411623479967917873)
          ·
            refine ⟨35623229558717609975938405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47497639411623479967917873 35623229558717609975938405)
            ·
              refine ⟨6679355542259551870488451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35623229558717609975938405 6679355542259551870488451)
              ·
                refine ⟨10019033313389327805732677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6679355542259551870488451 10019033313389327805732677)
                ·
                  refine ⟨1878568746260498963574877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10019033313389327805732677 1878568746260498963574877)
                  ·
                    refine ⟨704463279847687111340579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1878568746260498963574877 704463279847687111340579)
                    ·
                      rfl

theorem cell22_2057906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_2057906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057906 prefixEnd_2057906 := by exact prefixLift 2057906
  have htrace : WordTrace (prefixWord ++ tailWord_2057906) baseStart_2057906 baseEnd_2057906 := by
    simpa [prefixWord, tailWord_2057906, baseEnd_2057906] using wordTrace_append hprefix tailTrace_2057906
  have hstable : (prefixWord ++ tailWord_2057906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057906).length < 2 ^ (prefixWord ++ tailWord_2057906).sum := by decide
  have hdescent : baseEnd_2057906 < baseStart_2057906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057919 : List Nat := [1, 1, 2, 2, 2, 3, 4, 7]
def baseStart_2057919 : Nat := 118140960795 + 2057919 * 2 ^ 59
def prefixEnd_2057919 : Nat := 4983230072969 + 3 ^ 40 * 2057919 * 2
def baseEnd_2057919 : Nat := 78274192223706601196171

theorem tailTrace_2057919 : CollatzResearch.WordTrace tailWord_2057919 prefixEnd_2057919 78274192223706601196171 := by
  unfold tailWord_2057919
  simp only [CollatzResearch.WordTrace]
  refine ⟨75058472231518402428784811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50038981487678934952523207 75058472231518402428784811)
  ·
    refine ⟨112587708347277603643177217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75058472231518402428784811 112587708347277603643177217)
    ·
      refine ⟨84440781260458202732382913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112587708347277603643177217 84440781260458202732382913)
      ·
        refine ⟨63330585945343652049287185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84440781260458202732382913 63330585945343652049287185)
        ·
          refine ⟨47497939459007739036965389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63330585945343652049287185 47497939459007739036965389)
          ·
            refine ⟨17811727297127902138862021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47497939459007739036965389 17811727297127902138862021)
            ·
              refine ⟨3339698868211481651036629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17811727297127902138862021 3339698868211481651036629)
              ·
                refine ⟨78274192223706601196171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3339698868211481651036629 78274192223706601196171)
                ·
                  rfl

theorem cell22_2057919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 7].length) (baseStart_2057919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057919 prefixEnd_2057919 := by exact prefixLift 2057919
  have htrace : WordTrace (prefixWord ++ tailWord_2057919) baseStart_2057919 baseEnd_2057919 := by
    simpa [prefixWord, tailWord_2057919, baseEnd_2057919] using wordTrace_append hprefix tailTrace_2057919
  have hstable : (prefixWord ++ tailWord_2057919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057919).length < 2 ^ (prefixWord ++ tailWord_2057919).sum := by decide
  have hdescent : baseEnd_2057919 < baseStart_2057919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057938 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_2057938 : Nat := 118140960795 + 2057938 * 2 ^ 59
def prefixEnd_2057938 : Nat := 4983230072969 + 3 ^ 40 * 2057938 * 2
def baseEnd_2057938 : Nat := 704474234101649694540481

theorem tailTrace_2057938 : CollatzResearch.WordTrace tailWord_2057938 prefixEnd_2057938 704474234101649694540481 := by
  unfold tailWord_2057938
  simp only [CollatzResearch.WordTrace]
  refine ⟨18764791304612392168431617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50039443478966379115817645 18764791304612392168431617)
  ·
    refine ⟨14073593478459294126323713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18764791304612392168431617 14073593478459294126323713)
    ·
      refine ⟨10555195108844470594742785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14073593478459294126323713 10555195108844470594742785)
      ·
        refine ⟨7916396331633352946057089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10555195108844470594742785 7916396331633352946057089)
        ·
          refine ⟨5937297248725014709542817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7916396331633352946057089 5937297248725014709542817)
          ·
            refine ⟨4452972936543761032157113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5937297248725014709542817 4452972936543761032157113)
            ·
              refine ⟨3339729702407820774117835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4452972936543761032157113 3339729702407820774117835)
              ·
                refine ⟨5009594553611731161176753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339729702407820774117835 5009594553611731161176753)
                ·
                  refine ⟨3757195915208798370882565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5009594553611731161176753 3757195915208798370882565)
                  ·
                    refine ⟨704474234101649694540481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3757195915208798370882565 704474234101649694540481)
                    ·
                      rfl

theorem cell22_2057938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_2057938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057938 prefixEnd_2057938 := by exact prefixLift 2057938
  have htrace : WordTrace (prefixWord ++ tailWord_2057938) baseStart_2057938 baseEnd_2057938 := by
    simpa [prefixWord, tailWord_2057938, baseEnd_2057938] using wordTrace_append hprefix tailTrace_2057938
  have hstable : (prefixWord ++ tailWord_2057938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057938).length < 2 ^ (prefixWord ++ tailWord_2057938).sum := by decide
  have hdescent : baseEnd_2057938 < baseStart_2057938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057959 : List Nat := [1, 1, 5, 4, 2, 1, 2, 2, 4]
def baseStart_2057959 : Nat := 118140960795 + 2057959 * 2 ^ 59
def prefixEnd_2057959 : Nat := 4983230072969 + 3 ^ 40 * 2057959 * 2
def baseEnd_2057959 : Nat := 234827140943604213255139

theorem tailTrace_2057959 : CollatzResearch.WordTrace tailWord_2057959 prefixEnd_2057959 234827140943604213255139 := by
  unfold tailWord_2057959
  simp only [CollatzResearch.WordTrace]
  refine ⟨75059931151373489260240931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50039954100915659506827287 75059931151373489260240931)
  ·
    refine ⟨112589896727060233890361397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75059931151373489260240931 112589896727060233890361397)
    ·
      refine ⟨10555302818161896927221381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112589896727060233890361397 10555302818161896927221381)
      ·
        refine ⟨1979119278405355673854009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10555302818161896927221381 1979119278405355673854009)
        ·
          refine ⟨1484339458804016755390507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1979119278405355673854009 1484339458804016755390507)
          ·
            refine ⟨2226509188206025133085761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484339458804016755390507 2226509188206025133085761)
            ·
              refine ⟨1669881891154518849814321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2226509188206025133085761 1669881891154518849814321)
              ·
                refine ⟨1252411418365889137360741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1669881891154518849814321 1252411418365889137360741)
                ·
                  refine ⟨234827140943604213255139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1252411418365889137360741 234827140943604213255139)
                  ·
                    rfl

theorem cell22_2057959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 4].length) (baseStart_2057959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057959 prefixEnd_2057959 := by exact prefixLift 2057959
  have htrace : WordTrace (prefixWord ++ tailWord_2057959) baseStart_2057959 baseEnd_2057959 := by
    simpa [prefixWord, tailWord_2057959, baseEnd_2057959] using wordTrace_append hprefix tailTrace_2057959
  have hstable : (prefixWord ++ tailWord_2057959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057959).length < 2 ^ (prefixWord ++ tailWord_2057959).sum := by decide
  have hdescent : baseEnd_2057959 < baseStart_2057959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057964 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 7]
def baseStart_2057964 : Nat := 118140960795 + 2057964 * 2 ^ 59
def prefixEnd_2057964 : Nat := 4983230072969 + 3 ^ 40 * 2057964 * 2
def baseEnd_2057964 : Nat := 234827711477664764463467

theorem tailTrace_2057964 : CollatzResearch.WordTrace tailWord_2057964 prefixEnd_2057964 234827711477664764463467 := by
  unfold tailWord_2057964
  simp only [CollatzResearch.WordTrace]
  refine ⟨37530056758177687557086473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50040075677570250076115297 37530056758177687557086473)
  ·
    refine ⟨28147542568633265667814855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37530056758177687557086473 28147542568633265667814855)
    ·
      refine ⟨42221313852949898501722283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28147542568633265667814855 42221313852949898501722283)
      ·
        refine ⟨63331970779424847752583425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42221313852949898501722283 63331970779424847752583425)
        ·
          refine ⟨47498978084568635814437569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63331970779424847752583425 47498978084568635814437569)
          ·
            refine ⟨35624233563426476860828177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47498978084568635814437569 35624233563426476860828177)
            ·
              refine ⟨26718175172569857645621133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35624233563426476860828177 26718175172569857645621133)
              ·
                refine ⟨10019315689713696617107925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26718175172569857645621133 10019315689713696617107925)
                ·
                  refine ⟨234827711477664764463467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10019315689713696617107925 234827711477664764463467)
                  ·
                    rfl

theorem cell22_2057964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_2057964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2057964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2057964 prefixEnd_2057964 := by exact prefixLift 2057964
  have htrace : WordTrace (prefixWord ++ tailWord_2057964) baseStart_2057964 baseEnd_2057964 := by
    simpa [prefixWord, tailWord_2057964, baseEnd_2057964] using wordTrace_append hprefix tailTrace_2057964
  have hstable : (prefixWord ++ tailWord_2057964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057964).length < 2 ^ (prefixWord ++ tailWord_2057964).sum := by decide
  have hdescent : baseEnd_2057964 < baseStart_2057964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058002 : List Nat := [3, 2, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2058002 : Nat := 118140960795 + 2058002 * 2 ^ 59
def prefixEnd_2058002 : Nat := 4983230072969 + 3 ^ 40 * 2058002 * 2
def baseEnd_2058002 : Nat := 704496142609574860940285

theorem tailTrace_2058002 : CollatzResearch.WordTrace tailWord_2058002 prefixEnd_2058002 704496142609574860940285 := by
  unfold tailWord_2058002
  simp only [CollatzResearch.WordTrace]
  refine ⟨18765374872554426901014065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50040999660145138402704173 18765374872554426901014065)
  ·
    refine ⟨14074031154415820175760549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18765374872554426901014065 14074031154415820175760549)
    ·
      refine ⟨2638880841452966282955103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14074031154415820175760549 2638880841452966282955103)
      ·
        refine ⟨3958321262179449424432655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2638880841452966282955103 3958321262179449424432655)
        ·
          refine ⟨5937481893269174136648983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3958321262179449424432655 5937481893269174136648983)
          ·
            refine ⟨8906222839903761204973475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5937481893269174136648983 8906222839903761204973475)
            ·
              refine ⟨13359334259855641807460213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8906222839903761204973475 13359334259855641807460213)
              ·
                refine ⟨1252437586861466419449395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13359334259855641807460213 1252437586861466419449395)
                ·
                  refine ⟨1878656380292199629174093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252437586861466419449395 1878656380292199629174093)
                  ·
                    refine ⟨704496142609574860940285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1878656380292199629174093 704496142609574860940285)
                    ·
                      rfl

theorem cell22_2058002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2058002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058002 prefixEnd_2058002 := by exact prefixLift 2058002
  have htrace : WordTrace (prefixWord ++ tailWord_2058002) baseStart_2058002 baseEnd_2058002 := by
    simpa [prefixWord, tailWord_2058002, baseEnd_2058002] using wordTrace_append hprefix tailTrace_2058002
  have hstable : (prefixWord ++ tailWord_2058002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058002).length < 2 ^ (prefixWord ++ tailWord_2058002).sum := by decide
  have hdescent : baseEnd_2058002 < baseStart_2058002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058011 : List Nat := [1, 1, 1, 1, 1, 1, 4, 7, 1, 4]
def baseStart_2058011 : Nat := 118140960795 + 2058011 * 2 ^ 59
def prefixEnd_2058011 : Nat := 4983230072969 + 3 ^ 40 * 2058011 * 2
def baseEnd_2058011 : Nat := 704499223493501837465257

theorem tailTrace_2058011 : CollatzResearch.WordTrace tailWord_2058011 prefixEnd_2058011 704499223493501837465257 := by
  unfold tailWord_2058011
  simp only [CollatzResearch.WordTrace]
  refine ⟨75061827747185102141133887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50041218498123401427422591 75061827747185102141133887)
  ·
    refine ⟨112592741620777653211700831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75061827747185102141133887 112592741620777653211700831)
    ·
      refine ⟨168889112431166479817551247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112592741620777653211700831 168889112431166479817551247)
      ·
        refine ⟨253333668646749719726326871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168889112431166479817551247 253333668646749719726326871)
        ·
          refine ⟨380000502970124579589490307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253333668646749719726326871 380000502970124579589490307)
          ·
            refine ⟨570000754455186869384235461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380000502970124579589490307 570000754455186869384235461)
            ·
              refine ⟨106875141460347538009544149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 570000754455186869384235461 106875141460347538009544149)
              ·
                refine ⟨2504886127976895422098691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 106875141460347538009544149 2504886127976895422098691)
                ·
                  refine ⟨3757329191965343133148037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504886127976895422098691 3757329191965343133148037)
                  ·
                    refine ⟨704499223493501837465257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3757329191965343133148037 704499223493501837465257)
                    ·
                      rfl

theorem cell22_2058011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 4].length) (baseStart_2058011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058011 prefixEnd_2058011 := by exact prefixLift 2058011
  have htrace : WordTrace (prefixWord ++ tailWord_2058011) baseStart_2058011 baseEnd_2058011 := by
    simpa [prefixWord, tailWord_2058011, baseEnd_2058011] using wordTrace_append hprefix tailTrace_2058011
  have hstable : (prefixWord ++ tailWord_2058011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058011).length < 2 ^ (prefixWord ++ tailWord_2058011).sum := by decide
  have hdescent : baseEnd_2058011 < baseStart_2058011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058045 : List Nat := [1, 4, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_2058045 : Nat := 118140960795 + 2058045 * 2 ^ 59
def prefixEnd_2058045 : Nat := 4983230072969 + 3 ^ 40 * 2058045 * 2
def baseEnd_2058045 : Nat := 704510862388337082115153

theorem tailTrace_2058045 : CollatzResearch.WordTrace tailWord_2058045 prefixEnd_2058045 704510862388337082115153 := by
  unfold tailWord_2058045
  simp only [CollatzResearch.WordTrace]
  refine ⟨75063067829061925947871589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50042045219374617298581059 75063067829061925947871589)
  ·
    refine ⟨14074325217949111115225923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75063067829061925947871589 14074325217949111115225923)
    ·
      refine ⟨21111487826923666672838885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14074325217949111115225923 21111487826923666672838885)
      ·
        refine ⟨3958403967548187501157291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21111487826923666672838885 3958403967548187501157291)
        ·
          refine ⟨5937605951322281251735937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3958403967548187501157291 5937605951322281251735937)
          ·
            refine ⟨4453204463491710938801953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5937605951322281251735937 4453204463491710938801953)
            ·
              refine ⟨3339903347618783204101465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4453204463491710938801953 3339903347618783204101465)
              ·
                refine ⟨2504927510714087403076099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3339903347618783204101465 2504927510714087403076099)
                ·
                  refine ⟨3757391266071131104614149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504927510714087403076099 3757391266071131104614149)
                  ·
                    refine ⟨704510862388337082115153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3757391266071131104614149 704510862388337082115153)
                    ·
                      rfl

theorem cell22_2058045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_2058045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058045 prefixEnd_2058045 := by exact prefixLift 2058045
  have htrace : WordTrace (prefixWord ++ tailWord_2058045) baseStart_2058045 baseEnd_2058045 := by
    simpa [prefixWord, tailWord_2058045, baseEnd_2058045] using wordTrace_append hprefix tailTrace_2058045
  have hstable : (prefixWord ++ tailWord_2058045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058045).length < 2 ^ (prefixWord ++ tailWord_2058045).sum := by decide
  have hdescent : baseEnd_2058045 < baseStart_2058045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058056 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 1, 6]
def baseStart_2058056 : Nat := 118140960795 + 2058056 * 2 ^ 59
def prefixEnd_2058056 : Nat := 4983230072969 + 3 ^ 40 * 2058056 * 2
def baseEnd_2058056 : Nat := 704514627913136720090119

theorem tailTrace_2058056 : CollatzResearch.WordTrace tailWord_2058056 prefixEnd_2058056 704514627913136720090119 := by
  unfold tailWord_2058056
  simp only [CollatzResearch.WordTrace]
  refine ⟨37531734516011037413261011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50042312688014716551014681 37531734516011037413261011)
  ·
    refine ⟨56297601774016556119891517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37531734516011037413261011 56297601774016556119891517)
    ·
      refine ⟨21111600665256208544959319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56297601774016556119891517 21111600665256208544959319)
      ·
        refine ⟨31667400997884312817438979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21111600665256208544959319 31667400997884312817438979)
        ·
          refine ⟨47501101496826469226158469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31667400997884312817438979 47501101496826469226158469)
          ·
            refine ⟨8906456530654962979904713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47501101496826469226158469 8906456530654962979904713)
            ·
              refine ⟨6679842397991222234928535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8906456530654962979904713 6679842397991222234928535)
              ·
                refine ⟨10019763596986833352392803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6679842397991222234928535 10019763596986833352392803)
                ·
                  refine ⟨15029645395480250028589205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10019763596986833352392803 15029645395480250028589205)
                  ·
                    refine ⟨704514627913136720090119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15029645395480250028589205 704514627913136720090119)
                    ·
                      rfl

theorem cell22_2058056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_2058056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058056 prefixEnd_2058056 := by exact prefixLift 2058056
  have htrace : WordTrace (prefixWord ++ tailWord_2058056) baseStart_2058056 baseEnd_2058056 := by
    simpa [prefixWord, tailWord_2058056, baseEnd_2058056] using wordTrace_append hprefix tailTrace_2058056
  have hstable : (prefixWord ++ tailWord_2058056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058056).length < 2 ^ (prefixWord ++ tailWord_2058056).sum := by decide
  have hdescent : baseEnd_2058056 < baseStart_2058056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058092 : List Nat := [2, 2, 1, 1, 4, 4, 2, 1, 2, 3]
def baseStart_2058092 : Nat := 118140960795 + 2058092 * 2 ^ 59
def prefixEnd_2058092 : Nat := 4983230072969 + 3 ^ 40 * 2058092 * 2
def baseEnd_2058092 : Nat := 704526951448844626190009

theorem tailTrace_2058092 : CollatzResearch.WordTrace tailWord_2058092 prefixEnd_2058092 704526951448844626190009 := by
  unfold tailWord_2058092
  simp only [CollatzResearch.WordTrace]
  refine ⟨37532391029945826487416265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50043188039927768649888353 37532391029945826487416265)
  ·
    refine ⟨28149293272459369865562199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37532391029945826487416265 28149293272459369865562199)
    ·
      refine ⟨42223939908689054798343299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28149293272459369865562199 42223939908689054798343299)
      ·
        refine ⟨63335909863033582197514949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42223939908689054798343299 63335909863033582197514949)
        ·
          refine ⟨11875483099318796662034053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63335909863033582197514949 11875483099318796662034053)
          ·
            refine ⟨2226653081122274374131385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11875483099318796662034053 2226653081122274374131385)
            ·
              refine ⟨1669989810841705780598539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2226653081122274374131385 1669989810841705780598539)
              ·
                refine ⟨2504984716262558670897809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669989810841705780598539 2504984716262558670897809)
                ·
                  refine ⟨1878738537196919003173357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2504984716262558670897809 1878738537196919003173357)
                  ·
                    refine ⟨704526951448844626190009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1878738537196919003173357 704526951448844626190009)
                    ·
                      rfl

theorem cell22_2058092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_2058092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058092 prefixEnd_2058092 := by exact prefixLift 2058092
  have htrace : WordTrace (prefixWord ++ tailWord_2058092) baseStart_2058092 baseEnd_2058092 := by
    simpa [prefixWord, tailWord_2058092, baseEnd_2058092] using wordTrace_append hprefix tailTrace_2058092
  have hstable : (prefixWord ++ tailWord_2058092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058092).length < 2 ^ (prefixWord ++ tailWord_2058092).sum := by decide
  have hdescent : baseEnd_2058092 < baseStart_2058092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058116 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 9]
def baseStart_2058116 : Nat := 118140960795 + 2058116 * 2 ^ 59
def prefixEnd_2058116 : Nat := 4983230072969 + 3 ^ 40 * 2058116 * 2
def baseEnd_2058116 : Nat := 234845055713105521196645

theorem tailTrace_2058116 : CollatzResearch.WordTrace tailWord_2058116 prefixEnd_2058116 234845055713105521196645 := by
  unfold tailWord_2058116
  simp only [CollatzResearch.WordTrace]
  refine ⟨37532828705902352536853101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50043771607869803382470801 37532828705902352536853101)
  ·
    refine ⟨14074810764713382201319913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37532828705902352536853101 14074810764713382201319913)
    ·
      refine ⟨10556108073535036650989935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14074810764713382201319913 10556108073535036650989935)
      ·
        refine ⟨15834162110302554976484903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10556108073535036650989935 15834162110302554976484903)
        ·
          refine ⟨23751243165453832464727355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15834162110302554976484903 23751243165453832464727355)
          ·
            refine ⟨35626864748180748697091033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23751243165453832464727355 35626864748180748697091033)
            ·
              refine ⟨26720148561135561522818275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35626864748180748697091033 26720148561135561522818275)
              ·
                refine ⟨40080222841703342284227413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26720148561135561522818275 40080222841703342284227413)
                ·
                  refine ⟨234845055713105521196645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40080222841703342284227413 234845055713105521196645)
                  ·
                    rfl

theorem cell22_2058116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_2058116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058116 prefixEnd_2058116 := by exact prefixLift 2058116
  have htrace : WordTrace (prefixWord ++ tailWord_2058116) baseStart_2058116 baseEnd_2058116 := by
    simpa [prefixWord, tailWord_2058116, baseEnd_2058116] using wordTrace_append hprefix tailTrace_2058116
  have hstable : (prefixWord ++ tailWord_2058116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058116).length < 2 ^ (prefixWord ++ tailWord_2058116).sum := by decide
  have hdescent : baseEnd_2058116 < baseStart_2058116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058133 : List Nat := [1, 3, 2, 1, 1, 3, 4, 2, 5]
def baseStart_2058133 : Nat := 118140960795 + 2058133 * 2 ^ 59
def prefixEnd_2058133 : Nat := 4983230072969 + 3 ^ 40 * 2058133 * 2
def baseEnd_2058133 : Nat := 234846995528911395304961

theorem tailTrace_2058133 : CollatzResearch.WordTrace tailWord_2058133 prefixEnd_2058133 234846995528911395304961 := by
  unfold tailWord_2058133
  simp only [CollatzResearch.WordTrace]
  refine ⟨75066277452743116977075053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50044184968495411318050035 75066277452743116977075053)
  ·
    refine ⟨28149854044778668866403145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75066277452743116977075053 28149854044778668866403145)
    ·
      refine ⟨21112390533584001649802359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28149854044778668866403145 21112390533584001649802359)
      ·
        refine ⟨31668585800376002474703539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21112390533584001649802359 31668585800376002474703539)
        ·
          refine ⟨47502878700564003712055309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31668585800376002474703539 47502878700564003712055309)
          ·
            refine ⟨17813579512711501392020741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47502878700564003712055309 17813579512711501392020741)
            ·
              refine ⟨3340046158633406511003889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17813579512711501392020741 3340046158633406511003889)
              ·
                refine ⟨2505034618975054883252917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340046158633406511003889 2505034618975054883252917)
                ·
                  refine ⟨234846995528911395304961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2505034618975054883252917 234846995528911395304961)
                  ·
                    rfl

theorem cell22_2058133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_2058133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058133 prefixEnd_2058133 := by exact prefixLift 2058133
  have htrace : WordTrace (prefixWord ++ tailWord_2058133) baseStart_2058133 baseEnd_2058133 := by
    simpa [prefixWord, tailWord_2058133, baseEnd_2058133] using wordTrace_append hprefix tailTrace_2058133
  have hstable : (prefixWord ++ tailWord_2058133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058133).length < 2 ^ (prefixWord ++ tailWord_2058133).sum := by decide
  have hdescent : baseEnd_2058133 < baseStart_2058133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058137 : List Nat := [1, 2, 1, 2, 1, 3, 6, 2, 1, 3]
def baseStart_2058137 : Nat := 118140960795 + 2058137 * 2 ^ 59
def prefixEnd_2058137 : Nat := 4983230072969 + 3 ^ 40 * 2058137 * 2
def baseEnd_2058137 : Nat := 704542355868479508814871

theorem tailTrace_2058137 : CollatzResearch.WordTrace tailWord_2058137 prefixEnd_2058137 704542355868479508814871 := by
  unfold tailWord_2058137
  simp only [CollatzResearch.WordTrace]
  refine ⟨75066423344728625660220665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50044282229819083773480443 75066423344728625660220665)
  ·
    refine ⟨56299817508546469245165499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75066423344728625660220665 56299817508546469245165499)
    ·
      refine ⟨84449726262819703867748249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56299817508546469245165499 84449726262819703867748249)
      ·
        refine ⟨63337294697114777900811187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84449726262819703867748249 63337294697114777900811187)
        ·
          refine ⟨95005942045672166851216781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63337294697114777900811187 95005942045672166851216781)
          ·
            refine ⟨35627228267127062569206293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95005942045672166851216781 35627228267127062569206293)
            ·
              refine ⟨1670026325021581057931545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35627228267127062569206293 1670026325021581057931545)
              ·
                refine ⟨1252519743766185793448659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670026325021581057931545 1252519743766185793448659)
                ·
                  refine ⟨1878779615649278690172989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252519743766185793448659 1878779615649278690172989)
                  ·
                    refine ⟨704542355868479508814871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1878779615649278690172989 704542355868479508814871)
                    ·
                      rfl

theorem cell22_2058137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 1, 3].length) (baseStart_2058137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058137 prefixEnd_2058137 := by exact prefixLift 2058137
  have htrace : WordTrace (prefixWord ++ tailWord_2058137) baseStart_2058137 baseEnd_2058137 := by
    simpa [prefixWord, tailWord_2058137, baseEnd_2058137] using wordTrace_append hprefix tailTrace_2058137
  have hstable : (prefixWord ++ tailWord_2058137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058137).length < 2 ^ (prefixWord ++ tailWord_2058137).sum := by decide
  have hdescent : baseEnd_2058137 < baseStart_2058137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058148 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_2058148 : Nat := 118140960795 + 2058148 * 2 ^ 59
def prefixEnd_2058148 : Nat := 4983230072969 + 3 ^ 40 * 2058148 * 2
def baseEnd_2058148 : Nat := 704546121393279146789837

theorem tailTrace_2058148 : CollatzResearch.WordTrace tailWord_2058148 prefixEnd_2058148 704546121393279146789837 := by
  unfold tailWord_2058148
  simp only [CollatzResearch.WordTrace]
  refine ⟨37533412273844387269435549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50044549698459183025914065 37533412273844387269435549)
  ·
    refine ⟨14075029602691645226038331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37533412273844387269435549 14075029602691645226038331)
    ·
      refine ⟨21112544404037467839057497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14075029602691645226038331 21112544404037467839057497)
      ·
        refine ⟨15834408303028100879293123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21112544404037467839057497 15834408303028100879293123)
        ·
          refine ⟨23751612454542151318939685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15834408303028100879293123 23751612454542151318939685)
          ·
            refine ⟨4453427335226653372301191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23751612454542151318939685 4453427335226653372301191)
            ·
              refine ⟨6680141002839980058451787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453427335226653372301191 6680141002839980058451787)
              ·
                refine ⟨10020211504259970087677681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6680141002839980058451787 10020211504259970087677681)
                ·
                  refine ⟨7515158628194977565758261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10020211504259970087677681 7515158628194977565758261)
                  ·
                    refine ⟨704546121393279146789837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7515158628194977565758261 704546121393279146789837)
                    ·
                      rfl

theorem cell22_2058148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_2058148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058148 prefixEnd_2058148 := by exact prefixLift 2058148
  have htrace : WordTrace (prefixWord ++ tailWord_2058148) baseStart_2058148 baseEnd_2058148 := by
    simpa [prefixWord, tailWord_2058148, baseEnd_2058148] using wordTrace_append hprefix tailTrace_2058148
  have hstable : (prefixWord ++ tailWord_2058148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058148).length < 2 ^ (prefixWord ++ tailWord_2058148).sum := by decide
  have hdescent : baseEnd_2058148 < baseStart_2058148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058163 : List Nat := [1, 1, 1, 2, 3, 1, 4, 4, 1, 4]
def baseStart_2058163 : Nat := 118140960795 + 2058163 * 2 ^ 59
def prefixEnd_2058163 : Nat := 4983230072969 + 3 ^ 40 * 2058163 * 2
def baseEnd_2058163 : Nat := 704551256199824107664791

theorem tailTrace_2058163 : CollatzResearch.WordTrace tailWord_2058163 prefixEnd_2058163 704551256199824107664791 := by
  unfold tailWord_2058163
  simp only [CollatzResearch.WordTrace]
  refine ⟨75067371642634432100667143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50044914428422954733778095 75067371642634432100667143)
  ·
    refine ⟨112601057463951648151000715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75067371642634432100667143 112601057463951648151000715)
    ·
      refine ⟨168901586195927472226501073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112601057463951648151000715 168901586195927472226501073)
      ·
        refine ⟨126676189646945604169875805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168901586195927472226501073 126676189646945604169875805)
        ·
          refine ⟨47503571117604601563703427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126676189646945604169875805 47503571117604601563703427)
          ·
            refine ⟨71255356676406902345555141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47503571117604601563703427 71255356676406902345555141)
            ·
              refine ⟨13360379376826294189791589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71255356676406902345555141 13360379376826294189791589)
              ·
                refine ⟨2505071133154930160585923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13360379376826294189791589 2505071133154930160585923)
                ·
                  refine ⟨3757606699732395240878885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505071133154930160585923 3757606699732395240878885)
                  ·
                    refine ⟨704551256199824107664791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3757606699732395240878885 704551256199824107664791)
                    ·
                      rfl

theorem cell22_2058163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 4].length) (baseStart_2058163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058163 prefixEnd_2058163 := by exact prefixLift 2058163
  have htrace : WordTrace (prefixWord ++ tailWord_2058163) baseStart_2058163 baseEnd_2058163 := by
    simpa [prefixWord, tailWord_2058163, baseEnd_2058163] using wordTrace_append hprefix tailTrace_2058163
  have hstable : (prefixWord ++ tailWord_2058163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058163).length < 2 ^ (prefixWord ++ tailWord_2058163).sum := by decide
  have hdescent : baseEnd_2058163 < baseStart_2058163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058261 : List Nat := [1, 3, 2, 1, 6, 1, 2, 1, 2, 3]
def baseStart_2058261 : Nat := 118140960795 + 2058261 * 2 ^ 59
def prefixEnd_2058261 : Nat := 4983230072969 + 3 ^ 40 * 2058261 * 2
def baseEnd_2058261 : Nat := 704584803602584518714491

theorem tailTrace_2058261 : CollatzResearch.WordTrace tailWord_2058261 prefixEnd_2058261 704584803602584518714491 := by
  unfold tailWord_2058261
  simp only [CollatzResearch.WordTrace]
  refine ⟨75070945996279394837734637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50047297330852929891823091 75070945996279394837734637)
  ·
    refine ⟨28151604748604773064150489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75070945996279394837734637 28151604748604773064150489)
    ·
      refine ⟨21113703561453579798112867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28151604748604773064150489 21113703561453579798112867)
      ·
        refine ⟨31670555342180369697169301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21113703561453579798112867 31670555342180369697169301)
        ·
          refine ⟨1484557281664704829554811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31670555342180369697169301 1484557281664704829554811)
          ·
            refine ⟨2226835922497057244332217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484557281664704829554811 2226835922497057244332217)
            ·
              refine ⟨1670126941872792933249163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2226835922497057244332217 1670126941872792933249163)
              ·
                refine ⟨2505190412809189399873745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670126941872792933249163 2505190412809189399873745)
                ·
                  refine ⟨1878892809606892049905309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2505190412809189399873745 1878892809606892049905309)
                  ·
                    refine ⟨704584803602584518714491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1878892809606892049905309 704584803602584518714491)
                    ·
                      rfl

theorem cell22_2058261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_2058261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058261 prefixEnd_2058261 := by exact prefixLift 2058261
  have htrace : WordTrace (prefixWord ++ tailWord_2058261) baseStart_2058261 baseEnd_2058261 := by
    simpa [prefixWord, tailWord_2058261, baseEnd_2058261] using wordTrace_append hprefix tailTrace_2058261
  have hstable : (prefixWord ++ tailWord_2058261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058261).length < 2 ^ (prefixWord ++ tailWord_2058261).sum := by decide
  have hdescent : baseEnd_2058261 < baseStart_2058261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058313 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 6]
def baseStart_2058313 : Nat := 118140960795 + 2058313 * 2 ^ 59
def prefixEnd_2058313 : Nat := 4983230072969 + 3 ^ 40 * 2058313 * 2
def baseEnd_2058313 : Nat := 234867534755091238804777

theorem tailTrace_2058313 : CollatzResearch.WordTrace tailWord_2058313 prefixEnd_2058313 234867534755091238804777 := by
  unfold tailWord_2058313
  simp only [CollatzResearch.WordTrace]
  refine ⟨75072842592091007718627593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50048561728060671812418395 75072842592091007718627593)
  ·
    refine ⟨56304631944068255788970695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75072842592091007718627593 56304631944068255788970695)
    ·
      refine ⟨84456947916102383683456043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56304631944068255788970695 84456947916102383683456043)
      ·
        refine ⟨126685421874153575525184065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84456947916102383683456043 126685421874153575525184065)
        ·
          refine ⟨95014066405615181643888049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126685421874153575525184065 95014066405615181643888049)
          ·
            refine ⟨71260549804211386232916037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95014066405615181643888049 71260549804211386232916037)
            ·
              refine ⟨13361353088289634918671757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71260549804211386232916037 13361353088289634918671757)
              ·
                refine ⟨5010507408108613094501909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13361353088289634918671757 5010507408108613094501909)
                ·
                  refine ⟨234867534755091238804777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5010507408108613094501909 234867534755091238804777)
                  ·
                    rfl

theorem cell22_2058313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_2058313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058313 prefixEnd_2058313 := by exact prefixLift 2058313
  have htrace : WordTrace (prefixWord ++ tailWord_2058313) baseStart_2058313 baseEnd_2058313 := by
    simpa [prefixWord, tailWord_2058313, baseEnd_2058313] using wordTrace_append hprefix tailTrace_2058313
  have hstable : (prefixWord ++ tailWord_2058313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058313).length < 2 ^ (prefixWord ++ tailWord_2058313).sum := by decide
  have hdescent : baseEnd_2058313 < baseStart_2058313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058345 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 4, 3]
def baseStart_2058345 : Nat := 118140960795 + 2058345 * 2 ^ 59
def prefixEnd_2058345 : Nat := 4983230072969 + 3 ^ 40 * 2058345 * 2
def baseEnd_2058345 : Nat := 704613558519236299614233

theorem tailTrace_2058345 : CollatzResearch.WordTrace tailWord_2058345 prefixEnd_2058345 704613558519236299614233 := by
  unfold tailWord_2058345
  simp only [CollatzResearch.WordTrace]
  refine ⟨75074009727975077183792489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50049339818650051455861659 75074009727975077183792489)
  ·
    refine ⟨56305507295981307887844367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75074009727975077183792489 56305507295981307887844367)
    ·
      refine ⟨84458260943971961831766551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56305507295981307887844367 84458260943971961831766551)
      ·
        refine ⟨126687391415957942747649827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84458260943971961831766551 126687391415957942747649827)
        ·
          refine ⟨190031087123936914121474741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126687391415957942747649827 190031087123936914121474741)
          ·
            refine ⟨17815414417869085698888257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190031087123936914121474741 17815414417869085698888257)
            ·
              refine ⟨13361560813401814274166193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17815414417869085698888257 13361560813401814274166193)
              ·
                refine ⟨10021170610051360705624645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13361560813401814274166193 10021170610051360705624645)
                ·
                  refine ⟨1878969489384630132304621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10021170610051360705624645 1878969489384630132304621)
                  ·
                    refine ⟨704613558519236299614233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1878969489384630132304621 704613558519236299614233)
                    ·
                      rfl

theorem cell22_2058345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 3].length) (baseStart_2058345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058345 prefixEnd_2058345 := by exact prefixLift 2058345
  have htrace : WordTrace (prefixWord ++ tailWord_2058345) baseStart_2058345 baseEnd_2058345 := by
    simpa [prefixWord, tailWord_2058345, baseEnd_2058345] using wordTrace_append hprefix tailTrace_2058345
  have hstable : (prefixWord ++ tailWord_2058345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058345).length < 2 ^ (prefixWord ++ tailWord_2058345).sum := by decide
  have hdescent : baseEnd_2058345 < baseStart_2058345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058398 : List Nat := [4, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_2058398 : Nat := 118140960795 + 2058398 * 2 ^ 59
def prefixEnd_2058398 : Nat := 4983230072969 + 3 ^ 40 * 2058398 * 2
def baseEnd_2058398 : Nat := 234877233834120609346357

theorem tailTrace_2058398 : CollatzResearch.WordTrace tailWord_2058398 prefixEnd_2058398 234877233834120609346357 := by
  unfold tailWord_2058398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9384492849597883404433981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50050628531188711490314565 9384492849597883404433981)
  ·
    refine ⟨3519184818599206276662743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9384492849597883404433981 3519184818599206276662743)
    ·
      refine ⟨5278777227898809414994115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3519184818599206276662743 5278777227898809414994115)
      ·
        refine ⟨7918165841848214122491173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5278777227898809414994115 7918165841848214122491173)
        ·
          refine ⟨1484656095346540147967095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7918165841848214122491173 1484656095346540147967095)
          ·
            refine ⟨2226984143019810221950643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484656095346540147967095 2226984143019810221950643)
            ·
              refine ⟨3340476214529715332925965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226984143019810221950643 3340476214529715332925965)
              ·
                refine ⟨1252678580448643249847237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3340476214529715332925965 1252678580448643249847237)
                ·
                  refine ⟨234877233834120609346357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1252678580448643249847237 234877233834120609346357)
                  ·
                    rfl

theorem cell22_2058398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_2058398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058398 prefixEnd_2058398 := by exact prefixLift 2058398
  have htrace : WordTrace (prefixWord ++ tailWord_2058398) baseStart_2058398 baseEnd_2058398 := by
    simpa [prefixWord, tailWord_2058398, baseEnd_2058398] using wordTrace_append hprefix tailTrace_2058398
  have hstable : (prefixWord ++ tailWord_2058398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058398).length < 2 ^ (prefixWord ++ tailWord_2058398).sum := by decide
  have hdescent : baseEnd_2058398 < baseStart_2058398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058437 : List Nat := [1, 3, 1, 1, 1, 1, 8, 1, 5]
def baseStart_2058437 : Nat := 118140960795 + 2058437 * 2 ^ 59
def prefixEnd_2058437 : Nat := 4983230072969 + 3 ^ 40 * 2058437 * 2
def baseEnd_2058437 : Nat := 234881683999792908771317

theorem tailTrace_2058437 : CollatzResearch.WordTrace tailWord_2058437 prefixEnd_2058437 234881683999792908771317 := by
  unfold tailWord_2058437
  simp only [CollatzResearch.WordTrace]
  refine ⟨75077365243641776896141565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50051576829094517930761043 75077365243641776896141565)
  ·
    refine ⟨28154011966365666336053087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75077365243641776896141565 28154011966365666336053087)
    ·
      refine ⟨42231017949548499504079631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28154011966365666336053087 42231017949548499504079631)
      ·
        refine ⟨63346526924322749256119447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42231017949548499504079631 63346526924322749256119447)
        ·
          refine ⟨95019790386484123884179171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63346526924322749256119447 95019790386484123884179171)
          ·
            refine ⟨142529685579726185826268757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95019790386484123884179171 142529685579726185826268757)
            ·
              refine ⟨1670269752887416240151587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 142529685579726185826268757 1670269752887416240151587)
              ·
                refine ⟨2505404629331124360227381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670269752887416240151587 2505404629331124360227381)
                ·
                  refine ⟨234881683999792908771317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2505404629331124360227381 234881683999792908771317)
                  ·
                    rfl

theorem cell22_2058437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_2058437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058437 prefixEnd_2058437 := by exact prefixLift 2058437
  have htrace : WordTrace (prefixWord ++ tailWord_2058437) baseStart_2058437 baseEnd_2058437 := by
    simpa [prefixWord, tailWord_2058437, baseEnd_2058437] using wordTrace_append hprefix tailTrace_2058437
  have hstable : (prefixWord ++ tailWord_2058437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058437).length < 2 ^ (prefixWord ++ tailWord_2058437).sum := by decide
  have hdescent : baseEnd_2058437 < baseStart_2058437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058495 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 1, 6]
def baseStart_2058495 : Nat := 118140960795 + 2058495 * 2 ^ 59
def prefixEnd_2058495 : Nat := 4983230072969 + 3 ^ 40 * 2058495 * 2
def baseEnd_2058495 : Nat := 704664906584685908363773

theorem tailTrace_2058495 : CollatzResearch.WordTrace tailWord_2058495 prefixEnd_2058495 704664906584685908363773 := by
  unfold tailWord_2058495
  simp only [CollatzResearch.WordTrace]
  refine ⟨75079480677431652801752939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50052987118287768534501959 75079480677431652801752939)
  ·
    refine ⟨112619221016147479202629409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75079480677431652801752939 112619221016147479202629409)
    ·
      refine ⟨84464415762110609401972057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112619221016147479202629409 84464415762110609401972057)
      ·
        refine ⟨63348311821582957051479043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84464415762110609401972057 63348311821582957051479043)
        ·
          refine ⟨95022467732374435577218565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63348311821582957051479043 95022467732374435577218565)
          ·
            refine ⟨17816712699820206670728481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95022467732374435577218565 17816712699820206670728481)
            ·
              refine ⟨13362534524865155003046361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17816712699820206670728481 13362534524865155003046361)
              ·
                refine ⟨10021900893648866252284771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13362534524865155003046361 10021900893648866252284771)
                ·
                  refine ⟨15032851340473299378427157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10021900893648866252284771 15032851340473299378427157)
                  ·
                    refine ⟨704664906584685908363773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15032851340473299378427157 704664906584685908363773)
                    ·
                      rfl

theorem cell22_2058495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_2058495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058495 prefixEnd_2058495 := by exact prefixLift 2058495
  have htrace : WordTrace (prefixWord ++ tailWord_2058495) baseStart_2058495 baseEnd_2058495 := by
    simpa [prefixWord, tailWord_2058495, baseEnd_2058495] using wordTrace_append hprefix tailTrace_2058495
  have hstable : (prefixWord ++ tailWord_2058495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058495).length < 2 ^ (prefixWord ++ tailWord_2058495).sum := by decide
  have hdescent : baseEnd_2058495 < baseStart_2058495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058497 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 1, 5]
def baseStart_2058497 : Nat := 118140960795 + 2058497 * 2 ^ 59
def prefixEnd_2058497 : Nat := 4983230072969 + 3 ^ 40 * 2058497 * 2
def baseEnd_2058497 : Nat := 704665591225558569813767

theorem tailTrace_2058497 : CollatzResearch.WordTrace tailWord_2058497 prefixEnd_2058497 704665591225558569813767 := by
  unfold tailWord_2058497
  simp only [CollatzResearch.WordTrace]
  refine ⟨75079553623424407143325745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50053035748949604762217163 75079553623424407143325745)
  ·
    refine ⟨56309665217568305357494309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75079553623424407143325745 56309665217568305357494309)
    ·
      refine ⟨10558062228294057254530183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56309665217568305357494309 10558062228294057254530183)
      ·
        refine ⟨15837093342441085881795275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10558062228294057254530183 15837093342441085881795275)
        ·
          refine ⟨23755640013661628822692913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15837093342441085881795275 23755640013661628822692913)
          ·
            refine ⟨17816730010246221617019685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23755640013661628822692913 17816730010246221617019685)
            ·
              refine ⟨3340636876921166553191191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17816730010246221617019685 3340636876921166553191191)
              ·
                refine ⟨5010955315381749829786787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3340636876921166553191191 5010955315381749829786787)
                ·
                  refine ⟨7516432973072624744680181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010955315381749829786787 7516432973072624744680181)
                  ·
                    refine ⟨704665591225558569813767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7516432973072624744680181 704665591225558569813767)
                    ·
                      rfl

theorem cell22_2058497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_2058497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058497 prefixEnd_2058497 := by exact prefixLift 2058497
  have htrace : WordTrace (prefixWord ++ tailWord_2058497) baseStart_2058497 baseEnd_2058497 := by
    simpa [prefixWord, tailWord_2058497, baseEnd_2058497] using wordTrace_append hprefix tailTrace_2058497
  have hstable : (prefixWord ++ tailWord_2058497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058497).length < 2 ^ (prefixWord ++ tailWord_2058497).sum := by decide
  have hdescent : baseEnd_2058497 < baseStart_2058497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058540 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_2058540 : Nat := 118140960795 + 2058540 * 2 ^ 59
def prefixEnd_2058540 : Nat := 4983230072969 + 3 ^ 40 * 2058540 * 2
def baseEnd_2058540 : Nat := 704680311004320790988635

theorem tailTrace_2058540 : CollatzResearch.WordTrace tailWord_2058540 prefixEnd_2058540 704680311004320790988635 := by
  unfold tailWord_2058540
  simp only [CollatzResearch.WordTrace]
  refine ⟨37540560981134312743570537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50054081308179083658094049 37540560981134312743570537)
  ·
    refine ⟨28155420735850734557677903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37540560981134312743570537 28155420735850734557677903)
    ·
      refine ⟨42233131103776101836516855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28155420735850734557677903 42233131103776101836516855)
      ·
        refine ⟨63349696655664152754775283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42233131103776101836516855 63349696655664152754775283)
        ·
          refine ⟨95024544983496229132162925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63349696655664152754775283 95024544983496229132162925)
          ·
            refine ⟨35634204368811085924561097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95024544983496229132162925 35634204368811085924561097)
            ·
              refine ⟨26725653276608314443420823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35634204368811085924561097 26725653276608314443420823)
              ·
                refine ⟨40088479914912471665131235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26725653276608314443420823 40088479914912471665131235)
                ·
                  refine ⟨60132719872368707497696853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40088479914912471665131235 60132719872368707497696853)
                  ·
                    refine ⟨704680311004320790988635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60132719872368707497696853 704680311004320790988635)
                    ·
                      rfl

theorem cell22_2058540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_2058540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058540 prefixEnd_2058540 := by exact prefixLift 2058540
  have htrace : WordTrace (prefixWord ++ tailWord_2058540) baseStart_2058540 baseEnd_2058540 := by
    simpa [prefixWord, tailWord_2058540, baseEnd_2058540] using wordTrace_append hprefix tailTrace_2058540
  have hstable : (prefixWord ++ tailWord_2058540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058540).length < 2 ^ (prefixWord ++ tailWord_2058540).sum := by decide
  have hdescent : baseEnd_2058540 < baseStart_2058540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058548 : List Nat := [2, 5, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_2058548 : Nat := 118140960795 + 2058548 * 2 ^ 59
def prefixEnd_2058548 : Nat := 4983230072969 + 3 ^ 40 * 2058548 * 2
def baseEnd_2058548 : Nat := 704683049567811436788611

theorem tailTrace_2058548 : CollatzResearch.WordTrace tailWord_2058548 prefixEnd_2058548 704683049567811436788611 := by
  unfold tailWord_2058548
  simp only [CollatzResearch.WordTrace]
  refine ⟨37540706873119821426716149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50054275830826428568954865 37540706873119821426716149)
  ·
    refine ⟨3519441269354983258754639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37540706873119821426716149 3519441269354983258754639)
    ·
      refine ⟨5279161904032474888131959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3519441269354983258754639 5279161904032474888131959)
      ·
        refine ⟨7918742856048712332197939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5279161904032474888131959 7918742856048712332197939)
        ·
          refine ⟨11878114284073068498296909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7918742856048712332197939 11878114284073068498296909)
          ·
            refine ⟨4454292856527400686861341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11878114284073068498296909 4454292856527400686861341)
            ·
              refine ⟨1670359821197775257573003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4454292856527400686861341 1670359821197775257573003)
              ·
                refine ⟨2505539731796662886359505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670359821197775257573003 2505539731796662886359505)
                ·
                  refine ⟨1879154798847497164769629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2505539731796662886359505 1879154798847497164769629)
                  ·
                    refine ⟨704683049567811436788611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1879154798847497164769629 704683049567811436788611)
                    ·
                      rfl

theorem cell22_2058548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_2058548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058548 prefixEnd_2058548 := by exact prefixLift 2058548
  have htrace : WordTrace (prefixWord ++ tailWord_2058548) baseStart_2058548 baseEnd_2058548 := by
    simpa [prefixWord, tailWord_2058548, baseEnd_2058548] using wordTrace_append hprefix tailTrace_2058548
  have hstable : (prefixWord ++ tailWord_2058548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058548).length < 2 ^ (prefixWord ++ tailWord_2058548).sum := by decide
  have hdescent : baseEnd_2058548 < baseStart_2058548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058561 : List Nat := [1, 2, 5, 2, 2, 2, 2, 6]
def baseStart_2058561 : Nat := 118140960795 + 2058561 * 2 ^ 59
def prefixEnd_2058561 : Nat := 4983230072969 + 3 ^ 40 * 2058561 * 2
def baseEnd_2058561 : Nat := 78298611081498192912619

theorem tailTrace_2058561 : CollatzResearch.WordTrace tailWord_2058561 prefixEnd_2058561 78298611081498192912619 := by
  unfold tailWord_2058561
  simp only [CollatzResearch.WordTrace]
  refine ⟨75081887895192546073655537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50054591930128364049103691 75081887895192546073655537)
  ·
    refine ⟨56311415921394409555241653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75081887895192546073655537 56311415921394409555241653)
    ·
      refine ⟨5279195242630725895803905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56311415921394409555241653 5279195242630725895803905)
      ·
        refine ⟨3959396431973044421852929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5279195242630725895803905 3959396431973044421852929)
        ·
          refine ⟨2969547323979783316389697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3959396431973044421852929 2969547323979783316389697)
          ·
            refine ⟨2227160492984837487292273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2969547323979783316389697 2227160492984837487292273)
            ·
              refine ⟨1670370369738628115469205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227160492984837487292273 1670370369738628115469205)
              ·
                refine ⟨78298611081498192912619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1670370369738628115469205 78298611081498192912619)
                ·
                  rfl

theorem cell22_2058561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 6].length) (baseStart_2058561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058561 prefixEnd_2058561 := by exact prefixLift 2058561
  have htrace : WordTrace (prefixWord ++ tailWord_2058561) baseStart_2058561 baseEnd_2058561 := by
    simpa [prefixWord, tailWord_2058561, baseEnd_2058561] using wordTrace_append hprefix tailTrace_2058561
  have hstable : (prefixWord ++ tailWord_2058561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058561).length < 2 ^ (prefixWord ++ tailWord_2058561).sum := by decide
  have hdescent : baseEnd_2058561 < baseStart_2058561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058576 : List Nat := [2, 1, 1, 1, 1, 6, 3, 3, 1, 3]
def baseStart_2058576 : Nat := 118140960795 + 2058576 * 2 ^ 59
def prefixEnd_2058576 : Nat := 4983230072969 + 3 ^ 40 * 2058576 * 2
def baseEnd_2058576 : Nat := 704692634540028697088525

theorem tailTrace_2058576 : CollatzResearch.WordTrace tailWord_2058576 prefixEnd_2058576 704692634540028697088525 := by
  unfold tailWord_2058576
  simp only [CollatzResearch.WordTrace]
  refine ⟨37541217495069101817725791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50054956660092135756967721 37541217495069101817725791)
  ·
    refine ⟨56311826242603652726588687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37541217495069101817725791 56311826242603652726588687)
    ·
      refine ⟨84467739363905479089883031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56311826242603652726588687 84467739363905479089883031)
      ·
        refine ⟨126701609045858218634824547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84467739363905479089883031 126701609045858218634824547)
        ·
          refine ⟨190052413568787327952236821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126701609045858218634824547 190052413568787327952236821)
          ·
            refine ⟨8908706886036905997761101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190052413568787327952236821 8908706886036905997761101)
            ·
              refine ⟨3340765082263839749160413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8908706886036905997761101 3340765082263839749160413)
              ·
                refine ⟨1252786905848939905935155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3340765082263839749160413 1252786905848939905935155)
                ·
                  refine ⟨1879180358773409858902733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252786905848939905935155 1879180358773409858902733)
                  ·
                    refine ⟨704692634540028697088525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1879180358773409858902733 704692634540028697088525)
                    ·
                      rfl

theorem cell22_2058576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 1, 3].length) (baseStart_2058576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058576 prefixEnd_2058576 := by exact prefixLift 2058576
  have htrace : WordTrace (prefixWord ++ tailWord_2058576) baseStart_2058576 baseEnd_2058576 := by
    simpa [prefixWord, tailWord_2058576, baseEnd_2058576] using wordTrace_append hprefix tailTrace_2058576
  have hstable : (prefixWord ++ tailWord_2058576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058576).length < 2 ^ (prefixWord ++ tailWord_2058576).sum := by decide
  have hdescent : baseEnd_2058576 < baseStart_2058576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058619 : List Nat := [1, 1, 1, 1, 1, 7, 3, 2, 1, 4]
def baseStart_2058619 : Nat := 118140960795 + 2058619 * 2 ^ 59
def prefixEnd_2058619 : Nat := 4983230072969 + 3 ^ 40 * 2058619 * 2
def baseEnd_2058619 : Nat := 704707354318790918263393

theorem tailTrace_2058619 : CollatzResearch.WordTrace tailWord_2058619 prefixEnd_2058619 704707354318790918263393 := by
  unfold tailWord_2058619
  simp only [CollatzResearch.WordTrace]
  refine ⟨75084003328982421979266911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50056002219321614652844607 75084003328982421979266911)
  ·
    refine ⟨112626004993473632968900367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75084003328982421979266911 112626004993473632968900367)
    ·
      refine ⟨168939007490210449453350551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112626004993473632968900367 168939007490210449453350551)
      ·
        refine ⟨253408511235315674180025827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168939007490210449453350551 253408511235315674180025827)
        ·
          refine ⟨380112766852973511270038741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253408511235315674180025827 380112766852973511270038741)
          ·
            refine ⟨8908892973116566670391533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 380112766852973511270038741 8908892973116566670391533)
            ·
              refine ⟨3340834864918712501396825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8908892973116566670391533 3340834864918712501396825)
              ·
                refine ⟨2505626148689034376047619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340834864918712501396825 2505626148689034376047619)
                ·
                  refine ⟨3758439223033551564071429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505626148689034376047619 3758439223033551564071429)
                  ·
                    refine ⟨704707354318790918263393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3758439223033551564071429 704707354318790918263393)
                    ·
                      rfl

theorem cell22_2058619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 4].length) (baseStart_2058619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058619 prefixEnd_2058619 := by exact prefixLift 2058619
  have htrace : WordTrace (prefixWord ++ tailWord_2058619) baseStart_2058619 baseEnd_2058619 := by
    simpa [prefixWord, tailWord_2058619, baseEnd_2058619] using wordTrace_append hprefix tailTrace_2058619
  have hstable : (prefixWord ++ tailWord_2058619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058619).length < 2 ^ (prefixWord ++ tailWord_2058619).sum := by decide
  have hdescent : baseEnd_2058619 < baseStart_2058619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058636 : List Nat := [2, 2, 1, 2, 1, 5, 3, 1, 1, 4]
def baseStart_2058636 : Nat := 118140960795 + 2058636 * 2 ^ 59
def prefixEnd_2058636 : Nat := 4983230072969 + 3 ^ 40 * 2058636 * 2
def baseEnd_2058636 : Nat := 704713173766208540588341

theorem tailTrace_2058636 : CollatzResearch.WordTrace tailWord_2058636 prefixEnd_2058636 704713173766208540588341 := by
  unfold tailWord_2058636
  simp only [CollatzResearch.WordTrace]
  refine ⟨37542311684960416941317881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50056415579947222588423841 37542311684960416941317881)
  ·
    refine ⟨28156733763720312705988411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37542311684960416941317881 28156733763720312705988411)
    ·
      refine ⟨42235100645580469058982617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28156733763720312705988411 42235100645580469058982617)
      ·
        refine ⟨31676325484185351794236963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42235100645580469058982617 31676325484185351794236963)
        ·
          refine ⟨47514488226278027691355445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31676325484185351794236963 47514488226278027691355445)
          ·
            refine ⟨4454483271213565096064573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47514488226278027691355445 4454483271213565096064573)
            ·
              refine ⟨1670431226705086911024215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4454483271213565096064573 1670431226705086911024215)
              ·
                refine ⟨2505646840057630366536323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670431226705086911024215 2505646840057630366536323)
                ·
                  refine ⟨3758470260086445549804485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505646840057630366536323 3758470260086445549804485)
                  ·
                    refine ⟨704713173766208540588341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3758470260086445549804485 704713173766208540588341)
                    ·
                      rfl

theorem cell22_2058636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_2058636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058636 prefixEnd_2058636 := by exact prefixLift 2058636
  have htrace : WordTrace (prefixWord ++ tailWord_2058636) baseStart_2058636 baseEnd_2058636 := by
    simpa [prefixWord, tailWord_2058636, baseEnd_2058636] using wordTrace_append hprefix tailTrace_2058636
  have hstable : (prefixWord ++ tailWord_2058636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058636).length < 2 ^ (prefixWord ++ tailWord_2058636).sum := by decide
  have hdescent : baseEnd_2058636 < baseStart_2058636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058679 : List Nat := [1, 1, 3, 1, 3, 4, 3, 6]
def baseStart_2058679 : Nat := 118140960795 + 2058679 * 2 ^ 59
def prefixEnd_2058679 : Nat := 4983230072969 + 3 ^ 40 * 2058679 * 2
def baseEnd_2058679 : Nat := 78303099282774529084801

theorem tailTrace_2058679 : CollatzResearch.WordTrace tailWord_2058679 prefixEnd_2058679 78303099282774529084801 := by
  unfold tailWord_2058679
  simp only [CollatzResearch.WordTrace]
  refine ⟨75086191708765052226451091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50057461139176701484300727 75086191708765052226451091)
  ·
    refine ⟨112629287563147578339676637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75086191708765052226451091 112629287563147578339676637)
    ·
      refine ⟨42235982836180341877378739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112629287563147578339676637 42235982836180341877378739)
      ·
        refine ⟨63353974254270512816068109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42235982836180341877378739 63353974254270512816068109)
        ·
          refine ⟨23757740345351442306025541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63353974254270512816068109 23757740345351442306025541)
          ·
            refine ⟨4454576314753395432379789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23757740345351442306025541 4454576314753395432379789)
            ·
              refine ⟨1670466118032523287142421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4454576314753395432379789 1670466118032523287142421)
              ·
                refine ⟨78303099282774529084801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1670466118032523287142421 78303099282774529084801)
                ·
                  rfl

theorem cell22_2058679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 6].length) (baseStart_2058679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058679 prefixEnd_2058679 := by exact prefixLift 2058679
  have htrace : WordTrace (prefixWord ++ tailWord_2058679) baseStart_2058679 baseEnd_2058679 := by
    simpa [prefixWord, tailWord_2058679, baseEnd_2058679] using wordTrace_append hprefix tailTrace_2058679
  have hstable : (prefixWord ++ tailWord_2058679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058679).length < 2 ^ (prefixWord ++ tailWord_2058679).sum := by decide
  have hdescent : baseEnd_2058679 < baseStart_2058679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058681 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 2, 4]
def baseStart_2058681 : Nat := 118140960795 + 2058681 * 2 ^ 59
def prefixEnd_2058681 : Nat := 4983230072969 + 3 ^ 40 * 2058681 * 2
def baseEnd_2058681 : Nat := 704728578185843423213203

theorem tailTrace_2058681 : CollatzResearch.WordTrace tailWord_2058681 prefixEnd_2058681 704728578185843423213203 := by
  unfold tailWord_2058681
  simp only [CollatzResearch.WordTrace]
  refine ⟨75086264654757806568023897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50057509769838537712015931 75086264654757806568023897)
  ·
    refine ⟨56314698491068354926017923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75086264654757806568023897 56314698491068354926017923)
    ·
      refine ⟨84472047736602532389026885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56314698491068354926017923 84472047736602532389026885)
      ·
        refine ⟨15838508950612974822942541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84472047736602532389026885 15838508950612974822942541)
        ·
          refine ⟨5939440856479865558603453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15838508950612974822942541 5939440856479865558603453)
          ·
            refine ⟨2227290321179949584476295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5939440856479865558603453 2227290321179949584476295)
            ·
              refine ⟨3340935481769924376714443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227290321179949584476295 3340935481769924376714443)
              ·
                refine ⟨5011403222654886565071665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3340935481769924376714443 5011403222654886565071665)
                ·
                  refine ⟨3758552416991164923803749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5011403222654886565071665 3758552416991164923803749)
                  ·
                    refine ⟨704728578185843423213203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3758552416991164923803749 704728578185843423213203)
                    ·
                      rfl

theorem cell22_2058681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 4].length) (baseStart_2058681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058681 prefixEnd_2058681 := by exact prefixLift 2058681
  have htrace : WordTrace (prefixWord ++ tailWord_2058681) baseStart_2058681 baseEnd_2058681 := by
    simpa [prefixWord, tailWord_2058681, baseEnd_2058681] using wordTrace_append hprefix tailTrace_2058681
  have hstable : (prefixWord ++ tailWord_2058681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058681).length < 2 ^ (prefixWord ++ tailWord_2058681).sum := by decide
  have hdescent : baseEnd_2058681 < baseStart_2058681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058700 : List Nat := [2, 2, 1, 4, 4, 1, 1, 2, 2, 3]
def baseStart_2058700 : Nat := 118140960795 + 2058700 * 2 ^ 59
def prefixEnd_2058700 : Nat := 4983230072969 + 3 ^ 40 * 2058700 * 2
def baseEnd_2058700 : Nat := 704735082274133706988145

theorem tailTrace_2058700 : CollatzResearch.WordTrace tailWord_2058700 prefixEnd_2058700 704735082274133706988145 := by
  unfold tailWord_2058700
  simp only [CollatzResearch.WordTrace]
  refine ⟨37543478820844486406482777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50057971761125981875310369 37543478820844486406482777)
  ·
    refine ⟨28157609115633364804862083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37543478820844486406482777 28157609115633364804862083)
    ·
      refine ⟨42236413673450047207293125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28157609115633364804862083 42236413673450047207293125)
      ·
        refine ⟨7919327563771883851367461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42236413673450047207293125 7919327563771883851367461)
        ·
          refine ⟨1484873918207228222131399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7919327563771883851367461 1484873918207228222131399)
          ·
            refine ⟨2227310877310842333197099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484873918207228222131399 2227310877310842333197099)
            ·
              refine ⟨3340966315966263499795649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227310877310842333197099 3340966315966263499795649)
              ·
                refine ⟨2505724736974697624846737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340966315966263499795649 2505724736974697624846737)
                ·
                  refine ⟨1879293552731023218635053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2505724736974697624846737 1879293552731023218635053)
                  ·
                    refine ⟨704735082274133706988145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1879293552731023218635053 704735082274133706988145)
                    ·
                      rfl

theorem cell22_2058700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_2058700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058700 prefixEnd_2058700 := by exact prefixLift 2058700
  have htrace : WordTrace (prefixWord ++ tailWord_2058700) baseStart_2058700 baseEnd_2058700 := by
    simpa [prefixWord, tailWord_2058700, baseEnd_2058700] using wordTrace_append hprefix tailTrace_2058700
  have hstable : (prefixWord ++ tailWord_2058700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058700).length < 2 ^ (prefixWord ++ tailWord_2058700).sum := by decide
  have hdescent : baseEnd_2058700 < baseStart_2058700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058775 : List Nat := [1, 1, 3, 6, 1, 2, 2, 1, 5]
def baseStart_2058775 : Nat := 118140960795 + 2058775 * 2 ^ 59
def prefixEnd_2058775 : Nat := 4983230072969 + 3 ^ 40 * 2058775 * 2
def baseEnd_2058775 : Nat := 234920252102286170454305

theorem tailTrace_2058775 : CollatzResearch.WordTrace tailWord_2058775 prefixEnd_2058775 234920252102286170454305 := by
  unfold tailWord_2058775
  simp only [CollatzResearch.WordTrace]
  refine ⟨75089693116417260621945779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50059795410944840414630519 75089693116417260621945779)
  ·
    refine ⟨112634539674625890932918669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75089693116417260621945779 112634539674625890932918669)
    ·
      refine ⟨42237952377984709099844501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112634539674625890932918669 42237952377984709099844501)
      ·
        refine ⟨1979904017718033239055211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42237952377984709099844501 1979904017718033239055211)
        ·
          refine ⟨2969856026577049858582817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979904017718033239055211 2969856026577049858582817)
          ·
            refine ⟨2227392019932787393937113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2969856026577049858582817 2227392019932787393937113)
            ·
              refine ⟨1670544014949590545452835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227392019932787393937113 1670544014949590545452835)
              ·
                refine ⟨2505816022424385818179253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670544014949590545452835 2505816022424385818179253)
                ·
                  refine ⟨234920252102286170454305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2505816022424385818179253 234920252102286170454305)
                  ·
                    rfl

theorem cell22_2058775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 5].length) (baseStart_2058775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058775 prefixEnd_2058775 := by exact prefixLift 2058775
  have htrace : WordTrace (prefixWord ++ tailWord_2058775) baseStart_2058775 baseEnd_2058775 := by
    simpa [prefixWord, tailWord_2058775, baseEnd_2058775] using wordTrace_append hprefix tailTrace_2058775
  have hstable : (prefixWord ++ tailWord_2058775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058775).length < 2 ^ (prefixWord ++ tailWord_2058775).sum := by decide
  have hdescent : baseEnd_2058775 < baseStart_2058775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058788 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_2058788 : Nat := 118140960795 + 2058788 * 2 ^ 59
def prefixEnd_2058788 : Nat := 4983230072969 + 3 ^ 40 * 2058788 * 2
def baseEnd_2058788 : Nat := 704765206472530810787875

theorem tailTrace_2058788 : CollatzResearch.WordTrace tailWord_2058788 prefixEnd_2058788 704765206472530810787875 := by
  unfold tailWord_2058788
  simp only [CollatzResearch.WordTrace]
  refine ⟨37545083632685081921084509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50060111510246775894779345 37545083632685081921084509)
  ·
    refine ⟨14079406362256905720406691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37545083632685081921084509 14079406362256905720406691)
    ·
      refine ⟨21119109543385358580610037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14079406362256905720406691 21119109543385358580610037)
      ·
        refine ⟨1979916519692377366932191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21119109543385358580610037 1979916519692377366932191)
        ·
          refine ⟨2969874779538566050398287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979916519692377366932191 2969874779538566050398287)
          ·
            refine ⟨4454812169307849075597431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969874779538566050398287 4454812169307849075597431)
            ·
              refine ⟨6682218253961773613396147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4454812169307849075597431 6682218253961773613396147)
              ·
                refine ⟨10023327380942660420094221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6682218253961773613396147 10023327380942660420094221)
                ·
                  refine ⟨3758747767853497657535333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10023327380942660420094221 3758747767853497657535333)
                  ·
                    refine ⟨704765206472530810787875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3758747767853497657535333 704765206472530810787875)
                    ·
                      rfl

theorem cell22_2058788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_2058788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058788 prefixEnd_2058788 := by exact prefixLift 2058788
  have htrace : WordTrace (prefixWord ++ tailWord_2058788) baseStart_2058788 baseEnd_2058788 := by
    simpa [prefixWord, tailWord_2058788, baseEnd_2058788] using wordTrace_append hprefix tailTrace_2058788
  have hstable : (prefixWord ++ tailWord_2058788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058788).length < 2 ^ (prefixWord ++ tailWord_2058788).sum := by decide
  have hdescent : baseEnd_2058788 < baseStart_2058788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058863 : List Nat := [1, 1, 2, 1, 3, 2, 3, 5, 1, 3]
def baseStart_2058863 : Nat := 118140960795 + 2058863 * 2 ^ 59
def prefixEnd_2058863 : Nat := 4983230072969 + 3 ^ 40 * 2058863 * 2
def baseEnd_2058863 : Nat := 704790880505255615162645

theorem tailTrace_2058863 : CollatzResearch.WordTrace tailWord_2058863 prefixEnd_2058863 704790880505255615162645 := by
  unfold tailWord_2058863
  simp only [CollatzResearch.WordTrace]
  refine ⟨75092902740098451651149243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50061935160065634434099495 75092902740098451651149243)
  ·
    refine ⟨112639354110147677476723865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75092902740098451651149243 112639354110147677476723865)
    ·
      refine ⟨84479515582610758107542899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112639354110147677476723865 84479515582610758107542899)
      ·
        refine ⟨126719273373916137161314349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84479515582610758107542899 126719273373916137161314349)
        ·
          refine ⟨47519727515218551435492881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126719273373916137161314349 47519727515218551435492881)
          ·
            refine ⟨35639795636413913576619661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47519727515218551435492881 35639795636413913576619661)
            ·
              refine ⟨13364923363655217591232373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35639795636413913576619661 13364923363655217591232373)
              ·
                refine ⟨1252961565342676649178035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13364923363655217591232373 1252961565342676649178035)
                ·
                  refine ⟨1879442348014014973767053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252961565342676649178035 1879442348014014973767053)
                  ·
                    refine ⟨704790880505255615162645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1879442348014014973767053 704790880505255615162645)
                    ·
                      rfl

theorem cell22_2058863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 1, 3].length) (baseStart_2058863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058863 prefixEnd_2058863 := by exact prefixLift 2058863
  have htrace : WordTrace (prefixWord ++ tailWord_2058863) baseStart_2058863 baseEnd_2058863 := by
    simpa [prefixWord, tailWord_2058863, baseEnd_2058863] using wordTrace_append hprefix tailTrace_2058863
  have hstable : (prefixWord ++ tailWord_2058863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058863).length < 2 ^ (prefixWord ++ tailWord_2058863).sum := by decide
  have hdescent : baseEnd_2058863 < baseStart_2058863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058876 : List Nat := [2, 2, 2, 1, 1, 2, 5, 2, 5]
def baseStart_2058876 : Nat := 118140960795 + 2058876 * 2 ^ 59
def prefixEnd_2058876 : Nat := 4983230072969 + 3 ^ 40 * 2058876 * 2
def baseEnd_2058876 : Nat := 234931776890309304862535

theorem tailTrace_2058876 : CollatzResearch.WordTrace tailWord_2058876 prefixEnd_2058876 234931776890309304862535 := by
  unfold tailWord_2058876
  simp only [CollatzResearch.WordTrace]
  refine ⟨37546688444525677435686241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50062251259367569914248321 37546688444525677435686241)
  ·
    refine ⟨28160016333394258076764681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37546688444525677435686241 28160016333394258076764681)
    ·
      refine ⟨21120012250045693557573511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28160016333394258076764681 21120012250045693557573511)
      ·
        refine ⟨31680018375068540336360267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21120012250045693557573511 31680018375068540336360267)
        ·
          refine ⟨47520027562602810504540401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31680018375068540336360267 47520027562602810504540401)
          ·
            refine ⟨35640020671952107878405301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47520027562602810504540401 35640020671952107878405301)
            ·
              refine ⟨3341251937995510113600497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35640020671952107878405301 3341251937995510113600497)
              ·
                refine ⟨2505938953496632585200373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3341251937995510113600497 2505938953496632585200373)
                ·
                  refine ⟨234931776890309304862535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2505938953496632585200373 234931776890309304862535)
                  ·
                    rfl

theorem cell22_2058876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_2058876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058876 prefixEnd_2058876 := by exact prefixLift 2058876
  have htrace : WordTrace (prefixWord ++ tailWord_2058876) baseStart_2058876 baseEnd_2058876 := by
    simpa [prefixWord, tailWord_2058876, baseEnd_2058876] using wordTrace_append hprefix tailTrace_2058876
  have hstable : (prefixWord ++ tailWord_2058876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058876).length < 2 ^ (prefixWord ++ tailWord_2058876).sum := by decide
  have hdescent : baseEnd_2058876 < baseStart_2058876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058968 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 2, 4]
def baseStart_2058968 : Nat := 118140960795 + 2058968 * 2 ^ 59
def prefixEnd_2058968 : Nat := 4983230072969 + 3 ^ 40 * 2058968 * 2
def baseEnd_2058968 : Nat := 704826824151070341287323

theorem tailTrace_2058968 : CollatzResearch.WordTrace tailWord_2058968 prefixEnd_2058968 704826824151070341287323 := by
  unfold tailWord_2058968
  simp only [CollatzResearch.WordTrace]
  refine ⟨37548366202359027291860779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50064488269812036389147705 37548366202359027291860779)
  ·
    refine ⟨56322549303538540937791169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37548366202359027291860779 56322549303538540937791169)
    ·
      refine ⟨42241911977653905703343377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56322549303538540937791169 42241911977653905703343377)
      ·
        refine ⟨31681433983240429277507533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42241911977653905703343377 31681433983240429277507533)
        ·
          refine ⟨11880537743715160979065325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31681433983240429277507533 11880537743715160979065325)
          ·
            refine ⟨4455201653893185367149497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11880537743715160979065325 4455201653893185367149497)
            ·
              refine ⟨3341401240419889025362123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4455201653893185367149497 3341401240419889025362123)
              ·
                refine ⟨5012101860629833538043185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3341401240419889025362123 5012101860629833538043185)
                ·
                  refine ⟨3759076395472375153532389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5012101860629833538043185 3759076395472375153532389)
                  ·
                    refine ⟨704826824151070341287323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3759076395472375153532389 704826824151070341287323)
                    ·
                      rfl

theorem cell22_2058968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_2058968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2058968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2058968 prefixEnd_2058968 := by exact prefixLift 2058968
  have htrace : WordTrace (prefixWord ++ tailWord_2058968) baseStart_2058968 baseEnd_2058968 := by
    simpa [prefixWord, tailWord_2058968, baseEnd_2058968] using wordTrace_append hprefix tailTrace_2058968
  have hstable : (prefixWord ++ tailWord_2058968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058968).length < 2 ^ (prefixWord ++ tailWord_2058968).sum := by decide
  have hdescent : baseEnd_2058968 < baseStart_2058968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059015 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 3, 3]
def baseStart_2059015 : Nat := 118140960795 + 2059015 * 2 ^ 59
def prefixEnd_2059015 : Nat := 4983230072969 + 3 ^ 40 * 2059015 * 2
def baseEnd_2059015 : Nat := 704842913211577885362179

theorem tailTrace_2059015 : CollatzResearch.WordTrace tailWord_2059015 prefixEnd_2059015 704842913211577885362179 := by
  unfold tailWord_2059015
  simp only [CollatzResearch.WordTrace]
  refine ⟨75098446635547781610682499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50065631090365187740454999 75098446635547781610682499)
  ·
    refine ⟨112647669953321672416023749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75098446635547781610682499 112647669953321672416023749)
    ·
      refine ⟨21121438116247813578004453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112647669953321672416023749 21121438116247813578004453)
      ·
        refine ⟨3960269646796465045875835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21121438116247813578004453 3960269646796465045875835)
        ·
          refine ⟨5940404470194697568813753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960269646796465045875835 5940404470194697568813753)
          ·
            refine ⟨4455303352646023176610315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5940404470194697568813753 4455303352646023176610315)
            ·
              refine ⟨6682955028969034764915473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4455303352646023176610315 6682955028969034764915473)
              ·
                refine ⟨5012216271726776073686605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682955028969034764915473 5012216271726776073686605)
                ·
                  refine ⟨1879581101897541027632477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5012216271726776073686605 1879581101897541027632477)
                  ·
                    refine ⟨704842913211577885362179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1879581101897541027632477 704842913211577885362179)
                    ·
                      rfl

theorem cell22_2059015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_2059015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059015 prefixEnd_2059015 := by exact prefixLift 2059015
  have htrace : WordTrace (prefixWord ++ tailWord_2059015) baseStart_2059015 baseEnd_2059015 := by
    simpa [prefixWord, tailWord_2059015, baseEnd_2059015] using wordTrace_append hprefix tailTrace_2059015
  have hstable : (prefixWord ++ tailWord_2059015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059015).length < 2 ^ (prefixWord ++ tailWord_2059015).sum := by decide
  have hdescent : baseEnd_2059015 < baseStart_2059015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059088 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 4, 3]
def baseStart_2059088 : Nat := 118140960795 + 2059088 * 2 ^ 59
def prefixEnd_2059088 : Nat := 4983230072969 + 3 ^ 40 * 2059088 * 2
def baseEnd_2059088 : Nat := 704867902603430028286955

theorem tailTrace_2059088 : CollatzResearch.WordTrace tailWord_2059088 prefixEnd_2059088 704867902603430028286955 := by
  unfold tailWord_2059088
  simp only [CollatzResearch.WordTrace]
  refine ⟨37550554582141657539044959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50067406109522210052059945 37550554582141657539044959)
  ·
    refine ⟨56325831873212486308567439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37550554582141657539044959 56325831873212486308567439)
    ·
      refine ⟨84488747809818729462851159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56325831873212486308567439 84488747809818729462851159)
      ·
        refine ⟨126733121714728094194276739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84488747809818729462851159 126733121714728094194276739)
        ·
          refine ⟨190099682572092141291415109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126733121714728094194276739 190099682572092141291415109)
          ·
            refine ⟨35643690482267276492140333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190099682572092141291415109 35643690482267276492140333)
            ·
              refine ⟨13366383930850228684552625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35643690482267276492140333 13366383930850228684552625)
              ·
                refine ⟨10024787948137671513414469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13366383930850228684552625 10024787948137671513414469)
                ·
                  refine ⟨1879647740275813408765213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10024787948137671513414469 1879647740275813408765213)
                  ·
                    refine ⟨704867902603430028286955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1879647740275813408765213 704867902603430028286955)
                    ·
                      rfl

theorem cell22_2059088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 4, 3].length) (baseStart_2059088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059088 prefixEnd_2059088 := by exact prefixLift 2059088
  have htrace : WordTrace (prefixWord ++ tailWord_2059088) baseStart_2059088 baseEnd_2059088 := by
    simpa [prefixWord, tailWord_2059088, baseEnd_2059088] using wordTrace_append hprefix tailTrace_2059088
  have hstable : (prefixWord ++ tailWord_2059088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059088).length < 2 ^ (prefixWord ++ tailWord_2059088).sum := by decide
  have hdescent : baseEnd_2059088 < baseStart_2059088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059103 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 2, 4]
def baseStart_2059103 : Nat := 118140960795 + 2059103 * 2 ^ 59
def prefixEnd_2059103 : Nat := 4983230072969 + 3 ^ 40 * 2059103 * 2
def baseEnd_2059103 : Nat := 704873037409974989161909

theorem tailTrace_2059103 : CollatzResearch.WordTrace tailWord_2059103 prefixEnd_2059103 704873037409974989161909 := by
  unfold tailWord_2059103
  simp only [CollatzResearch.WordTrace]
  refine ⟨75101656259228972639885963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50067770839485981759923975 75101656259228972639885963)
  ·
    refine ⟨112652484388843458959828945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75101656259228972639885963 112652484388843458959828945)
    ·
      refine ⟨84489363291632594219871709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112652484388843458959828945 84489363291632594219871709)
      ·
        refine ⟨31683511234362222832451891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84489363291632594219871709 31683511234362222832451891)
        ·
          refine ⟨47525266851543334248677837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31683511234362222832451891 47525266851543334248677837)
          ·
            refine ⟨17821975069328750343254189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47525266851543334248677837 17821975069328750343254189)
            ·
              refine ⟨6683240650998281378720321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17821975069328750343254189 6683240650998281378720321)
              ·
                refine ⟨5012430488248711034040241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6683240650998281378720321 5012430488248711034040241)
                ·
                  refine ⟨3759322866186533275530181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5012430488248711034040241 3759322866186533275530181)
                  ·
                    refine ⟨704873037409974989161909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3759322866186533275530181 704873037409974989161909)
                    ·
                      rfl

theorem cell22_2059103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_2059103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059103 prefixEnd_2059103 := by exact prefixLift 2059103
  have htrace : WordTrace (prefixWord ++ tailWord_2059103) baseStart_2059103 baseEnd_2059103 := by
    simpa [prefixWord, tailWord_2059103, baseEnd_2059103] using wordTrace_append hprefix tailTrace_2059103
  have hstable : (prefixWord ++ tailWord_2059103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059103).length < 2 ^ (prefixWord ++ tailWord_2059103).sum := by decide
  have hdescent : baseEnd_2059103 < baseStart_2059103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059107 : List Nat := [1, 1, 1, 5, 3, 2, 3, 2, 4]
def baseStart_2059107 : Nat := 118140960795 + 2059107 * 2 ^ 59
def prefixEnd_2059107 : Nat := 4983230072969 + 3 ^ 40 * 2059107 * 2
def baseEnd_2059107 : Nat := 234958135563906770687299

theorem tailTrace_2059107 : CollatzResearch.WordTrace tailWord_2059107 prefixEnd_2059107 234958135563906770687299 := by
  unfold tailWord_2059107
  simp only [CollatzResearch.WordTrace]
  refine ⟨75101802151214481323031575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50067868100809654215354383 75101802151214481323031575)
  ·
    refine ⟨112652703226821721984547363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75101802151214481323031575 112652703226821721984547363)
    ·
      refine ⟨168979054840232582976821045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112652703226821721984547363 168979054840232582976821045)
      ·
        refine ⟨15841786391271804654076973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168979054840232582976821045 15841786391271804654076973)
        ·
          refine ⟨5940669896726926745278865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15841786391271804654076973 5940669896726926745278865)
          ·
            refine ⟨4455502422545195058959149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5940669896726926745278865 4455502422545195058959149)
            ·
              refine ⟨1670813408454448147109681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4455502422545195058959149 1670813408454448147109681)
              ·
                refine ⟨1253110056340836110332261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670813408454448147109681 1253110056340836110332261)
                ·
                  refine ⟨234958135563906770687299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1253110056340836110332261 234958135563906770687299)
                  ·
                    rfl

theorem cell22_2059107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 4].length) (baseStart_2059107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059107 prefixEnd_2059107 := by exact prefixLift 2059107
  have htrace : WordTrace (prefixWord ++ tailWord_2059107) baseStart_2059107 baseEnd_2059107 := by
    simpa [prefixWord, tailWord_2059107, baseEnd_2059107] using wordTrace_append hprefix tailTrace_2059107
  have hstable : (prefixWord ++ tailWord_2059107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059107).length < 2 ^ (prefixWord ++ tailWord_2059107).sum := by decide
  have hdescent : baseEnd_2059107 < baseStart_2059107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059122 : List Nat := [3, 2, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_2059122 : Nat := 118140960795 + 2059122 * 2 ^ 59
def prefixEnd_2059122 : Nat := 4983230072969 + 3 ^ 40 * 2059122 * 2
def baseEnd_2059122 : Nat := 704879541498265272936851

theorem tailTrace_2059122 : CollatzResearch.WordTrace tailWord_2059122 prefixEnd_2059122 704879541498265272936851 := by
  unfold tailWord_2059122
  simp only [CollatzResearch.WordTrace]
  refine ⟨18775587311540034721206905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50068232830773425923218413 18775587311540034721206905)
  ·
    refine ⟨14081690483655026040905179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18775587311540034721206905 14081690483655026040905179)
    ·
      refine ⟨21122535725482539061357769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14081690483655026040905179 21122535725482539061357769)
      ·
        refine ⟨15841901794111904296018327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21122535725482539061357769 15841901794111904296018327)
        ·
          refine ⟨23762852691167856444027491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15841901794111904296018327 23762852691167856444027491)
          ·
            refine ⟨35644279036751784666041237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23762852691167856444027491 35644279036751784666041237)
            ·
              refine ⟨1670825579847739906220683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35644279036751784666041237 1670825579847739906220683)
              ·
                refine ⟨2506238369771609859331025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670825579847739906220683 2506238369771609859331025)
                ·
                  refine ⟨1879678777328707394498269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2506238369771609859331025 1879678777328707394498269)
                  ·
                    refine ⟨704879541498265272936851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1879678777328707394498269 704879541498265272936851)
                    ·
                      rfl

theorem cell22_2059122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_2059122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059122 prefixEnd_2059122 := by exact prefixLift 2059122
  have htrace : WordTrace (prefixWord ++ tailWord_2059122) baseStart_2059122 baseEnd_2059122 := by
    simpa [prefixWord, tailWord_2059122, baseEnd_2059122] using wordTrace_append hprefix tailTrace_2059122
  have hstable : (prefixWord ++ tailWord_2059122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059122).length < 2 ^ (prefixWord ++ tailWord_2059122).sum := by decide
  have hdescent : baseEnd_2059122 < baseStart_2059122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059158 : List Nat := [5, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_2059158 : Nat := 118140960795 + 2059158 * 2 ^ 59
def prefixEnd_2059158 : Nat := 4983230072969 + 3 ^ 40 * 2059158 * 2
def baseEnd_2059158 : Nat := 234963955011324393012247

theorem tailTrace_2059158 : CollatzResearch.WordTrace tailWord_2059158 prefixEnd_2059158 234963955011324393012247 := by
  unfold tailWord_2059158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4693978892126857314571133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50069108182686478022092085 4693978892126857314571133)
  ·
    refine ⟨1760242084547571492964175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4693978892126857314571133 1760242084547571492964175)
    ·
      refine ⟨2640363126821357239446263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1760242084547571492964175 2640363126821357239446263)
      ·
        refine ⟨3960544690232035859169395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640363126821357239446263 3960544690232035859169395)
        ·
          refine ⟨5940817035348053788754093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960544690232035859169395 5940817035348053788754093)
          ·
            refine ⟨2227806388255520170782785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5940817035348053788754093 2227806388255520170782785)
            ·
              refine ⟨1670854791191640128087089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227806388255520170782785 1670854791191640128087089)
              ·
                refine ⟨1253141093393730096065317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670854791191640128087089 1253141093393730096065317)
                ·
                  refine ⟨234963955011324393012247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1253141093393730096065317 234963955011324393012247)
                  ·
                    rfl

theorem cell22_2059158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_2059158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059158 prefixEnd_2059158 := by exact prefixLift 2059158
  have htrace : WordTrace (prefixWord ++ tailWord_2059158) baseStart_2059158 baseEnd_2059158 := by
    simpa [prefixWord, tailWord_2059158, baseEnd_2059158] using wordTrace_append hprefix tailTrace_2059158
  have hstable : (prefixWord ++ tailWord_2059158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059158).length < 2 ^ (prefixWord ++ tailWord_2059158).sum := by decide
  have hdescent : baseEnd_2059158 < baseStart_2059158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
