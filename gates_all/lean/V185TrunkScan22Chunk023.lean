import V185TrunkScan22Chunk022

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_204447 : List Nat := [1, 1, 2, 7, 1, 2, 1, 7]
def baseStart_204447 : Nat := 118140960795 + 204447 * 2 ^ 59
def prefixEnd_204447 : Nat := 4983230072969 + 3 ^ 40 * 204447 * 2
def baseEnd_204447 : Nat := 7776265138508654360909

theorem tailTrace_204447 : CollatzResearch.WordTrace tailWord_204447 prefixEnd_204447 7776265138508654360909 := by
  unfold tailWord_204447
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456794690330910612843595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4971196460220607075229063 7456794690330910612843595)
  ·
    refine ⟨11185192035496365919265393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7456794690330910612843595 11185192035496365919265393)
    ·
      refine ⟨8388894026622274439449045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11185192035496365919265393 8388894026622274439449045)
      ·
        refine ⟨196614703748959557174587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 8388894026622274439449045 196614703748959557174587)
        ·
          refine ⟨294922055623439335761881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196614703748959557174587 294922055623439335761881)
          ·
            refine ⟨221191541717579501821411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294922055623439335761881 221191541717579501821411)
            ·
              refine ⟨331787312576369252732117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221191541717579501821411 331787312576369252732117)
              ·
                refine ⟨7776265138508654360909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 331787312576369252732117 7776265138508654360909)
                ·
                  rfl

theorem cell22_204447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 7].length) (baseStart_204447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204447 prefixEnd_204447 := by exact prefixLift 204447
  have htrace : WordTrace (prefixWord ++ tailWord_204447) baseStart_204447 baseEnd_204447 := by
    simpa [prefixWord, tailWord_204447, baseEnd_204447] using wordTrace_append hprefix tailTrace_204447
  have hstable : (prefixWord ++ tailWord_204447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204447).length < 2 ^ (prefixWord ++ tailWord_204447).sum := by decide
  have hdescent : baseEnd_204447 < baseStart_204447 := by decide
  rcases family_descends (prefixWord ++ tailWord_204447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204520 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 6]
def baseStart_204520 : Nat := 118140960795 + 204520 * 2 ^ 59
def prefixEnd_204520 : Nat := 4983230072969 + 3 ^ 40 * 204520 * 2
def baseEnd_204520 : Nat := 23337125212810010724319

theorem tailTrace_204520 : CollatzResearch.WordTrace tailWord_204520 prefixEnd_204520 23337125212810010724319 := by
  unfold tailWord_204520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3729728609533222040125507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4972971479377629386834009 3729728609533222040125507)
  ·
    refine ⟨5594592914299833060188261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3729728609533222040125507 5594592914299833060188261)
    ·
      refine ⟨1048986171431218698785299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5594592914299833060188261 1048986171431218698785299)
      ·
        refine ⟨1573479257146828048177949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048986171431218698785299 1573479257146828048177949)
        ·
          refine ⟨590054721430060518066731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1573479257146828048177949 590054721430060518066731)
          ·
            refine ⟨885082082145090777100097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590054721430060518066731 885082082145090777100097)
            ·
              refine ⟨663811561608818082825073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885082082145090777100097 663811561608818082825073)
              ·
                refine ⟨497858671206613562118805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663811561608818082825073 497858671206613562118805)
                ·
                  refine ⟨23337125212810010724319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 497858671206613562118805 23337125212810010724319)
                  ·
                    rfl

theorem cell22_204520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_204520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204520 prefixEnd_204520 := by exact prefixLift 204520
  have htrace : WordTrace (prefixWord ++ tailWord_204520) baseStart_204520 baseEnd_204520 := by
    simpa [prefixWord, tailWord_204520, baseEnd_204520] using wordTrace_append hprefix tailTrace_204520
  have hstable : (prefixWord ++ tailWord_204520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204520).length < 2 ^ (prefixWord ++ tailWord_204520).sum := by decide
  have hdescent : baseEnd_204520 < baseStart_204520 := by decide
  rcases family_descends (prefixWord ++ tailWord_204520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204535 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 4, 3]
def baseStart_204535 : Nat := 118140960795 + 204535 * 2 ^ 59
def prefixEnd_204535 : Nat := 4983230072969 + 3 ^ 40 * 204535 * 2
def baseEnd_204535 : Nat := 70016510444974993047911

theorem tailTrace_204535 : CollatzResearch.WordTrace tailWord_204535 prefixEnd_204535 70016510444974993047911 := by
  unfold tailWord_204535
  simp only [CollatzResearch.WordTrace]
  refine ⟨7460004314012101642047059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4973336209341401094698039 7460004314012101642047059)
  ·
    refine ⟨11190006471018152463070589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7460004314012101642047059 11190006471018152463070589)
    ·
      refine ⟨4196252426631807173651471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11190006471018152463070589 4196252426631807173651471)
      ·
        refine ⟨6294378639947710760477207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4196252426631807173651471 6294378639947710760477207)
        ·
          refine ⟨9441567959921566140715811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6294378639947710760477207 9441567959921566140715811)
          ·
            refine ⟨14162351939882349211073717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9441567959921566140715811 14162351939882349211073717)
            ·
              refine ⟨1327720494363970238538161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14162351939882349211073717 1327720494363970238538161)
              ·
                refine ⟨995790370772977678903621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1327720494363970238538161 995790370772977678903621)
                ·
                  refine ⟨186710694519933314794429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 995790370772977678903621 186710694519933314794429)
                  ·
                    refine ⟨70016510444974993047911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186710694519933314794429 70016510444974993047911)
                    ·
                      rfl

theorem cell22_204535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_204535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204535 prefixEnd_204535 := by exact prefixLift 204535
  have htrace : WordTrace (prefixWord ++ tailWord_204535) baseStart_204535 baseEnd_204535 := by
    simpa [prefixWord, tailWord_204535, baseEnd_204535] using wordTrace_append hprefix tailTrace_204535
  have hstable : (prefixWord ++ tailWord_204535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204535).length < 2 ^ (prefixWord ++ tailWord_204535).sum := by decide
  have hdescent : baseEnd_204535 < baseStart_204535 := by decide
  rcases family_descends (prefixWord ++ tailWord_204535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204552 : List Nat := [2, 1, 3, 2, 2, 1, 2, 4, 2, 3]
def baseStart_204552 : Nat := 118140960795 + 204552 * 2 ^ 59
def prefixEnd_204552 : Nat := 4983230072969 + 3 ^ 40 * 204552 * 2
def baseEnd_204552 : Nat := 70022329892392615372859

theorem tailTrace_204552 : CollatzResearch.WordTrace tailWord_204552 prefixEnd_204552 70022329892392615372859 := by
  unfold tailWord_204552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730312177475256772707955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4973749569967009030277273 3730312177475256772707955)
  ·
    refine ⟨5595468266212885159061933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3730312177475256772707955 5595468266212885159061933)
    ·
      refine ⟨2098300599829831934648225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5595468266212885159061933 2098300599829831934648225)
      ·
        refine ⟨1573725449872373950986169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2098300599829831934648225 1573725449872373950986169)
        ·
          refine ⟨1180294087404280463239627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1573725449872373950986169 1180294087404280463239627)
          ·
            refine ⟨1770441131106420694859441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180294087404280463239627 1770441131106420694859441)
            ·
              refine ⟨1327830848329815521144581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770441131106420694859441 1327830848329815521144581)
              ·
                refine ⟨248968284061840410214609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1327830848329815521144581 248968284061840410214609)
                ·
                  refine ⟨186726213046380307660957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248968284061840410214609 186726213046380307660957)
                  ·
                    refine ⟨70022329892392615372859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186726213046380307660957 70022329892392615372859)
                    ·
                      rfl

theorem cell22_204552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_204552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204552 prefixEnd_204552 := by exact prefixLift 204552
  have htrace : WordTrace (prefixWord ++ tailWord_204552) baseStart_204552 baseEnd_204552 := by
    simpa [prefixWord, tailWord_204552, baseEnd_204552] using wordTrace_append hprefix tailTrace_204552
  have hstable : (prefixWord ++ tailWord_204552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204552).length < 2 ^ (prefixWord ++ tailWord_204552).sum := by decide
  have hdescent : baseEnd_204552 < baseStart_204552 := by decide
  rcases family_descends (prefixWord ++ tailWord_204552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204554 : List Nat := [3, 1, 2, 2, 1, 4, 3, 2, 4]
def baseStart_204554 : Nat := 118140960795 + 204554 * 2 ^ 59
def prefixEnd_204554 : Nat := 4983230072969 + 3 ^ 40 * 204554 * 2
def baseEnd_204554 : Nat := 23341004844421758940951

theorem tailTrace_204554 : CollatzResearch.WordTrace tailWord_204554 prefixEnd_204554 23341004844421758940951 := by
  unfold tailWord_204554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865174325235816971747179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4973798200628845257992477 1865174325235816971747179)
  ·
    refine ⟨2797761487853725457620769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1865174325235816971747179 2797761487853725457620769)
    ·
      refine ⟨2098321115890294093215577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2797761487853725457620769 2098321115890294093215577)
      ·
        refine ⟨1573740836917720569911683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2098321115890294093215577 1573740836917720569911683)
        ·
          refine ⟨2360611255376580854867525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573740836917720569911683 2360611255376580854867525)
          ·
            refine ⟨442614610383108910287661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2360611255376580854867525 442614610383108910287661)
            ·
              refine ⟨165980478893665841357873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 442614610383108910287661 165980478893665841357873)
              ·
                refine ⟨124485359170249381018405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165980478893665841357873 124485359170249381018405)
                ·
                  refine ⟨23341004844421758940951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124485359170249381018405 23341004844421758940951)
                  ·
                    rfl

theorem cell22_204554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_204554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204554 prefixEnd_204554 := by exact prefixLift 204554
  have htrace : WordTrace (prefixWord ++ tailWord_204554) baseStart_204554 baseEnd_204554 := by
    simpa [prefixWord, tailWord_204554, baseEnd_204554] using wordTrace_append hprefix tailTrace_204554
  have hstable : (prefixWord ++ tailWord_204554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204554).length < 2 ^ (prefixWord ++ tailWord_204554).sum := by decide
  have hdescent : baseEnd_204554 < baseStart_204554 := by decide
  rcases family_descends (prefixWord ++ tailWord_204554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204563 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 2, 7]
def baseStart_204563 : Nat := 118140960795 + 204563 * 2 ^ 59
def prefixEnd_204563 : Nat := 4983230072969 + 3 ^ 40 * 204563 * 2
def baseEnd_204563 : Nat := 70026095417192253347825

theorem tailTrace_204563 : CollatzResearch.WordTrace tailWord_204563 prefixEnd_204563 70026095417192253347825 := by
  unfold tailWord_204563
  simp only [CollatzResearch.WordTrace]
  refine ⟨7461025557910662424066343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4974017038607108282710895 7461025557910662424066343)
  ·
    refine ⟨11191538336865993636099515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7461025557910662424066343 11191538336865993636099515)
    ·
      refine ⟨16787307505298990454149273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11191538336865993636099515 16787307505298990454149273)
      ·
        refine ⟨12590480628974242840611955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16787307505298990454149273 12590480628974242840611955)
        ·
          refine ⟨18885720943461364260917933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12590480628974242840611955 18885720943461364260917933)
          ·
            refine ⟨7082145353798011597844225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18885720943461364260917933 7082145353798011597844225)
            ·
              refine ⟨5311609015348508698383169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7082145353798011597844225 5311609015348508698383169)
              ·
                refine ⟨3983706761511381523787377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5311609015348508698383169 3983706761511381523787377)
                ·
                  refine ⟨2987780071133536142840533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3983706761511381523787377 2987780071133536142840533)
                  ·
                    refine ⟨70026095417192253347825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2987780071133536142840533 70026095417192253347825)
                    ·
                      rfl

theorem cell22_204563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_204563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204563 prefixEnd_204563 := by exact prefixLift 204563
  have htrace : WordTrace (prefixWord ++ tailWord_204563) baseStart_204563 baseEnd_204563 := by
    simpa [prefixWord, tailWord_204563, baseEnd_204563] using wordTrace_append hprefix tailTrace_204563
  have hstable : (prefixWord ++ tailWord_204563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204563).length < 2 ^ (prefixWord ++ tailWord_204563).sum := by decide
  have hdescent : baseEnd_204563 < baseStart_204563 := by decide
  rcases family_descends (prefixWord ++ tailWord_204563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204565 : List Nat := [1, 3, 2, 1, 2, 4, 2, 7]
def baseStart_204565 : Nat := 118140960795 + 204565 * 2 ^ 59
def prefixEnd_204565 : Nat := 4983230072969 + 3 ^ 40 * 204565 * 2
def baseEnd_204565 : Nat := 7780753339784990533091

theorem tailTrace_204565 : CollatzResearch.WordTrace tailWord_204565 prefixEnd_204565 7780753339784990533091 := by
  unfold tailWord_204565
  simp only [CollatzResearch.WordTrace]
  refine ⟨7461098503903416765639149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4974065669268944510426099 7461098503903416765639149)
  ·
    refine ⟨2797911938963781287114681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7461098503903416765639149 2797911938963781287114681)
    ·
      refine ⟨2098433954222835965336011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2797911938963781287114681 2098433954222835965336011)
      ·
        refine ⟨3147650931334253948004017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2098433954222835965336011 3147650931334253948004017)
        ·
          refine ⟨2360738198500690461003013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3147650931334253948004017 2360738198500690461003013)
          ·
            refine ⟨442638412218879461438065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2360738198500690461003013 442638412218879461438065)
            ·
              refine ⟨331978809164159596078549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442638412218879461438065 331978809164159596078549)
              ·
                refine ⟨7780753339784990533091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 331978809164159596078549 7780753339784990533091)
                ·
                  rfl

theorem cell22_204565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 7].length) (baseStart_204565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204565 prefixEnd_204565 := by exact prefixLift 204565
  have htrace : WordTrace (prefixWord ++ tailWord_204565) baseStart_204565 baseEnd_204565 := by
    simpa [prefixWord, tailWord_204565, baseEnd_204565] using wordTrace_append hprefix tailTrace_204565
  have hstable : (prefixWord ++ tailWord_204565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204565).length < 2 ^ (prefixWord ++ tailWord_204565).sum := by decide
  have hdescent : baseEnd_204565 < baseStart_204565 := by decide
  rcases family_descends (prefixWord ++ tailWord_204565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204625 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 1, 7]
def baseStart_204625 : Nat := 118140960795 + 204625 * 2 ^ 59
def prefixEnd_204625 : Nat := 4983230072969 + 3 ^ 40 * 204625 * 2
def baseEnd_204625 : Nat := 70047319284244758297635

theorem tailTrace_204625 : CollatzResearch.WordTrace tailWord_204625 prefixEnd_204625 70047319284244758297635 := by
  unfold tailWord_204625
  simp only [CollatzResearch.WordTrace]
  refine ⟨7463286883686047012823329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4975524589124031341882219 7463286883686047012823329)
  ·
    refine ⟨5597465162764535259617497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7463286883686047012823329 5597465162764535259617497)
    ·
      refine ⟨4198098872073401444713123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5597465162764535259617497 4198098872073401444713123)
      ·
        refine ⟨6297148308110102167069685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4198098872073401444713123 6297148308110102167069685)
        ·
          refine ⟨590357653885322078162783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6297148308110102167069685 590357653885322078162783)
          ·
            refine ⟨885536480827983117244175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590357653885322078162783 885536480827983117244175)
            ·
              refine ⟨1328304721241974675866263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885536480827983117244175 1328304721241974675866263)
              ·
                refine ⟨1992457081862962013799395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328304721241974675866263 1992457081862962013799395)
                ·
                  refine ⟨2988685622794443020699093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1992457081862962013799395 2988685622794443020699093)
                  ·
                    refine ⟨70047319284244758297635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2988685622794443020699093 70047319284244758297635)
                    ·
                      rfl

theorem cell22_204625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_204625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204625 prefixEnd_204625 := by exact prefixLift 204625
  have htrace : WordTrace (prefixWord ++ tailWord_204625) baseStart_204625 baseEnd_204625 := by
    simpa [prefixWord, tailWord_204625, baseEnd_204625] using wordTrace_append hprefix tailTrace_204625
  have hstable : (prefixWord ++ tailWord_204625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204625).length < 2 ^ (prefixWord ++ tailWord_204625).sum := by decide
  have hdescent : baseEnd_204625 < baseStart_204625 := by decide
  rcases family_descends (prefixWord ++ tailWord_204625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204657 : List Nat := [1, 2, 2, 2, 1, 3, 3, 3, 1, 4]
def baseStart_204657 : Nat := 118140960795 + 204657 * 2 ^ 59
def prefixEnd_204657 : Nat := 4983230072969 + 3 ^ 40 * 204657 * 2
def baseEnd_204657 : Nat := 70058273538207341497537

theorem tailTrace_204657 : CollatzResearch.WordTrace tailWord_204657 prefixEnd_204657 70058273538207341497537 := by
  unfold tailWord_204657
  simp only [CollatzResearch.WordTrace]
  refine ⟨7464454019570116477988225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4976302679713410985325483 7464454019570116477988225)
  ·
    refine ⟨5598340514677587358491169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7464454019570116477988225 5598340514677587358491169)
    ·
      refine ⟨4198755386008190518868377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5598340514677587358491169 4198755386008190518868377)
      ·
        refine ⟨3149066539506142889151283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4198755386008190518868377 3149066539506142889151283)
        ·
          refine ⟨4723599809259214333726925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149066539506142889151283 4723599809259214333726925)
          ·
            refine ⟨1771349928472205375147597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4723599809259214333726925 1771349928472205375147597)
            ·
              refine ⟨664256223177077015680349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1771349928472205375147597 664256223177077015680349)
              ·
                refine ⟨249096083691403880880131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 664256223177077015680349 249096083691403880880131)
                ·
                  refine ⟨373644125537105821320197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249096083691403880880131 373644125537105821320197)
                  ·
                    refine ⟨70058273538207341497537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 373644125537105821320197 70058273538207341497537)
                    ·
                      rfl

theorem cell22_204657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_204657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204657 prefixEnd_204657 := by exact prefixLift 204657
  have htrace : WordTrace (prefixWord ++ tailWord_204657) baseStart_204657 baseEnd_204657 := by
    simpa [prefixWord, tailWord_204657, baseEnd_204657] using wordTrace_append hprefix tailTrace_204657
  have hstable : (prefixWord ++ tailWord_204657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204657).length < 2 ^ (prefixWord ++ tailWord_204657).sum := by decide
  have hdescent : baseEnd_204657 < baseStart_204657 := by decide
  rcases family_descends (prefixWord ++ tailWord_204657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204672 : List Nat := [2, 1, 1, 2, 1, 2, 3, 6, 4]
def baseStart_204672 : Nat := 118140960795 + 204672 * 2 ^ 59
def prefixEnd_204672 : Nat := 4983230072969 + 3 ^ 40 * 204672 * 2
def baseEnd_204672 : Nat := 23354469448250767457497

theorem tailTrace_204672 : CollatzResearch.WordTrace tailWord_204672 prefixEnd_204672 23354469448250767457497 := by
  unfold tailWord_204672
  simp only [CollatzResearch.WordTrace]
  refine ⟨3732500557257887019892135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4976667409677182693189513 3732500557257887019892135)
  ·
    refine ⟨5598750835886830529838203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3732500557257887019892135 5598750835886830529838203)
    ·
      refine ⟨8398126253830245794757305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5598750835886830529838203 8398126253830245794757305)
      ·
        refine ⟨6298594690372684346067979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8398126253830245794757305 6298594690372684346067979)
        ·
          refine ⟨9447892035559026519101969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6298594690372684346067979 9447892035559026519101969)
          ·
            refine ⟨7085919026669269889326477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9447892035559026519101969 7085919026669269889326477)
            ·
              refine ⟨2657219635000976208497429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7085919026669269889326477 2657219635000976208497429)
              ·
                refine ⟨124557170390670759773317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2657219635000976208497429 124557170390670759773317)
                ·
                  refine ⟨23354469448250767457497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124557170390670759773317 23354469448250767457497)
                  ·
                    rfl

theorem cell22_204672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 4].length) (baseStart_204672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204672 prefixEnd_204672 := by exact prefixLift 204672
  have htrace : WordTrace (prefixWord ++ tailWord_204672) baseStart_204672 baseEnd_204672 := by
    simpa [prefixWord, tailWord_204672, baseEnd_204672] using wordTrace_append hprefix tailTrace_204672
  have hstable : (prefixWord ++ tailWord_204672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204672).length < 2 ^ (prefixWord ++ tailWord_204672).sum := by decide
  have hdescent : baseEnd_204672 < baseStart_204672 := by decide
  rcases family_descends (prefixWord ++ tailWord_204672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204792 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 3, 4]
def baseStart_204792 : Nat := 118140960795 + 204792 * 2 ^ 59
def prefixEnd_204792 : Nat := 4983230072969 + 3 ^ 40 * 204792 * 2
def baseEnd_204792 : Nat := 70104486797111989372123

theorem tailTrace_204792 : CollatzResearch.WordTrace tailWord_204792 prefixEnd_204792 70104486797111989372123 := by
  unfold tailWord_204792
  simp only [CollatzResearch.WordTrace]
  refine ⟨3734688937040517267076315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4979585249387356356101753 3734688937040517267076315)
  ·
    refine ⟨5602033405560775900614473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3734688937040517267076315 5602033405560775900614473)
    ·
      refine ⟨4201525054170581925460855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5602033405560775900614473 4201525054170581925460855)
      ·
        refine ⟨6302287581255872888191283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4201525054170581925460855 6302287581255872888191283)
        ·
          refine ⟨9453431371883809332286925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6302287581255872888191283 9453431371883809332286925)
          ·
            refine ⟨3545036764456428499607597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9453431371883809332286925 3545036764456428499607597)
            ·
              refine ⟨1329388786671160687352849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3545036764456428499607597 1329388786671160687352849)
              ·
                refine ⟨997041590003370515514637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1329388786671160687352849 997041590003370515514637)
                ·
                  refine ⟨373890596251263943317989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 997041590003370515514637 373890596251263943317989)
                  ·
                    refine ⟨70104486797111989372123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 373890596251263943317989 70104486797111989372123)
                    ·
                      rfl

theorem cell22_204792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_204792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204792 prefixEnd_204792 := by exact prefixLift 204792
  have htrace : WordTrace (prefixWord ++ tailWord_204792) baseStart_204792 baseEnd_204792 := by
    simpa [prefixWord, tailWord_204792, baseEnd_204792] using wordTrace_append hprefix tailTrace_204792
  have hstable : (prefixWord ++ tailWord_204792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204792).length < 2 ^ (prefixWord ++ tailWord_204792).sum := by decide
  have hdescent : baseEnd_204792 < baseStart_204792 := by decide
  rcases family_descends (prefixWord ++ tailWord_204792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204807 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 8]
def baseStart_204807 : Nat := 118140960795 + 204807 * 2 ^ 59
def prefixEnd_204807 : Nat := 4983230072969 + 3 ^ 40 * 204807 * 2
def baseEnd_204807 : Nat := 23369873867885650082359

theorem tailTrace_204807 : CollatzResearch.WordTrace tailWord_204807 prefixEnd_204807 23369873867885650082359 := by
  unfold tailWord_204807
  simp only [CollatzResearch.WordTrace]
  refine ⟨7469924969026692095948675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4979949979351128063965783 7469924969026692095948675)
  ·
    refine ⟨11204887453540038143923013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7469924969026692095948675 11204887453540038143923013)
    ·
      refine ⟨2100916397538757151985565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11204887453540038143923013 2100916397538757151985565)
      ·
        refine ⟨787843649077033931994587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2100916397538757151985565 787843649077033931994587)
        ·
          refine ⟨1181765473615550897991881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787843649077033931994587 1181765473615550897991881)
          ·
            refine ⟨886324105211663173493911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1181765473615550897991881 886324105211663173493911)
            ·
              refine ⟨1329486157817494760240867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886324105211663173493911 1329486157817494760240867)
              ·
                refine ⟨1994229236726242140361301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1329486157817494760240867 1994229236726242140361301)
                ·
                  refine ⟨23369873867885650082359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1994229236726242140361301 23369873867885650082359)
                  ·
                    rfl

theorem cell22_204807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 8].length) (baseStart_204807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204807 prefixEnd_204807 := by exact prefixLift 204807
  have htrace : WordTrace (prefixWord ++ tailWord_204807) baseStart_204807 baseEnd_204807 := by
    simpa [prefixWord, tailWord_204807, baseEnd_204807] using wordTrace_append hprefix tailTrace_204807
  have hstable : (prefixWord ++ tailWord_204807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204807).length < 2 ^ (prefixWord ++ tailWord_204807).sum := by decide
  have hdescent : baseEnd_204807 < baseStart_204807 := by decide
  rcases family_descends (prefixWord ++ tailWord_204807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204826 : List Nat := [3, 1, 1, 3, 1, 3, 4, 1, 1, 4]
def baseStart_204826 : Nat := 118140960795 + 204826 * 2 ^ 59
def prefixEnd_204826 : Nat := 4983230072969 + 3 ^ 40 * 204826 * 2
def baseEnd_204826 : Nat := 70116125691947234022019

theorem tailTrace_204826 : CollatzResearch.WordTrace tailWord_204826 prefixEnd_204826 70116125691947234022019 := by
  unfold tailWord_204826
  simp only [CollatzResearch.WordTrace]
  refine ⟨1867654488989464585222583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4980411970638572227260221 1867654488989464585222583)
  ·
    refine ⟨2801481733484196877833875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1867654488989464585222583 2801481733484196877833875)
    ·
      refine ⟨4202222600226295316750813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2801481733484196877833875 4202222600226295316750813)
      ·
        refine ⟨1575833475084860743781555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4202222600226295316750813 1575833475084860743781555)
        ·
          refine ⟨2363750212627291115672333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1575833475084860743781555 2363750212627291115672333)
          ·
            refine ⟨886406329735234168377125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2363750212627291115672333 886406329735234168377125)
            ·
              refine ⟨166201186825356406570711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 886406329735234168377125 166201186825356406570711)
              ·
                refine ⟨249301780238034609856067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166201186825356406570711 249301780238034609856067)
                ·
                  refine ⟨373952670357051914784101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249301780238034609856067 373952670357051914784101)
                  ·
                    refine ⟨70116125691947234022019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 373952670357051914784101 70116125691947234022019)
                    ·
                      rfl

theorem cell22_204826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_204826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204826 prefixEnd_204826 := by exact prefixLift 204826
  have htrace : WordTrace (prefixWord ++ tailWord_204826) baseStart_204826 baseEnd_204826 := by
    simpa [prefixWord, tailWord_204826, baseEnd_204826] using wordTrace_append hprefix tailTrace_204826
  have hstable : (prefixWord ++ tailWord_204826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204826).length < 2 ^ (prefixWord ++ tailWord_204826).sum := by decide
  have hdescent : baseEnd_204826 < baseStart_204826 := by decide
  rcases family_descends (prefixWord ++ tailWord_204826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204854 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_204854 : Nat := 118140960795 + 204854 * 2 ^ 59
def prefixEnd_204854 : Nat := 4983230072969 + 3 ^ 40 * 204854 * 2
def baseEnd_204854 : Nat := 70125710664164494321933

theorem tailTrace_204854 : CollatzResearch.WordTrace tailWord_204854 prefixEnd_204854 70125710664164494321933 := by
  unfold tailWord_204854
  simp only [CollatzResearch.WordTrace]
  refine ⟨466977449991026195181851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4981092799904279415273077 466977449991026195181851)
  ·
    refine ⟨700466174986539292772777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 466977449991026195181851 700466174986539292772777)
    ·
      refine ⟨525349631239904469579583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 700466174986539292772777 525349631239904469579583)
      ·
        refine ⟨788024446859856704369375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525349631239904469579583 788024446859856704369375)
        ·
          refine ⟨1182036670289785056554063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788024446859856704369375 1182036670289785056554063)
          ·
            refine ⟨1773055005434677584831095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182036670289785056554063 1773055005434677584831095)
            ·
              refine ⟨2659582508152016377246643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773055005434677584831095 2659582508152016377246643)
              ·
                refine ⟨3989373762228024565869965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659582508152016377246643 3989373762228024565869965)
                ·
                  refine ⟨1496015160835509212201237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3989373762228024565869965 1496015160835509212201237)
                  ·
                    refine ⟨70125710664164494321933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1496015160835509212201237 70125710664164494321933)
                    ·
                      rfl

theorem cell22_204854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_204854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204854 prefixEnd_204854 := by exact prefixLift 204854
  have htrace : WordTrace (prefixWord ++ tailWord_204854) baseStart_204854 baseEnd_204854 := by
    simpa [prefixWord, tailWord_204854, baseEnd_204854] using wordTrace_append hprefix tailTrace_204854
  have hstable : (prefixWord ++ tailWord_204854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204854).length < 2 ^ (prefixWord ++ tailWord_204854).sum := by decide
  have hdescent : baseEnd_204854 < baseStart_204854 := by decide
  rcases family_descends (prefixWord ++ tailWord_204854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204856 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 1, 5]
def baseStart_204856 : Nat := 118140960795 + 204856 * 2 ^ 59
def prefixEnd_204856 : Nat := 4983230072969 + 3 ^ 40 * 204856 * 2
def baseEnd_204856 : Nat := 70126395305037155771927

theorem tailTrace_204856 : CollatzResearch.WordTrace tailWord_204856 prefixEnd_204856 70126395305037155771927 := by
  unfold tailWord_204856
  simp only [CollatzResearch.WordTrace]
  refine ⟨3735856072924586732241211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4981141430566115642988281 3735856072924586732241211)
  ·
    refine ⟨5603784109386880098361817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3735856072924586732241211 5603784109386880098361817)
    ·
      refine ⟨4202838082040160073771363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5603784109386880098361817 4202838082040160073771363)
      ·
        refine ⟨6304257123060240110657045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4202838082040160073771363 6304257123060240110657045)
        ·
          refine ⟨295512052643448755187049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6304257123060240110657045 295512052643448755187049)
          ·
            refine ⟨221634039482586566390287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295512052643448755187049 221634039482586566390287)
            ·
              refine ⟨332451059223879849585431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221634039482586566390287 332451059223879849585431)
              ·
                refine ⟨498676588835819774378147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332451059223879849585431 498676588835819774378147)
                ·
                  refine ⟨748014883253729661567221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498676588835819774378147 748014883253729661567221)
                  ·
                    refine ⟨70126395305037155771927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 748014883253729661567221 70126395305037155771927)
                    ·
                      rfl

theorem cell22_204856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_204856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204856 prefixEnd_204856 := by exact prefixLift 204856
  have htrace : WordTrace (prefixWord ++ tailWord_204856) baseStart_204856 baseEnd_204856 := by
    simpa [prefixWord, tailWord_204856, baseEnd_204856] using wordTrace_append hprefix tailTrace_204856
  have hstable : (prefixWord ++ tailWord_204856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204856).length < 2 ^ (prefixWord ++ tailWord_204856).sum := by decide
  have hdescent : baseEnd_204856 < baseStart_204856 := by decide
  rcases family_descends (prefixWord ++ tailWord_204856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204886 : List Nat := [5, 2, 2, 1, 1, 1, 10]
def baseStart_204886 : Nat := 118140960795 + 204886 * 2 ^ 59
def prefixEnd_204886 : Nat := 4983230072969 + 3 ^ 40 * 204886 * 2
def baseEnd_204886 : Nat := 2597654256226928797105

theorem tailTrace_204886 : CollatzResearch.WordTrace tailWord_204886 prefixEnd_204886 2597654256226928797105 := by
  unfold tailWord_204886
  simp only [CollatzResearch.WordTrace]
  refine ⟨467050395983780536754657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4981870890493659058716341 467050395983780536754657)
  ·
    refine ⟨350287796987835402565993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 467050395983780536754657 350287796987835402565993)
    ·
      refine ⟨262715847740876551924495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350287796987835402565993 262715847740876551924495)
      ·
        refine ⟨394073771611314827886743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262715847740876551924495 394073771611314827886743)
        ·
          refine ⟨591110657416972241830115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394073771611314827886743 591110657416972241830115)
          ·
            refine ⟨886665986125458362745173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591110657416972241830115 886665986125458362745173)
            ·
              refine ⟨2597654256226928797105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 886665986125458362745173 2597654256226928797105)
              ·
                rfl

theorem cell22_204886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 10].length) (baseStart_204886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204886 prefixEnd_204886 := by exact prefixLift 204886
  have htrace : WordTrace (prefixWord ++ tailWord_204886) baseStart_204886 baseEnd_204886 := by
    simpa [prefixWord, tailWord_204886, baseEnd_204886] using wordTrace_append hprefix tailTrace_204886
  have hstable : (prefixWord ++ tailWord_204886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204886).length < 2 ^ (prefixWord ++ tailWord_204886).sum := by decide
  have hdescent : baseEnd_204886 < baseStart_204886 := by decide
  rcases family_descends (prefixWord ++ tailWord_204886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204901 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 3, 3]
def baseStart_204901 : Nat := 118140960795 + 204901 * 2 ^ 59
def prefixEnd_204901 : Nat := 4983230072969 + 3 ^ 40 * 204901 * 2
def baseEnd_204901 : Nat := 70141799724672038396789

theorem tailTrace_204901 : CollatzResearch.WordTrace tailWord_204901 prefixEnd_204901 70141799724672038396789 := by
  unfold tailWord_204901
  simp only [CollatzResearch.WordTrace]
  refine ⟨7473353430686146149870557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4982235620457430766580371 7473353430686146149870557)
  ·
    refine ⟨2802507536507304806201459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7473353430686146149870557 2802507536507304806201459)
    ·
      refine ⟨4203761304760957209302189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2802507536507304806201459 4203761304760957209302189)
      ·
        refine ⟨1576410489285358953488321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4203761304760957209302189 1576410489285358953488321)
        ·
          refine ⟨1182307866964019215116241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1576410489285358953488321 1182307866964019215116241)
          ·
            refine ⟨886730900223014411337181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1182307866964019215116241 886730900223014411337181)
            ·
              refine ⟨332524087583630404251443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 886730900223014411337181 332524087583630404251443)
              ·
                refine ⟨498786131375445606377165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332524087583630404251443 498786131375445606377165)
                ·
                  refine ⟨187044799265792102391437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498786131375445606377165 187044799265792102391437)
                  ·
                    refine ⟨70141799724672038396789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187044799265792102391437 70141799724672038396789)
                    ·
                      rfl

theorem cell22_204901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_204901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204901 prefixEnd_204901 := by exact prefixLift 204901
  have htrace : WordTrace (prefixWord ++ tailWord_204901) baseStart_204901 baseEnd_204901 := by
    simpa [prefixWord, tailWord_204901, baseEnd_204901] using wordTrace_append hprefix tailTrace_204901
  have hstable : (prefixWord ++ tailWord_204901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204901).length < 2 ^ (prefixWord ++ tailWord_204901).sum := by decide
  have hdescent : baseEnd_204901 < baseStart_204901 := by decide
  rcases family_descends (prefixWord ++ tailWord_204901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204952 : List Nat := [2, 1, 2, 4, 3, 2, 2, 2, 1, 3]
def baseStart_204952 : Nat := 118140960795 + 204952 * 2 ^ 59
def prefixEnd_204952 : Nat := 4983230072969 + 3 ^ 40 * 204952 * 2
def baseEnd_204952 : Nat := 70159258066924905371633

theorem tailTrace_204952 : CollatzResearch.WordTrace tailWord_204952 prefixEnd_204952 70159258066924905371633 := by
  unfold tailWord_204952
  simp only [CollatzResearch.WordTrace]
  refine ⟨3737606776750690929988555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4983475702334254573318073 3737606776750690929988555)
  ·
    refine ⟨5606410165126036394982833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3737606776750690929988555 5606410165126036394982833)
    ·
      refine ⟨4204807623844527296237125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5606410165126036394982833 4204807623844527296237125)
      ·
        refine ⟨788401429470848868044461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4204807623844527296237125 788401429470848868044461)
        ·
          refine ⟨295650536051568325516673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 788401429470848868044461 295650536051568325516673)
          ·
            refine ⟨221737902038676244137505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295650536051568325516673 221737902038676244137505)
            ·
              refine ⟨166303426529007183103129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221737902038676244137505 166303426529007183103129)
              ·
                refine ⟨124727569896755387327347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166303426529007183103129 124727569896755387327347)
                ·
                  refine ⟨187091354845133080991021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124727569896755387327347 187091354845133080991021)
                  ·
                    refine ⟨70159258066924905371633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187091354845133080991021 70159258066924905371633)
                    ·
                      rfl

theorem cell22_204952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_204952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204952 prefixEnd_204952 := by exact prefixLift 204952
  have htrace : WordTrace (prefixWord ++ tailWord_204952) baseStart_204952 baseEnd_204952 := by
    simpa [prefixWord, tailWord_204952, baseEnd_204952] using wordTrace_append hprefix tailTrace_204952
  have hstable : (prefixWord ++ tailWord_204952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204952).length < 2 ^ (prefixWord ++ tailWord_204952).sum := by decide
  have hdescent : baseEnd_204952 < baseStart_204952 := by decide
  rcases family_descends (prefixWord ++ tailWord_204952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205036 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 3, 3]
def baseStart_205036 : Nat := 118140960795 + 205036 * 2 ^ 59
def prefixEnd_205036 : Nat := 4983230072969 + 3 ^ 40 * 205036 * 2
def baseEnd_205036 : Nat := 70188012983576686271375

theorem tailTrace_205036 : CollatzResearch.WordTrace tailWord_205036 prefixEnd_205036 70188012983576686271375 := by
  unfold tailWord_205036
  simp only [CollatzResearch.WordTrace]
  refine ⟨3739138642598532103017481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4985518190131376137356641 3739138642598532103017481)
  ·
    refine ⟨2804353981948899077263111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3739138642598532103017481 2804353981948899077263111)
    ·
      refine ⟨4206530972923348615894667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2804353981948899077263111 4206530972923348615894667)
      ·
        refine ⟨6309796459385022923842001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4206530972923348615894667 6309796459385022923842001)
        ·
          refine ⟨4732347344538767192881501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6309796459385022923842001 4732347344538767192881501)
          ·
            refine ⟨1774630254202037697330563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4732347344538767192881501 1774630254202037697330563)
            ·
              refine ⟨2661945381303056545995845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774630254202037697330563 2661945381303056545995845)
              ·
                refine ⟨499114758994323102374221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2661945381303056545995845 499114758994323102374221)
                ·
                  refine ⟨187168034622871163390333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499114758994323102374221 187168034622871163390333)
                  ·
                    refine ⟨70188012983576686271375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187168034622871163390333 70188012983576686271375)
                    ·
                      rfl

theorem cell22_205036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_205036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205036 prefixEnd_205036 := by exact prefixLift 205036
  have htrace : WordTrace (prefixWord ++ tailWord_205036) baseStart_205036 baseEnd_205036 := by
    simpa [prefixWord, tailWord_205036, baseEnd_205036] using wordTrace_append hprefix tailTrace_205036
  have hstable : (prefixWord ++ tailWord_205036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205036).length < 2 ^ (prefixWord ++ tailWord_205036).sum := by decide
  have hdescent : baseEnd_205036 < baseStart_205036 := by decide
  rcases family_descends (prefixWord ++ tailWord_205036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205121 : List Nat := [1, 2, 5, 2, 3, 1, 2, 2, 1, 3]
def baseStart_205121 : Nat := 118140960795 + 205121 * 2 ^ 59
def prefixEnd_205121 : Nat := 4983230072969 + 3 ^ 40 * 205121 * 2
def baseEnd_205121 : Nat := 70217110220664797896115

theorem tailTrace_205121 : CollatzResearch.WordTrace tailWord_205121 prefixEnd_205121 70217110220664797896115 := by
  unfold tailWord_205121
  simp only [CollatzResearch.WordTrace]
  refine ⟨7481377489889123722879217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4987584993259415815252811 7481377489889123722879217)
  ·
    refine ⟨5611033117416842792159413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7481377489889123722879217 5611033117416842792159413)
    ·
      refine ⟨526034354757829011764945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5611033117416842792159413 526034354757829011764945)
      ·
        refine ⟨394525766068371758823709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526034354757829011764945 394525766068371758823709)
        ·
          refine ⟨147947162275639409558891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394525766068371758823709 147947162275639409558891)
          ·
            refine ⟨221920743413459114338337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147947162275639409558891 221920743413459114338337)
            ·
              refine ⟨166440557560094335753753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221920743413459114338337 166440557560094335753753)
              ·
                refine ⟨124830418170070751815315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166440557560094335753753 124830418170070751815315)
                ·
                  refine ⟨187245627255106127722973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124830418170070751815315 187245627255106127722973)
                  ·
                    refine ⟨70217110220664797896115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187245627255106127722973 70217110220664797896115)
                    ·
                      rfl

theorem cell22_205121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_205121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205121 prefixEnd_205121 := by exact prefixLift 205121
  have htrace : WordTrace (prefixWord ++ tailWord_205121) baseStart_205121 baseEnd_205121 := by
    simpa [prefixWord, tailWord_205121, baseEnd_205121] using wordTrace_append hprefix tailTrace_205121
  have hstable : (prefixWord ++ tailWord_205121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205121).length < 2 ^ (prefixWord ++ tailWord_205121).sum := by decide
  have hdescent : baseEnd_205121 < baseStart_205121 := by decide
  rcases family_descends (prefixWord ++ tailWord_205121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205139 : List Nat := [1, 1, 1, 2, 1, 1, 4, 11]
def baseStart_205139 : Nat := 118140960795 + 205139 * 2 ^ 59
def prefixEnd_205139 : Nat := 4983230072969 + 3 ^ 40 * 205139 * 2
def baseEnd_205139 : Nat := 7802585776502083438451

theorem tailTrace_205139 : CollatzResearch.WordTrace tailWord_205139 prefixEnd_205139 7802585776502083438451 := by
  unfold tailWord_205139
  simp only [CollatzResearch.WordTrace]
  refine ⟨7482034003823912797034471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4988022669215941864689647 7482034003823912797034471)
  ·
    refine ⟨11223051005735869195551707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7482034003823912797034471 11223051005735869195551707)
    ·
      refine ⟨16834576508603803793327561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11223051005735869195551707 16834576508603803793327561)
      ·
        refine ⟨12625932381452852844995671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16834576508603803793327561 12625932381452852844995671)
        ·
          refine ⟨18938898572179279267493507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12625932381452852844995671 18938898572179279267493507)
          ·
            refine ⟨28408347858268918901240261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18938898572179279267493507 28408347858268918901240261)
            ·
              refine ⟨5326565223425422293982549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28408347858268918901240261 5326565223425422293982549)
              ·
                refine ⟨7802585776502083438451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 5326565223425422293982549 7802585776502083438451)
                ·
                  rfl

theorem cell22_205139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 11].length) (baseStart_205139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205139 prefixEnd_205139 := by exact prefixLift 205139
  have htrace : WordTrace (prefixWord ++ tailWord_205139) baseStart_205139 baseEnd_205139 := by
    simpa [prefixWord, tailWord_205139, baseEnd_205139] using wordTrace_append hprefix tailTrace_205139
  have hstable : (prefixWord ++ tailWord_205139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205139).length < 2 ^ (prefixWord ++ tailWord_205139).sum := by decide
  have hdescent : baseEnd_205139 < baseStart_205139 := by decide
  rcases family_descends (prefixWord ++ tailWord_205139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205143 : List Nat := [1, 1, 3, 2, 3, 1, 1, 5, 2, 3]
def baseStart_205143 : Nat := 118140960795 + 205143 * 2 ^ 59
def prefixEnd_205143 : Nat := 4983230072969 + 3 ^ 40 * 205143 * 2
def baseEnd_205143 : Nat := 70224641270264073846047

theorem tailTrace_205143 : CollatzResearch.WordTrace tailWord_205143 prefixEnd_205143 70224641270264073846047 := by
  unfold tailWord_205143
  simp only [CollatzResearch.WordTrace]
  refine ⟨7482179895809421480180083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4988119930539614320120055 7482179895809421480180083)
  ·
    refine ⟨11223269843714132220270125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7482179895809421480180083 11223269843714132220270125)
    ·
      refine ⟨4208726191392799582601297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11223269843714132220270125 4208726191392799582601297)
      ·
        refine ⟨3156544643544599686950973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4208726191392799582601297 3156544643544599686950973)
        ·
          refine ⟨1183704241329224882606615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3156544643544599686950973 1183704241329224882606615)
          ·
            refine ⟨1775556361993837323909923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183704241329224882606615 1775556361993837323909923)
            ·
              refine ⟨2663334542990755985864885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775556361993837323909923 2663334542990755985864885)
              ·
                refine ⟨249687613405383373674833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2663334542990755985864885 249687613405383373674833)
                ·
                  refine ⟨187265710054037530256125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249687613405383373674833 187265710054037530256125)
                  ·
                    refine ⟨70224641270264073846047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187265710054037530256125 70224641270264073846047)
                    ·
                      rfl

theorem cell22_205143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_205143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205143 prefixEnd_205143 := by exact prefixLift 205143
  have htrace : WordTrace (prefixWord ++ tailWord_205143) baseStart_205143 baseEnd_205143 := by
    simpa [prefixWord, tailWord_205143, baseEnd_205143] using wordTrace_append hprefix tailTrace_205143
  have hstable : (prefixWord ++ tailWord_205143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205143).length < 2 ^ (prefixWord ++ tailWord_205143).sum := by decide
  have hdescent : baseEnd_205143 < baseStart_205143 := by decide
  rcases family_descends (prefixWord ++ tailWord_205143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205194 : List Nat := [3, 1, 2, 5, 1, 1, 3, 1, 2, 3]
def baseStart_205194 : Nat := 118140960795 + 205194 * 2 ^ 59
def prefixEnd_205194 : Nat := 4983230072969 + 3 ^ 40 * 205194 * 2
def baseEnd_205194 : Nat := 70242099612516940820891

theorem tailTrace_205194 : CollatzResearch.WordTrace tailWord_205194 prefixEnd_205194 70242099612516940820891 := by
  unfold tailWord_205194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871010004656164297571659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4989360012416438126857757 1871010004656164297571659)
  ·
    refine ⟨2806515006984246446357489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1871010004656164297571659 2806515006984246446357489)
    ·
      refine ⟨2104886255238184834768117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2806515006984246446357489 2104886255238184834768117)
      ·
        refine ⟨197333086428579828259511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2104886255238184834768117 197333086428579828259511)
        ·
          refine ⟨295999629642869742389267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197333086428579828259511 295999629642869742389267)
          ·
            refine ⟨443999444464304613583901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295999629642869742389267 443999444464304613583901)
            ·
              refine ⟨166499791674114230093963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 443999444464304613583901 166499791674114230093963)
              ·
                refine ⟨249749687511171345140945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166499791674114230093963 249749687511171345140945)
                ·
                  refine ⟨187312265633378508855709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249749687511171345140945 187312265633378508855709)
                  ·
                    refine ⟨70242099612516940820891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187312265633378508855709 70242099612516940820891)
                    ·
                      rfl

theorem cell22_205194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_205194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205194 prefixEnd_205194 := by exact prefixLift 205194
  have htrace : WordTrace (prefixWord ++ tailWord_205194) baseStart_205194 baseEnd_205194 := by
    simpa [prefixWord, tailWord_205194, baseEnd_205194] using wordTrace_append hprefix tailTrace_205194
  have hstable : (prefixWord ++ tailWord_205194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205194).length < 2 ^ (prefixWord ++ tailWord_205194).sum := by decide
  have hdescent : baseEnd_205194 < baseStart_205194 := by decide
  rcases family_descends (prefixWord ++ tailWord_205194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205231 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 7, 4]
def baseStart_205231 : Nat := 118140960795 + 205231 * 2 ^ 59
def prefixEnd_205231 : Nat := 4983230072969 + 3 ^ 40 * 205231 * 2
def baseEnd_205231 : Nat := 70254765468661177645777

theorem tailTrace_205231 : CollatzResearch.WordTrace tailWord_205231 prefixEnd_205231 70254765468661177645777 := by
  unfold tailWord_205231
  simp only [CollatzResearch.WordTrace]
  refine ⟨7485389519490612509383547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4990259679660408339589031 7485389519490612509383547)
  ·
    refine ⟨11228084279235918764075321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7485389519490612509383547 11228084279235918764075321)
    ·
      refine ⟨8421063209426939073056491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11228084279235918764075321 8421063209426939073056491)
      ·
        refine ⟨12631594814140408609584737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8421063209426939073056491 12631594814140408609584737)
        ·
          refine ⟨9473696110605306457188553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12631594814140408609584737 9473696110605306457188553)
          ·
            refine ⟨7105272082953979842891415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9473696110605306457188553 7105272082953979842891415)
            ·
              refine ⟨10657908124430969764337123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7105272082953979842891415 10657908124430969764337123)
              ·
                refine ⟨15986862186646454646505685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10657908124430969764337123 15986862186646454646505685)
                ·
                  refine ⟨374692082499526280777477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15986862186646454646505685 374692082499526280777477)
                  ·
                    refine ⟨70254765468661177645777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 374692082499526280777477 70254765468661177645777)
                    ·
                      rfl

theorem cell22_205231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_205231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205231 prefixEnd_205231 := by exact prefixLift 205231
  have htrace : WordTrace (prefixWord ++ tailWord_205231) baseStart_205231 baseEnd_205231 := by
    simpa [prefixWord, tailWord_205231, baseEnd_205231] using wordTrace_append hprefix tailTrace_205231
  have hstable : (prefixWord ++ tailWord_205231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205231).length < 2 ^ (prefixWord ++ tailWord_205231).sum := by decide
  have hdescent : baseEnd_205231 < baseStart_205231 := by decide
  rcases family_descends (prefixWord ++ tailWord_205231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205368 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 2, 5]
def baseStart_205368 : Nat := 118140960795 + 205368 * 2 ^ 59
def prefixEnd_205368 : Nat := 4983230072969 + 3 ^ 40 * 205368 * 2
def baseEnd_205368 : Nat := 70301663368438486970357

theorem tailTrace_205368 : CollatzResearch.WordTrace tailWord_205368 prefixEnd_205368 70301663368438486970357 := by
  unfold tailWord_205368
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745193159997142453560379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4993590879996189938080505 3745193159997142453560379)
  ·
    refine ⟨5617789739995713680340569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3745193159997142453560379 5617789739995713680340569)
    ·
      refine ⟨4213342304996785260255427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5617789739995713680340569 4213342304996785260255427)
      ·
        refine ⟨6320013457495177890383141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4213342304996785260255427 6320013457495177890383141)
        ·
          refine ⟨1185002523280345854446839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6320013457495177890383141 1185002523280345854446839)
          ·
            refine ⟨1777503784920518781670259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185002523280345854446839 1777503784920518781670259)
            ·
              refine ⟨2666255677380778172505389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777503784920518781670259 2666255677380778172505389)
              ·
                refine ⟨999845879017791814689521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2666255677380778172505389 999845879017791814689521)
                ·
                  refine ⟨749884409263343861017141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 999845879017791814689521 749884409263343861017141)
                  ·
                    refine ⟨70301663368438486970357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 749884409263343861017141 70301663368438486970357)
                    ·
                      rfl

theorem cell22_205368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_205368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205368 prefixEnd_205368 := by exact prefixLift 205368
  have htrace : WordTrace (prefixWord ++ tailWord_205368) baseStart_205368 baseEnd_205368 := by
    simpa [prefixWord, tailWord_205368, baseEnd_205368] using wordTrace_append hprefix tailTrace_205368
  have hstable : (prefixWord ++ tailWord_205368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205368).length < 2 ^ (prefixWord ++ tailWord_205368).sum := by decide
  have hdescent : baseEnd_205368 < baseStart_205368 := by decide
  rcases family_descends (prefixWord ++ tailWord_205368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205400 : List Nat := [2, 1, 2, 2, 1, 2, 4, 3, 1, 4]
def baseStart_205400 : Nat := 118140960795 + 205400 * 2 ^ 59
def prefixEnd_205400 : Nat := 4983230072969 + 3 ^ 40 * 205400 * 2
def baseEnd_205400 : Nat := 70312617622401070170259

theorem tailTrace_205400 : CollatzResearch.WordTrace tailWord_205400 prefixEnd_205400 70312617622401070170259 := by
  unfold tailWord_205400
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745776727939177186142827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4994368970585569581523769 3745776727939177186142827)
  ·
    refine ⟨5618665091908765779214241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3745776727939177186142827 5618665091908765779214241)
    ·
      refine ⟨4213998818931574334410681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5618665091908765779214241 4213998818931574334410681)
      ·
        refine ⟨3160499114198680750808011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4213998818931574334410681 3160499114198680750808011)
        ·
          refine ⟨4740748671298021126212017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3160499114198680750808011 4740748671298021126212017)
          ·
            refine ⟨3555561503473515844659013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4740748671298021126212017 3555561503473515844659013)
            ·
              refine ⟨666667781901284220873565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3555561503473515844659013 666667781901284220873565)
              ·
                refine ⟨250000418212981582827587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 666667781901284220873565 250000418212981582827587)
                ·
                  refine ⟨375000627319472374241381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250000418212981582827587 375000627319472374241381)
                  ·
                    refine ⟨70312617622401070170259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 375000627319472374241381 70312617622401070170259)
                    ·
                      rfl

theorem cell22_205400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_205400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205400 prefixEnd_205400 := by exact prefixLift 205400
  have htrace : WordTrace (prefixWord ++ tailWord_205400) baseStart_205400 baseEnd_205400 := by
    simpa [prefixWord, tailWord_205400, baseEnd_205400] using wordTrace_append hprefix tailTrace_205400
  have hstable : (prefixWord ++ tailWord_205400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205400).length < 2 ^ (prefixWord ++ tailWord_205400).sum := by decide
  have hdescent : baseEnd_205400 < baseStart_205400 := by decide
  rcases family_descends (prefixWord ++ tailWord_205400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205443 : List Nat := [1, 1, 1, 3, 3, 1, 4, 8]
def baseStart_205443 : Nat := 118140960795 + 205443 * 2 ^ 59
def prefixEnd_205443 : Nat := 4983230072969 + 3 ^ 40 * 205443 * 2
def baseEnd_205443 : Nat := 7814148600129254593903

theorem tailTrace_205443 : CollatzResearch.WordTrace tailWord_205443 prefixEnd_205443 7814148600129254593903 := by
  unfold tailWord_205443
  simp only [CollatzResearch.WordTrace]
  refine ⟨7493121794722572716100983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4995414529815048477400655 7493121794722572716100983)
  ·
    refine ⟨11239682692083859074151475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7493121794722572716100983 11239682692083859074151475)
    ·
      refine ⟨16859524038125788611227213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11239682692083859074151475 16859524038125788611227213)
      ·
        refine ⟨6322321514297170729210205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16859524038125788611227213 6322321514297170729210205)
        ·
          refine ⟨2370870567861439023453827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6322321514297170729210205 2370870567861439023453827)
          ·
            refine ⟨3556305851792158535180741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370870567861439023453827 3556305851792158535180741)
            ·
              refine ⟨666807347211029725346389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3556305851792158535180741 666807347211029725346389)
              ·
                refine ⟨7814148600129254593903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 666807347211029725346389 7814148600129254593903)
                ·
                  rfl

theorem cell22_205443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 8].length) (baseStart_205443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205443 prefixEnd_205443 := by exact prefixLift 205443
  have htrace : WordTrace (prefixWord ++ tailWord_205443) baseStart_205443 baseEnd_205443 := by
    simpa [prefixWord, tailWord_205443, baseEnd_205443] using wordTrace_append hprefix tailTrace_205443
  have hstable : (prefixWord ++ tailWord_205443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205443).length < 2 ^ (prefixWord ++ tailWord_205443).sum := by decide
  have hdescent : baseEnd_205443 < baseStart_205443 := by decide
  rcases family_descends (prefixWord ++ tailWord_205443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205445 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_205445 : Nat := 118140960795 + 205445 * 2 ^ 59
def prefixEnd_205445 : Nat := 4983230072969 + 3 ^ 40 * 205445 * 2
def baseEnd_205445 : Nat := 70328022042035952795121

theorem tailTrace_205445 : CollatzResearch.WordTrace tailWord_205445 prefixEnd_205445 70328022042035952795121 := by
  unfold tailWord_205445
  simp only [CollatzResearch.WordTrace]
  refine ⟨7493194740715327057673789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4995463160476884705115859 7493194740715327057673789)
  ·
    refine ⟨2809948027768247646627671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7493194740715327057673789 2809948027768247646627671)
    ·
      refine ⟨4214922041652371469941507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2809948027768247646627671 4214922041652371469941507)
      ·
        refine ⟨6322383062478557204912261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4214922041652371469941507 6322383062478557204912261)
        ·
          refine ⟨1185446824214729475921049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6322383062478557204912261 1185446824214729475921049)
          ·
            refine ⟨889085118161047106940787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1185446824214729475921049 889085118161047106940787)
            ·
              refine ⟨1333627677241570660411181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889085118161047106940787 1333627677241570660411181)
              ·
                refine ⟨500110378965588997654193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1333627677241570660411181 500110378965588997654193)
                ·
                  refine ⟨375082784224191748240645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500110378965588997654193 375082784224191748240645)
                  ·
                    refine ⟨70328022042035952795121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 375082784224191748240645 70328022042035952795121)
                    ·
                      rfl

theorem cell22_205445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_205445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205445 prefixEnd_205445 := by exact prefixLift 205445
  have htrace : WordTrace (prefixWord ++ tailWord_205445) baseStart_205445 baseEnd_205445 := by
    simpa [prefixWord, tailWord_205445, baseEnd_205445] using wordTrace_append hprefix tailTrace_205445
  have hstable : (prefixWord ++ tailWord_205445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205445).length < 2 ^ (prefixWord ++ tailWord_205445).sum := by decide
  have hdescent : baseEnd_205445 < baseStart_205445 := by decide
  rcases family_descends (prefixWord ++ tailWord_205445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205460 : List Nat := [2, 4, 2, 2, 1, 11]
def baseStart_205460 : Nat := 118140960795 + 205460 * 2 ^ 59
def prefixEnd_205460 : Nat := 4983230072969 + 3 ^ 40 * 205460 * 2
def baseEnd_205460 : Nat := 868310578377542144075

theorem tailTrace_205460 : CollatzResearch.WordTrace tailWord_205460 prefixEnd_205460 868310578377542144075 := by
  unfold tailWord_205460
  simp only [CollatzResearch.WordTrace]
  refine ⟨3746870917830492309734917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4995827890440656412979889 3746870917830492309734917)
  ·
    refine ⟨702538297093217308075297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3746870917830492309734917 702538297093217308075297)
    ·
      refine ⟨526903722819912981056473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 702538297093217308075297 526903722819912981056473)
      ·
        refine ⟨395177792114934735792355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526903722819912981056473 395177792114934735792355)
        ·
          refine ⟨592766688172402103688533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395177792114934735792355 592766688172402103688533)
          ·
            refine ⟨868310578377542144075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 592766688172402103688533 868310578377542144075)
            ·
              rfl

theorem cell22_205460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 11].length) (baseStart_205460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205460 prefixEnd_205460 := by exact prefixLift 205460
  have htrace : WordTrace (prefixWord ++ tailWord_205460) baseStart_205460 baseEnd_205460 := by
    simpa [prefixWord, tailWord_205460, baseEnd_205460] using wordTrace_append hprefix tailTrace_205460
  have hstable : (prefixWord ++ tailWord_205460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205460).length < 2 ^ (prefixWord ++ tailWord_205460).sum := by decide
  have hdescent : baseEnd_205460 < baseStart_205460 := by decide
  rcases family_descends (prefixWord ++ tailWord_205460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205488 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 9]
def baseStart_205488 : Nat := 118140960795 + 205488 * 2 ^ 59
def prefixEnd_205488 : Nat := 4983230072969 + 3 ^ 40 * 205488 * 2
def baseEnd_205488 : Nat := 23447580606932724656663

theorem tailTrace_205488 : CollatzResearch.WordTrace tailWord_205488 prefixEnd_205488 23447580606932724656663 := by
  unfold tailWord_205488
  simp only [CollatzResearch.WordTrace]
  refine ⟨3747381539779772700744559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4996508719706363600992745 3747381539779772700744559)
  ·
    refine ⟨5621072309669659051116839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3747381539779772700744559 5621072309669659051116839)
    ·
      refine ⟨8431608464504488576675259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5621072309669659051116839 8431608464504488576675259)
      ·
        refine ⟨12647412696756732865012889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8431608464504488576675259 12647412696756732865012889)
        ·
          refine ⟨9485559522567549648759667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12647412696756732865012889 9485559522567549648759667)
          ·
            refine ⟨14228339283851324473139501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9485559522567549648759667 14228339283851324473139501)
            ·
              refine ⟨5335627231444246677427313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14228339283851324473139501 5335627231444246677427313)
              ·
                refine ⟨4001720423583185008070485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5335627231444246677427313 4001720423583185008070485)
                ·
                  refine ⟨23447580606932724656663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4001720423583185008070485 23447580606932724656663)
                  ·
                    rfl

theorem cell22_205488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_205488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205488 prefixEnd_205488 := by exact prefixLift 205488
  have htrace : WordTrace (prefixWord ++ tailWord_205488) baseStart_205488 baseEnd_205488 := by
    simpa [prefixWord, tailWord_205488, baseEnd_205488] using wordTrace_append hprefix tailTrace_205488
  have hstable : (prefixWord ++ tailWord_205488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205488).length < 2 ^ (prefixWord ++ tailWord_205488).sum := by decide
  have hdescent : baseEnd_205488 < baseStart_205488 := by decide
  rcases family_descends (prefixWord ++ tailWord_205488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205522 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 7]
def baseStart_205522 : Nat := 118140960795 + 205522 * 2 ^ 59
def prefixEnd_205522 : Nat := 4983230072969 + 3 ^ 40 * 205522 * 2
def baseEnd_205522 : Nat := 23451460238544472873295

theorem tailTrace_205522 : CollatzResearch.WordTrace tailWord_205522 prefixEnd_205522 23451460238544472873295 := by
  unfold tailWord_205522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1874000790359092302056705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4997335440957579472151213 1874000790359092302056705)
  ·
    refine ⟨1405500592769319226542529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1874000790359092302056705 1405500592769319226542529)
    ·
      refine ⟨1054125444576989419906897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1405500592769319226542529 1054125444576989419906897)
      ·
        refine ⟨790594083432742064930173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1054125444576989419906897 790594083432742064930173)
        ·
          refine ⟨296472781287278274348815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 790594083432742064930173 296472781287278274348815)
          ·
            refine ⟨444709171930917411523223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296472781287278274348815 444709171930917411523223)
            ·
              refine ⟨667063757896376117284835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444709171930917411523223 667063757896376117284835)
              ·
                refine ⟨1000595636844564175927253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667063757896376117284835 1000595636844564175927253)
                ·
                  refine ⟨23451460238544472873295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1000595636844564175927253 23451460238544472873295)
                  ·
                    rfl

theorem cell22_205522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_205522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205522 prefixEnd_205522 := by exact prefixLift 205522
  have htrace : WordTrace (prefixWord ++ tailWord_205522) baseStart_205522 baseEnd_205522 := by
    simpa [prefixWord, tailWord_205522, baseEnd_205522] using wordTrace_append hprefix tailTrace_205522
  have hstable : (prefixWord ++ tailWord_205522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205522).length < 2 ^ (prefixWord ++ tailWord_205522).sum := by decide
  have hdescent : baseEnd_205522 < baseStart_205522 := by decide
  rcases family_descends (prefixWord ++ tailWord_205522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205539 : List Nat := [1, 1, 1, 7, 1, 2, 3, 1, 5]
def baseStart_205539 : Nat := 118140960795 + 205539 * 2 ^ 59
def prefixEnd_205539 : Nat := 4983230072969 + 3 ^ 40 * 205539 * 2
def baseEnd_205539 : Nat := 23453400054350346981611

theorem tailTrace_205539 : CollatzResearch.WordTrace tailWord_205539 prefixEnd_205539 23453400054350346981611 := by
  unfold tailWord_205539
  simp only [CollatzResearch.WordTrace]
  refine ⟨7496623202374781111595671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4997748801583187407730447 7496623202374781111595671)
  ·
    refine ⟨11244934803562171667393507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7496623202374781111595671 11244934803562171667393507)
    ·
      refine ⟨16867402205343257501090261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11244934803562171667393507 16867402205343257501090261)
      ·
        refine ⟨395329739187732597681803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 16867402205343257501090261 395329739187732597681803)
        ·
          refine ⟨592994608781598896522705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395329739187732597681803 592994608781598896522705)
          ·
            refine ⟨444745956586199172392029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592994608781598896522705 444745956586199172392029)
            ·
              refine ⟨166779733719824689647011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 444745956586199172392029 166779733719824689647011)
              ·
                refine ⟨250169600579737034470517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166779733719824689647011 250169600579737034470517)
                ·
                  refine ⟨23453400054350346981611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250169600579737034470517 23453400054350346981611)
                  ·
                    rfl

theorem cell22_205539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 5].length) (baseStart_205539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205539 prefixEnd_205539 := by exact prefixLift 205539
  have htrace : WordTrace (prefixWord ++ tailWord_205539) baseStart_205539 baseEnd_205539 := by
    simpa [prefixWord, tailWord_205539, baseEnd_205539] using wordTrace_append hprefix tailTrace_205539
  have hstable : (prefixWord ++ tailWord_205539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205539).length < 2 ^ (prefixWord ++ tailWord_205539).sum := by decide
  have hdescent : baseEnd_205539 < baseStart_205539 := by decide
  rcases family_descends (prefixWord ++ tailWord_205539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205552 : List Nat := [2, 1, 1, 1, 3, 1, 6, 2, 1, 4]
def baseStart_205552 : Nat := 118140960795 + 205552 * 2 ^ 59
def prefixEnd_205552 : Nat := 4983230072969 + 3 ^ 40 * 205552 * 2
def baseEnd_205552 : Nat := 70364650328723340369793

theorem tailTrace_205552 : CollatzResearch.WordTrace tailWord_205552 prefixEnd_205552 70364650328723340369793 := by
  unfold tailWord_205552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3748548675663842165909455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4998064900885122887879273 3748548675663842165909455)
  ·
    refine ⟨5622823013495763248864183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3748548675663842165909455 5622823013495763248864183)
    ·
      refine ⟨8434234520243644873296275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5622823013495763248864183 8434234520243644873296275)
      ·
        refine ⟨12651351780365467309944413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8434234520243644873296275 12651351780365467309944413)
        ·
          refine ⟨4744256917637050241229155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12651351780365467309944413 4744256917637050241229155)
          ·
            refine ⟨7116385376455575361843733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744256917637050241229155 7116385376455575361843733)
            ·
              refine ⟨333580564521355095086425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7116385376455575361843733 333580564521355095086425)
              ·
                refine ⟨250185423391016321314819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333580564521355095086425 250185423391016321314819)
                ·
                  refine ⟨375278135086524481972229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250185423391016321314819 375278135086524481972229)
                  ·
                    refine ⟨70364650328723340369793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 375278135086524481972229 70364650328723340369793)
                    ·
                      rfl

theorem cell22_205552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_205552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205552 prefixEnd_205552 := by exact prefixLift 205552
  have htrace : WordTrace (prefixWord ++ tailWord_205552) baseStart_205552 baseEnd_205552 := by
    simpa [prefixWord, tailWord_205552, baseEnd_205552] using wordTrace_append hprefix tailTrace_205552
  have hstable : (prefixWord ++ tailWord_205552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205552).length < 2 ^ (prefixWord ++ tailWord_205552).sum := by decide
  have hdescent : baseEnd_205552 < baseStart_205552 := by decide
  rcases family_descends (prefixWord ++ tailWord_205552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205565 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_205565 : Nat := 118140960795 + 205565 * 2 ^ 59
def prefixEnd_205565 : Nat := 4983230072969 + 3 ^ 40 * 205565 * 2
def baseEnd_205565 : Nat := 70369100494395639794753

theorem tailTrace_205565 : CollatzResearch.WordTrace tailWord_205565 prefixEnd_205565 70369100494395639794753 := by
  unfold tailWord_205565
  simp only [CollatzResearch.WordTrace]
  refine ⟨7497571500280587552042149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4998381000187058368028099 7497571500280587552042149)
  ·
    refine ⟨1405794656302610166007903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7497571500280587552042149 1405794656302610166007903)
    ·
      refine ⟨2108691984453915249011855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1405794656302610166007903 2108691984453915249011855)
      ·
        refine ⟨3163037976680872873517783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108691984453915249011855 3163037976680872873517783)
        ·
          refine ⟨4744556965021309310276675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3163037976680872873517783 4744556965021309310276675)
          ·
            refine ⟨7116835447531963965415013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744556965021309310276675 7116835447531963965415013)
            ·
              refine ⟨1334406646412243243515315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7116835447531963965415013 1334406646412243243515315)
              ·
                refine ⟨2001609969618364865272973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334406646412243243515315 2001609969618364865272973)
                ·
                  refine ⟨750603738606886824477365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2001609969618364865272973 750603738606886824477365)
                  ·
                    refine ⟨70369100494395639794753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 750603738606886824477365 70369100494395639794753)
                    ·
                      rfl

theorem cell22_205565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_205565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205565 prefixEnd_205565 := by exact prefixLift 205565
  have htrace : WordTrace (prefixWord ++ tailWord_205565) baseStart_205565 baseEnd_205565 := by
    simpa [prefixWord, tailWord_205565, baseEnd_205565] using wordTrace_append hprefix tailTrace_205565
  have hstable : (prefixWord ++ tailWord_205565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205565).length < 2 ^ (prefixWord ++ tailWord_205565).sum := by decide
  have hdescent : baseEnd_205565 < baseStart_205565 := by decide
  rcases family_descends (prefixWord ++ tailWord_205565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205599 : List Nat := [1, 1, 2, 4, 2, 3, 1, 3, 2, 3]
def baseStart_205599 : Nat := 118140960795 + 205599 * 2 ^ 59
def prefixEnd_205599 : Nat := 4983230072969 + 3 ^ 40 * 205599 * 2
def baseEnd_205599 : Nat := 70380739389230884444649

theorem tailTrace_205599 : CollatzResearch.WordTrace tailWord_205599 prefixEnd_205599 70380739389230884444649 := by
  unfold tailWord_205599
  simp only [CollatzResearch.WordTrace]
  refine ⟨7498811582157411358779851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4999207721438274239186567 7498811582157411358779851)
  ·
    refine ⟨11248217373236117038169777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7498811582157411358779851 11248217373236117038169777)
    ·
      refine ⟨8436163029927087778627333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11248217373236117038169777 8436163029927087778627333)
      ·
        refine ⟨1581780568111328958492625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8436163029927087778627333 1581780568111328958492625)
        ·
          refine ⟨1186335426083496718869469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1581780568111328958492625 1186335426083496718869469)
          ·
            refine ⟨444875784781311269576051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1186335426083496718869469 444875784781311269576051)
            ·
              refine ⟨667313677171966904364077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444875784781311269576051 667313677171966904364077)
              ·
                refine ⟨250242628939487589136529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 667313677171966904364077 250242628939487589136529)
                ·
                  refine ⟨187681971704615691852397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250242628939487589136529 187681971704615691852397)
                  ·
                    refine ⟨70380739389230884444649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187681971704615691852397 70380739389230884444649)
                    ·
                      rfl

theorem cell22_205599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 3].length) (baseStart_205599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205599 prefixEnd_205599 := by exact prefixLift 205599
  have htrace : WordTrace (prefixWord ++ tailWord_205599) baseStart_205599 baseEnd_205599 := by
    simpa [prefixWord, tailWord_205599, baseEnd_205599] using wordTrace_append hprefix tailTrace_205599
  have hstable : (prefixWord ++ tailWord_205599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205599).length < 2 ^ (prefixWord ++ tailWord_205599).sum := by decide
  have hdescent : baseEnd_205599 < baseStart_205599 := by decide
  rcases family_descends (prefixWord ++ tailWord_205599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205614 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_205614 : Nat := 118140960795 + 205614 * 2 ^ 59
def prefixEnd_205614 : Nat := 4983230072969 + 3 ^ 40 * 205614 * 2
def baseEnd_205614 : Nat := 70385874195775845319603

theorem tailTrace_205614 : CollatzResearch.WordTrace tailWord_205614 prefixEnd_205614 70385874195775845319603 := by
  unfold tailWord_205614
  simp only [CollatzResearch.WordTrace]
  refine ⟨937419834637883615071987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4999572451402045947050597 937419834637883615071987)
  ·
    refine ⟨1406129751956825422607981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 937419834637883615071987 1406129751956825422607981)
    ·
      refine ⟨527298656983809533477993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1406129751956825422607981 527298656983809533477993)
      ·
        refine ⟨395473992737857150108495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527298656983809533477993 395473992737857150108495)
        ·
          refine ⟨593210989106785725162743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395473992737857150108495 593210989106785725162743)
          ·
            refine ⟨889816483660178587744115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593210989106785725162743 889816483660178587744115)
            ·
              refine ⟨1334724725490267881616173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889816483660178587744115 1334724725490267881616173)
              ·
                refine ⟨500521772058850455606065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1334724725490267881616173 500521772058850455606065)
                ·
                  refine ⟨375391329044137841704549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500521772058850455606065 375391329044137841704549)
                  ·
                    refine ⟨70385874195775845319603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 375391329044137841704549 70385874195775845319603)
                    ·
                      rfl

theorem cell22_205614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_205614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205614 prefixEnd_205614 := by exact prefixLift 205614
  have htrace : WordTrace (prefixWord ++ tailWord_205614) baseStart_205614 baseEnd_205614 := by
    simpa [prefixWord, tailWord_205614, baseEnd_205614] using wordTrace_append hprefix tailTrace_205614
  have hstable : (prefixWord ++ tailWord_205614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205614).length < 2 ^ (prefixWord ++ tailWord_205614).sum := by decide
  have hdescent : baseEnd_205614 < baseStart_205614 := by decide
  rcases family_descends (prefixWord ++ tailWord_205614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205633 : List Nat := [1, 2, 5, 3, 1, 1, 2, 2, 2, 3]
def baseStart_205633 : Nat := 118140960795 + 205633 * 2 ^ 59
def prefixEnd_205633 : Nat := 4983230072969 + 3 ^ 40 * 205633 * 2
def baseEnd_205633 : Nat := 70392378284066129094545

theorem tailTrace_205633 : CollatzResearch.WordTrace tailWord_205633 prefixEnd_205633 70392378284066129094545 := by
  unfold tailWord_205633
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500051664034235165517553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5000034442689490110345035 7500051664034235165517553)
  ·
    refine ⟨5625038748025676374138165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7500051664034235165517553 5625038748025676374138165)
    ·
      refine ⟨527347382627407160075453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5625038748025676374138165 527347382627407160075453)
      ·
        refine ⟨197755268485277685028295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 527347382627407160075453 197755268485277685028295)
        ·
          refine ⟨296632902727916527542443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197755268485277685028295 296632902727916527542443)
          ·
            refine ⟨444949354091874791313665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296632902727916527542443 444949354091874791313665)
            ·
              refine ⟨333712015568906093485249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444949354091874791313665 333712015568906093485249)
              ·
                refine ⟨250284011676679570113937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333712015568906093485249 250284011676679570113937)
                ·
                  refine ⟨187713008757509677585453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250284011676679570113937 187713008757509677585453)
                  ·
                    refine ⟨70392378284066129094545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187713008757509677585453 70392378284066129094545)
                    ·
                      rfl

theorem cell22_205633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_205633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205633 prefixEnd_205633 := by exact prefixLift 205633
  have htrace : WordTrace (prefixWord ++ tailWord_205633) baseStart_205633 baseEnd_205633 := by
    simpa [prefixWord, tailWord_205633, baseEnd_205633] using wordTrace_append hprefix tailTrace_205633
  have hstable : (prefixWord ++ tailWord_205633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205633).length < 2 ^ (prefixWord ++ tailWord_205633).sum := by decide
  have hdescent : baseEnd_205633 < baseStart_205633 := by decide
  rcases family_descends (prefixWord ++ tailWord_205633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205657 : List Nat := [1, 2, 1, 2, 2, 4, 2, 3, 5]
def baseStart_205657 : Nat := 118140960795 + 205657 * 2 ^ 59
def prefixEnd_205657 : Nat := 4983230072969 + 3 ^ 40 * 205657 * 2
def baseEnd_205657 : Nat := 23466864658179355498157

theorem tailTrace_205657 : CollatzResearch.WordTrace tailWord_205657 prefixEnd_205657 23466864658179355498157 := by
  unfold tailWord_205657
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500927015947287264391225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5000618010631524842927483 7500927015947287264391225)
  ·
    refine ⟨5625695261960465448293419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7500927015947287264391225 5625695261960465448293419)
    ·
      refine ⟨8438542892940698172440129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5625695261960465448293419 8438542892940698172440129)
      ·
        refine ⟨6328907169705523629330097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8438542892940698172440129 6328907169705523629330097)
        ·
          refine ⟨4746680377279142721997573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6328907169705523629330097 4746680377279142721997573)
          ·
            refine ⟨890002570739839260374545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4746680377279142721997573 890002570739839260374545)
            ·
              refine ⟨667501928054879445280909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890002570739839260374545 667501928054879445280909)
              ·
                refine ⟨250313223020579791980341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 667501928054879445280909 250313223020579791980341)
                ·
                  refine ⟨23466864658179355498157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250313223020579791980341 23466864658179355498157)
                  ·
                    rfl

theorem cell22_205657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 5].length) (baseStart_205657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205657 prefixEnd_205657 := by exact prefixLift 205657
  have htrace : WordTrace (prefixWord ++ tailWord_205657) baseStart_205657 baseEnd_205657 := by
    simpa [prefixWord, tailWord_205657, baseEnd_205657] using wordTrace_append hprefix tailTrace_205657
  have hstable : (prefixWord ++ tailWord_205657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205657).length < 2 ^ (prefixWord ++ tailWord_205657).sum := by decide
  have hdescent : baseEnd_205657 < baseStart_205657 := by decide
  rcases family_descends (prefixWord ++ tailWord_205657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205732 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_205732 : Nat := 118140960795 + 205732 * 2 ^ 59
def prefixEnd_205732 : Nat := 4983230072969 + 3 ^ 40 * 205732 * 2
def baseEnd_205732 : Nat := 70426268007262870869241

theorem tailTrace_205732 : CollatzResearch.WordTrace tailWord_205732 prefixEnd_205732 70426268007262870869241 := by
  unfold tailWord_205732
  simp only [CollatzResearch.WordTrace]
  refine ⟨3751831245337787536685725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5002441660450383382247633 3751831245337787536685725)
  ·
    refine ⟨1406936717001670326257147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3751831245337787536685725 1406936717001670326257147)
    ·
      refine ⟨2110405075502505489385721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1406936717001670326257147 2110405075502505489385721)
      ·
        refine ⟨1582803806626879117039291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2110405075502505489385721 1582803806626879117039291)
        ·
          refine ⟨2374205709940318675558937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582803806626879117039291 2374205709940318675558937)
          ·
            refine ⟨1780654282455239006669203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2374205709940318675558937 1780654282455239006669203)
            ·
              refine ⟨2670981423682858510003805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780654282455239006669203 2670981423682858510003805)
              ·
                refine ⟨1001618033881071941251427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2670981423682858510003805 1001618033881071941251427)
                ·
                  refine ⟨1502427050821607911877141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001618033881071941251427 1502427050821607911877141)
                  ·
                    refine ⟨70426268007262870869241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1502427050821607911877141 70426268007262870869241)
                    ·
                      rfl

theorem cell22_205732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_205732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205732 prefixEnd_205732 := by exact prefixLift 205732
  have htrace : WordTrace (prefixWord ++ tailWord_205732) baseStart_205732 baseEnd_205732 := by
    simpa [prefixWord, tailWord_205732, baseEnd_205732] using wordTrace_append hprefix tailTrace_205732
  have hstable : (prefixWord ++ tailWord_205732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205732).length < 2 ^ (prefixWord ++ tailWord_205732).sum := by decide
  have hdescent : baseEnd_205732 < baseStart_205732 := by decide
  rcases family_descends (prefixWord ++ tailWord_205732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205749 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_205749 : Nat := 118140960795 + 205749 * 2 ^ 59
def prefixEnd_205749 : Nat := 4983230072969 + 3 ^ 40 * 205749 * 2
def baseEnd_205749 : Nat := 70432087454680493194189

theorem tailTrace_205749 : CollatzResearch.WordTrace tailWord_205749 prefixEnd_205749 70432087454680493194189 := by
  unfold tailWord_205749
  simp only [CollatzResearch.WordTrace]
  refine ⟨7504282531613986976740301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5002855021075991317826867 7504282531613986976740301)
  ·
    refine ⟨2814105949355245116277613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7504282531613986976740301 2814105949355245116277613)
    ·
      refine ⟨1055289731008216918604105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2814105949355245116277613 1055289731008216918604105)
      ·
        refine ⟨791467298256162688953079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1055289731008216918604105 791467298256162688953079)
        ·
          refine ⟨1187200947384244033429619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791467298256162688953079 1187200947384244033429619)
          ·
            refine ⟨1780801421076366050144429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187200947384244033429619 1780801421076366050144429)
            ·
              refine ⟨667800532903637268804161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1780801421076366050144429 667800532903637268804161)
              ·
                refine ⟨500850399677727951603121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667800532903637268804161 500850399677727951603121)
                ·
                  refine ⟨375637799758295963702341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500850399677727951603121 375637799758295963702341)
                  ·
                    refine ⟨70432087454680493194189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 375637799758295963702341 70432087454680493194189)
                    ·
                      rfl

theorem cell22_205749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_205749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205749 prefixEnd_205749 := by exact prefixLift 205749
  have htrace : WordTrace (prefixWord ++ tailWord_205749) baseStart_205749 baseEnd_205749 := by
    simpa [prefixWord, tailWord_205749, baseEnd_205749] using wordTrace_append hprefix tailTrace_205749
  have hstable : (prefixWord ++ tailWord_205749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205749).length < 2 ^ (prefixWord ++ tailWord_205749).sum := by decide
  have hdescent : baseEnd_205749 < baseStart_205749 := by decide
  rcases family_descends (prefixWord ++ tailWord_205749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205809 : List Nat := [1, 2, 2, 2, 4, 1, 1, 4, 5]
def baseStart_205809 : Nat := 118140960795 + 205809 * 2 ^ 59
def prefixEnd_205809 : Nat := 4983230072969 + 3 ^ 40 * 205809 * 2
def baseEnd_205809 : Nat := 23484208893620112231335

theorem tailTrace_205809 : CollatzResearch.WordTrace tailWord_205809 prefixEnd_205809 23484208893620112231335 := by
  unfold tailWord_205809
  simp only [CollatzResearch.WordTrace]
  refine ⟨7506470911396617223924481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5004313940931078149282987 7506470911396617223924481)
  ·
    refine ⟨5629853183547462917943361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7506470911396617223924481 5629853183547462917943361)
    ·
      refine ⟨4222389887660597188457521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5629853183547462917943361 4222389887660597188457521)
      ·
        refine ⟨3166792415745447891343141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4222389887660597188457521 3166792415745447891343141)
        ·
          refine ⟨593773577952271479626839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3166792415745447891343141 593773577952271479626839)
          ·
            refine ⟨890660366928407219440259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593773577952271479626839 890660366928407219440259)
            ·
              refine ⟨1335990550392610829160389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890660366928407219440259 1335990550392610829160389)
              ·
                refine ⟨250498228198614530467573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1335990550392610829160389 250498228198614530467573)
                ·
                  refine ⟨23484208893620112231335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250498228198614530467573 23484208893620112231335)
                  ·
                    rfl

theorem cell22_205809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 5].length) (baseStart_205809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205809 prefixEnd_205809 := by exact prefixLift 205809
  have htrace : WordTrace (prefixWord ++ tailWord_205809) baseStart_205809 baseEnd_205809 := by
    simpa [prefixWord, tailWord_205809, baseEnd_205809] using wordTrace_append hprefix tailTrace_205809
  have hstable : (prefixWord ++ tailWord_205809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205809).length < 2 ^ (prefixWord ++ tailWord_205809).sum := by decide
  have hdescent : baseEnd_205809 < baseStart_205809 := by decide
  rcases family_descends (prefixWord ++ tailWord_205809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205884 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_205884 : Nat := 118140960795 + 205884 * 2 ^ 59
def prefixEnd_205884 : Nat := 4983230072969 + 3 ^ 40 * 205884 * 2
def baseEnd_205884 : Nat := 70478300713585141068775

theorem tailTrace_205884 : CollatzResearch.WordTrace tailWord_205884 prefixEnd_205884 70478300713585141068775 := by
  unfold tailWord_205884
  simp only [CollatzResearch.WordTrace]
  refine ⟨3754603193062452516452353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5006137590749936688603137 3754603193062452516452353)
  ·
    refine ⟨2815952394796839387339265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3754603193062452516452353 2815952394796839387339265)
    ·
      refine ⟨2111964296097629540504449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2815952394796839387339265 2111964296097629540504449)
      ·
        refine ⟨1583973222073222155378337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2111964296097629540504449 1583973222073222155378337)
        ·
          refine ⟨1187979916554916616533753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1583973222073222155378337 1187979916554916616533753)
          ·
            refine ⟨890984937416187462400315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1187979916554916616533753 890984937416187462400315)
            ·
              refine ⟨1336477406124281193600473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890984937416187462400315 1336477406124281193600473)
              ·
                refine ⟨1002358054593210895200355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336477406124281193600473 1002358054593210895200355)
                ·
                  refine ⟨1503537081889816342800533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002358054593210895200355 1503537081889816342800533)
                  ·
                    refine ⟨70478300713585141068775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1503537081889816342800533 70478300713585141068775)
                    ·
                      rfl

theorem cell22_205884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_205884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205884 prefixEnd_205884 := by exact prefixLift 205884
  have htrace : WordTrace (prefixWord ++ tailWord_205884) baseStart_205884 baseEnd_205884 := by
    simpa [prefixWord, tailWord_205884, baseEnd_205884] using wordTrace_append hprefix tailTrace_205884
  have hstable : (prefixWord ++ tailWord_205884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205884).length < 2 ^ (prefixWord ++ tailWord_205884).sum := by decide
  have hdescent : baseEnd_205884 < baseStart_205884 := by decide
  rcases family_descends (prefixWord ++ tailWord_205884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205901 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_205901 : Nat := 118140960795 + 205901 * 2 ^ 59
def prefixEnd_205901 : Nat := 4983230072969 + 3 ^ 40 * 205901 * 2
def baseEnd_205901 : Nat := 70484120161002763393723

theorem tailTrace_205901 : CollatzResearch.WordTrace tailWord_205901 prefixEnd_205901 70484120161002763393723 := by
  unfold tailWord_205901
  simp only [CollatzResearch.WordTrace]
  refine ⟨7509826427063316936273557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5006550951375544624182371 7509826427063316936273557)
  ·
    refine ⟨352023113768592981387823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7509826427063316936273557 352023113768592981387823)
    ·
      refine ⟨528034670652889472081735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352023113768592981387823 528034670652889472081735)
      ·
        refine ⟨792052005979334208122603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528034670652889472081735 792052005979334208122603)
        ·
          refine ⟨1188078008969001312183905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792052005979334208122603 1188078008969001312183905)
          ·
            refine ⟨891058506726750984137929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188078008969001312183905 891058506726750984137929)
            ·
              refine ⟨668293880045063238103447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891058506726750984137929 668293880045063238103447)
              ·
                refine ⟨1002440820067594857155171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668293880045063238103447 1002440820067594857155171)
                ·
                  refine ⟨1503661230101392285732757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002440820067594857155171 1503661230101392285732757)
                  ·
                    refine ⟨70484120161002763393723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1503661230101392285732757 70484120161002763393723)
                    ·
                      rfl

theorem cell22_205901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_205901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205901 prefixEnd_205901 := by exact prefixLift 205901
  have htrace : WordTrace (prefixWord ++ tailWord_205901) baseStart_205901 baseEnd_205901 := by
    simpa [prefixWord, tailWord_205901, baseEnd_205901] using wordTrace_append hprefix tailTrace_205901
  have hstable : (prefixWord ++ tailWord_205901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205901).length < 2 ^ (prefixWord ++ tailWord_205901).sum := by decide
  have hdescent : baseEnd_205901 < baseStart_205901 := by decide
  rcases family_descends (prefixWord ++ tailWord_205901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205959 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 4, 5]
def baseStart_205959 : Nat := 118140960795 + 205959 * 2 ^ 59
def prefixEnd_205959 : Nat := 4983230072969 + 3 ^ 40 * 205959 * 2
def baseEnd_205959 : Nat := 70503974746309945443545

theorem tailTrace_205959 : CollatzResearch.WordTrace tailWord_205959 prefixEnd_205959 70503974746309945443545 := by
  unfold tailWord_205959
  simp only [CollatzResearch.WordTrace]
  refine ⟨7511941860853192841884931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5007961240568795227923287 7511941860853192841884931)
  ·
    refine ⟨11267912791279789262827397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7511941860853192841884931 11267912791279789262827397)
    ·
      refine ⟨2112733648364960486780137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11267912791279789262827397 2112733648364960486780137)
      ·
        refine ⟨1584550236273720365085103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2112733648364960486780137 1584550236273720365085103)
        ·
          refine ⟨2376825354410580547627655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1584550236273720365085103 2376825354410580547627655)
          ·
            refine ⟨3565238031615870821441483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376825354410580547627655 3565238031615870821441483)
            ·
              refine ⟨5347857047423806232162225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3565238031615870821441483 5347857047423806232162225)
              ·
                refine ⟨4010892785567854674121669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5347857047423806232162225 4010892785567854674121669)
                ·
                  refine ⟨752042397293972751397813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4010892785567854674121669 752042397293972751397813)
                  ·
                    refine ⟨70503974746309945443545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 752042397293972751397813 70503974746309945443545)
                    ·
                      rfl

theorem cell22_205959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_205959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205959 prefixEnd_205959 := by exact prefixLift 205959
  have htrace : WordTrace (prefixWord ++ tailWord_205959) baseStart_205959 baseEnd_205959 := by
    simpa [prefixWord, tailWord_205959, baseEnd_205959] using wordTrace_append hprefix tailTrace_205959
  have hstable : (prefixWord ++ tailWord_205959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205959).length < 2 ^ (prefixWord ++ tailWord_205959).sum := by decide
  have hdescent : baseEnd_205959 < baseStart_205959 := by decide
  rcases family_descends (prefixWord ++ tailWord_205959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205978 : List Nat := [3, 1, 1, 5, 1, 2, 2, 2, 5]
def baseStart_205978 : Nat := 118140960795 + 205978 * 2 ^ 59
def prefixEnd_205978 : Nat := 4983230072969 + 3 ^ 40 * 205978 * 2
def baseEnd_205978 : Nat := 23503492944866743072829

theorem tailTrace_205978 : CollatzResearch.WordTrace tailWord_205978 prefixEnd_205978 23503492944866743072829 := by
  unfold tailWord_205978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878158711946089771706647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5008423231856239391217725 1878158711946089771706647)
  ·
    refine ⟨2817238067919134657559971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1878158711946089771706647 2817238067919134657559971)
    ·
      refine ⟨4225857101878701986339957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2817238067919134657559971 4225857101878701986339957)
      ·
        refine ⟨396174103301128311219371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4225857101878701986339957 396174103301128311219371)
        ·
          refine ⟨594261154951692466829057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396174103301128311219371 594261154951692466829057)
          ·
            refine ⟨445695866213769350121793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594261154951692466829057 445695866213769350121793)
            ·
              refine ⟨334271899660327012591345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445695866213769350121793 334271899660327012591345)
              ·
                refine ⟨250703924745245259443509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334271899660327012591345 250703924745245259443509)
                ·
                  refine ⟨23503492944866743072829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250703924745245259443509 23503492944866743072829)
                  ·
                    rfl

theorem cell22_205978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_205978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205978 prefixEnd_205978 := by exact prefixLift 205978
  have htrace : WordTrace (prefixWord ++ tailWord_205978) baseStart_205978 baseEnd_205978 := by
    simpa [prefixWord, tailWord_205978, baseEnd_205978] using wordTrace_append hprefix tailTrace_205978
  have hstable : (prefixWord ++ tailWord_205978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205978).length < 2 ^ (prefixWord ++ tailWord_205978).sum := by decide
  have hdescent : baseEnd_205978 < baseStart_205978 := by decide
  rcases family_descends (prefixWord ++ tailWord_205978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205982 : List Nat := [4, 3, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_205982 : Nat := 118140960795 + 205982 * 2 ^ 59
def prefixEnd_205982 : Nat := 4983230072969 + 3 ^ 40 * 205982 * 2
def baseEnd_205982 : Nat := 70511848116345552118475

theorem tailTrace_205982 : CollatzResearch.WordTrace tailWord_205982 prefixEnd_205982 70511848116345552118475 := by
  unfold tailWord_205982
  simp only [CollatzResearch.WordTrace]
  refine ⟨939097592471233471246525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5008520493179911846648133 939097592471233471246525)
  ·
    refine ⟨352161597176712551717447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 939097592471233471246525 352161597176712551717447)
    ·
      refine ⟨528242395765068827576171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352161597176712551717447 528242395765068827576171)
      ·
        refine ⟨792363593647603241364257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528242395765068827576171 792363593647603241364257)
        ·
          refine ⟨594272695235702431023193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792363593647603241364257 594272695235702431023193)
          ·
            refine ⟨445704521426776823267395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594272695235702431023193 445704521426776823267395)
            ·
              refine ⟨668556782140165234901093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445704521426776823267395 668556782140165234901093)
              ·
                refine ⟨125354396651280981543955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 668556782140165234901093 125354396651280981543955)
                ·
                  refine ⟨188031594976921472315933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125354396651280981543955 188031594976921472315933)
                  ·
                    refine ⟨70511848116345552118475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188031594976921472315933 70511848116345552118475)
                    ·
                      rfl

theorem cell22_205982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_205982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_205982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_205982 prefixEnd_205982 := by exact prefixLift 205982
  have htrace : WordTrace (prefixWord ++ tailWord_205982) baseStart_205982 baseEnd_205982 := by
    simpa [prefixWord, tailWord_205982, baseEnd_205982] using wordTrace_append hprefix tailTrace_205982
  have hstable : (prefixWord ++ tailWord_205982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205982).length < 2 ^ (prefixWord ++ tailWord_205982).sum := by decide
  have hdescent : baseEnd_205982 < baseStart_205982 := by decide
  rcases family_descends (prefixWord ++ tailWord_205982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206021 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 4, 3]
def baseStart_206021 : Nat := 118140960795 + 206021 * 2 ^ 59
def prefixEnd_206021 : Nat := 4983230072969 + 3 ^ 40 * 206021 * 2
def baseEnd_206021 : Nat := 70525198613362450393355

theorem tailTrace_206021 : CollatzResearch.WordTrace tailWord_206021 prefixEnd_206021 70525198613362450393355 := by
  unfold tailWord_206021
  simp only [CollatzResearch.WordTrace]
  refine ⟨7514203186628577430641917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5009468791085718287094611 7514203186628577430641917)
  ·
    refine ⟨2817826194985716536490719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7514203186628577430641917 2817826194985716536490719)
    ·
      refine ⟨4226739292478574804736079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2817826194985716536490719 4226739292478574804736079)
      ·
        refine ⟨6340108938717862207104119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4226739292478574804736079 6340108938717862207104119)
        ·
          refine ⟨9510163408076793310656179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6340108938717862207104119 9510163408076793310656179)
          ·
            refine ⟨14265245112115189965984269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9510163408076793310656179 14265245112115189965984269)
            ·
              refine ⟨5349466917043196237244101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14265245112115189965984269 5349466917043196237244101)
              ·
                refine ⟨1003025046945599294483269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5349466917043196237244101 1003025046945599294483269)
                ·
                  refine ⟨188067196302299867715613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003025046945599294483269 188067196302299867715613)
                  ·
                    refine ⟨70525198613362450393355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188067196302299867715613 70525198613362450393355)
                    ·
                      rfl

theorem cell22_206021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_206021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206021 prefixEnd_206021 := by exact prefixLift 206021
  have htrace : WordTrace (prefixWord ++ tailWord_206021) baseStart_206021 baseEnd_206021 := by
    simpa [prefixWord, tailWord_206021, baseEnd_206021] using wordTrace_append hprefix tailTrace_206021
  have hstable : (prefixWord ++ tailWord_206021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206021).length < 2 ^ (prefixWord ++ tailWord_206021).sum := by decide
  have hdescent : baseEnd_206021 < baseStart_206021 := by decide
  rcases family_descends (prefixWord ++ tailWord_206021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206029 : List Nat := [1, 6, 2, 2, 2, 1, 1, 2, 5]
def baseStart_206029 : Nat := 118140960795 + 206029 * 2 ^ 59
def prefixEnd_206029 : Nat := 4983230072969 + 3 ^ 40 * 206029 * 2
def baseEnd_206029 : Nat := 23509312392284365397777

theorem tailTrace_206029 : CollatzResearch.WordTrace tailWord_206029 prefixEnd_206029 23509312392284365397777 := by
  unfold tailWord_206029
  simp only [CollatzResearch.WordTrace]
  refine ⟨7514494970599594796933141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5009663313733063197955427 7514494970599594796933141)
  ·
    refine ⟨352241951746856006106241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7514494970599594796933141 352241951746856006106241)
    ·
      refine ⟨264181463810142004579681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352241951746856006106241 264181463810142004579681)
      ·
        refine ⟨198136097857606503434761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264181463810142004579681 198136097857606503434761)
        ·
          refine ⟨148602073393204877576071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198136097857606503434761 148602073393204877576071)
          ·
            refine ⟨222903110089807316364107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148602073393204877576071 222903110089807316364107)
            ·
              refine ⟨334354665134710974546161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222903110089807316364107 334354665134710974546161)
              ·
                refine ⟨250765998851033230909621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334354665134710974546161 250765998851033230909621)
                ·
                  refine ⟨23509312392284365397777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250765998851033230909621 23509312392284365397777)
                  ·
                    rfl

theorem cell22_206029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_206029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206029 prefixEnd_206029 := by exact prefixLift 206029
  have htrace : WordTrace (prefixWord ++ tailWord_206029) baseStart_206029 baseEnd_206029 := by
    simpa [prefixWord, tailWord_206029, baseEnd_206029] using wordTrace_append hprefix tailTrace_206029
  have hstable : (prefixWord ++ tailWord_206029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206029).length < 2 ^ (prefixWord ++ tailWord_206029).sum := by decide
  have hdescent : baseEnd_206029 < baseStart_206029 := by decide
  rcases family_descends (prefixWord ++ tailWord_206029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206055 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 1, 5]
def baseStart_206055 : Nat := 118140960795 + 206055 * 2 ^ 59
def prefixEnd_206055 : Nat := 4983230072969 + 3 ^ 40 * 206055 * 2
def baseEnd_206055 : Nat := 70536837508197695043251

theorem tailTrace_206055 : CollatzResearch.WordTrace tailWord_206055 prefixEnd_206055 70536837508197695043251 := by
  unfold tailWord_206055
  simp only [CollatzResearch.WordTrace]
  refine ⟨7515443268505401237379619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5010295512336934158253079 7515443268505401237379619)
  ·
    refine ⟨11273164902758101856069429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7515443268505401237379619 11273164902758101856069429)
    ·
      refine ⟨1056859209633572049006509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11273164902758101856069429 1056859209633572049006509)
      ·
        refine ⟨396322203612589518377441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1056859209633572049006509 396322203612589518377441)
        ·
          refine ⟨297241652709442138783081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396322203612589518377441 297241652709442138783081)
          ·
            refine ⟨222931239532081604087311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297241652709442138783081 222931239532081604087311)
            ·
              refine ⟨334396859298122406130967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222931239532081604087311 334396859298122406130967)
              ·
                refine ⟨501595288947183609196451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334396859298122406130967 501595288947183609196451)
                ·
                  refine ⟨752392933420775413794677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501595288947183609196451 752392933420775413794677)
                  ·
                    refine ⟨70536837508197695043251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 752392933420775413794677 70536837508197695043251)
                    ·
                      rfl

theorem cell22_206055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_206055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206055 prefixEnd_206055 := by exact prefixLift 206055
  have htrace : WordTrace (prefixWord ++ tailWord_206055) baseStart_206055 baseEnd_206055 := by
    simpa [prefixWord, tailWord_206055, baseEnd_206055] using wordTrace_append hprefix tailTrace_206055
  have hstable : (prefixWord ++ tailWord_206055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206055).length < 2 ^ (prefixWord ++ tailWord_206055).sum := by decide
  have hdescent : baseEnd_206055 < baseStart_206055 := by decide
  rcases family_descends (prefixWord ++ tailWord_206055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206188 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_206188 : Nat := 118140960795 + 206188 * 2 ^ 59
def prefixEnd_206188 : Nat := 4983230072969 + 3 ^ 40 * 206188 * 2
def baseEnd_206188 : Nat := 70582366126229681467843

theorem tailTrace_206188 : CollatzResearch.WordTrace tailWord_206188 prefixEnd_206188 70582366126229681467843 := by
  unfold tailWord_206188
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760147088511782475985609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5013529451349043301314145 3760147088511782475985609)
  ·
    refine ⟨2820110316383836856989207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3760147088511782475985609 2820110316383836856989207)
    ·
      refine ⟨4230165474575755285483811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2820110316383836856989207 4230165474575755285483811)
      ·
        refine ⟨6345248211863632928225717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4230165474575755285483811 6345248211863632928225717)
        ·
          refine ⟨594867019862215587021161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6345248211863632928225717 594867019862215587021161)
          ·
            refine ⟨446150264896661690265871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594867019862215587021161 446150264896661690265871)
            ·
              refine ⟨669225397344992535398807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446150264896661690265871 669225397344992535398807)
              ·
                refine ⟨1003838096017488803098211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669225397344992535398807 1003838096017488803098211)
                ·
                  refine ⟨1505757144026233204647317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003838096017488803098211 1505757144026233204647317)
                  ·
                    refine ⟨70582366126229681467843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1505757144026233204647317 70582366126229681467843)
                    ·
                      rfl

theorem cell22_206188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_206188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206188 prefixEnd_206188 := by exact prefixLift 206188
  have htrace : WordTrace (prefixWord ++ tailWord_206188) baseStart_206188 baseEnd_206188 := by
    simpa [prefixWord, tailWord_206188, baseEnd_206188] using wordTrace_append hprefix tailTrace_206188
  have hstable : (prefixWord ++ tailWord_206188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206188).length < 2 ^ (prefixWord ++ tailWord_206188).sum := by decide
  have hdescent : baseEnd_206188 < baseStart_206188 := by decide
  rcases family_descends (prefixWord ++ tailWord_206188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206252 : List Nat := [2, 2, 1, 1, 1, 1, 7, 3, 1, 3]
def baseStart_206252 : Nat := 118140960795 + 206252 * 2 ^ 59
def prefixEnd_206252 : Nat := 4983230072969 + 3 ^ 40 * 206252 * 2
def baseEnd_206252 : Nat := 70604274634154847867647

theorem tailTrace_206252 : CollatzResearch.WordTrace tailWord_206252 prefixEnd_206252 70604274634154847867647 := by
  unfold tailWord_206252
  simp only [CollatzResearch.WordTrace]
  refine ⟨3761314224395851941150505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5015085632527802588200673 3761314224395851941150505)
  ·
    refine ⟨2820985668296888955862879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3761314224395851941150505 2820985668296888955862879)
    ·
      refine ⟨4231478502445333433794319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2820985668296888955862879 4231478502445333433794319)
      ·
        refine ⟨6347217753668000150691479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4231478502445333433794319 6347217753668000150691479)
        ·
          refine ⟨9520826630502000226037219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6347217753668000150691479 9520826630502000226037219)
          ·
            refine ⟨14281239945753000339055829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9520826630502000226037219 14281239945753000339055829)
            ·
              refine ⟨334716561228585945446621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14281239945753000339055829 334716561228585945446621)
              ·
                refine ⟨125518710460719729542483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334716561228585945446621 125518710460719729542483)
                ·
                  refine ⟨188278065691079594313725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125518710460719729542483 188278065691079594313725)
                  ·
                    refine ⟨70604274634154847867647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188278065691079594313725 70604274634154847867647)
                    ·
                      rfl

theorem cell22_206252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_206252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206252 prefixEnd_206252 := by exact prefixLift 206252
  have htrace : WordTrace (prefixWord ++ tailWord_206252) baseStart_206252 baseEnd_206252 := by
    simpa [prefixWord, tailWord_206252, baseEnd_206252] using wordTrace_append hprefix tailTrace_206252
  have hstable : (prefixWord ++ tailWord_206252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206252).length < 2 ^ (prefixWord ++ tailWord_206252).sum := by decide
  have hdescent : baseEnd_206252 < baseStart_206252 := by decide
  rcases family_descends (prefixWord ++ tailWord_206252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206269 : List Nat := [1, 4, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_206269 : Nat := 118140960795 + 206269 * 2 ^ 59
def prefixEnd_206269 : Nat := 4983230072969 + 3 ^ 40 * 206269 * 2
def baseEnd_206269 : Nat := 70610094081572470192595

theorem tailTrace_206269 : CollatzResearch.WordTrace tailWord_206269 prefixEnd_206269 70610094081572470192595 := by
  unfold tailWord_206269
  simp only [CollatzResearch.WordTrace]
  refine ⟨7523248489730115785669861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5015498993153410523779907 7523248489730115785669861)
  ·
    refine ⟨1410609091824396709813099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7523248489730115785669861 1410609091824396709813099)
    ·
      refine ⟨2115913637736595064719649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410609091824396709813099 2115913637736595064719649)
      ·
        refine ⟨1586935228302446298539737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2115913637736595064719649 1586935228302446298539737)
        ·
          refine ⟨1190201421226834723904803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1586935228302446298539737 1190201421226834723904803)
          ·
            refine ⟨1785302131840252085857205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190201421226834723904803 1785302131840252085857205)
            ·
              refine ⟨167372074860023633049113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1785302131840252085857205 167372074860023633049113)
              ·
                refine ⟨125529056145017724786835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167372074860023633049113 125529056145017724786835)
                ·
                  refine ⟨188293584217526587180253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125529056145017724786835 188293584217526587180253)
                  ·
                    refine ⟨70610094081572470192595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188293584217526587180253 70610094081572470192595)
                    ·
                      rfl

theorem cell22_206269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_206269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206269 prefixEnd_206269 := by exact prefixLift 206269
  have htrace : WordTrace (prefixWord ++ tailWord_206269) baseStart_206269 baseEnd_206269 := by
    simpa [prefixWord, tailWord_206269, baseEnd_206269] using wordTrace_append hprefix tailTrace_206269
  have hstable : (prefixWord ++ tailWord_206269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206269).length < 2 ^ (prefixWord ++ tailWord_206269).sum := by decide
  have hdescent : baseEnd_206269 < baseStart_206269 := by decide
  rcases family_descends (prefixWord ++ tailWord_206269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206282 : List Nat := [3, 1, 2, 1, 2, 5, 2, 1, 5]
def baseStart_206282 : Nat := 118140960795 + 206282 * 2 ^ 59
def prefixEnd_206282 : Nat := 4983230072969 + 3 ^ 40 * 206282 * 2
def baseEnd_206282 : Nat := 23538181415748256539185

theorem tailTrace_206282 : CollatzResearch.WordTrace tailWord_206282 prefixEnd_206282 23538181415748256539185 := by
  unfold tailWord_206282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1880930659670754751473275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5015815092455346003928733 1880930659670754751473275)
  ·
    refine ⟨2821395989506132127209913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1880930659670754751473275 2821395989506132127209913)
    ·
      refine ⟨2116046992129599095407435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2821395989506132127209913 2116046992129599095407435)
      ·
        refine ⟨3174070488194398643111153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116046992129599095407435 3174070488194398643111153)
        ·
          refine ⟨2380552866145798982333365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3174070488194398643111153 2380552866145798982333365)
          ·
            refine ⟨223176831201168654593753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2380552866145798982333365 223176831201168654593753)
            ·
              refine ⟨167382623400876490945315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223176831201168654593753 167382623400876490945315)
              ·
                refine ⟨251073935101314736417973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167382623400876490945315 251073935101314736417973)
                ·
                  refine ⟨23538181415748256539185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 251073935101314736417973 23538181415748256539185)
                  ·
                    rfl

theorem cell22_206282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_206282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206282 prefixEnd_206282 := by exact prefixLift 206282
  have htrace : WordTrace (prefixWord ++ tailWord_206282) baseStart_206282 baseEnd_206282 := by
    simpa [prefixWord, tailWord_206282, baseEnd_206282] using wordTrace_append hprefix tailTrace_206282
  have hstable : (prefixWord ++ tailWord_206282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206282).length < 2 ^ (prefixWord ++ tailWord_206282).sum := by decide
  have hdescent : baseEnd_206282 < baseStart_206282 := by decide
  rcases family_descends (prefixWord ++ tailWord_206282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206293 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 8]
def baseStart_206293 : Nat := 118140960795 + 206293 * 2 ^ 59
def prefixEnd_206293 : Nat := 4983230072969 + 3 ^ 40 * 206293 * 2
def baseEnd_206293 : Nat := 23539436590681469197507

theorem tailTrace_206293 : CollatzResearch.WordTrace tailWord_206293 prefixEnd_206293 23539436590681469197507 := by
  unfold tailWord_206293
  simp only [CollatzResearch.WordTrace]
  refine ⟨7524123841643167884543533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5016082561095445256362355 7524123841643167884543533)
  ·
    refine ⟨2821546440616187956703825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7524123841643167884543533 2821546440616187956703825)
    ·
      refine ⟨2116159830462140967527869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2821546440616187956703825 2116159830462140967527869)
      ·
        refine ⟨793559936423302862822951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2116159830462140967527869 793559936423302862822951)
        ·
          refine ⟨1190339904634954294234427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793559936423302862822951 1190339904634954294234427)
          ·
            refine ⟨1785509856952431441351641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190339904634954294234427 1785509856952431441351641)
            ·
              refine ⟨1339132392714323581013731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785509856952431441351641 1339132392714323581013731)
              ·
                refine ⟨2008698589071485371520597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339132392714323581013731 2008698589071485371520597)
                ·
                  refine ⟨23539436590681469197507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2008698589071485371520597 23539436590681469197507)
                  ·
                    rfl

theorem cell22_206293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_206293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206293 prefixEnd_206293 := by exact prefixLift 206293
  have htrace : WordTrace (prefixWord ++ tailWord_206293) baseStart_206293 baseEnd_206293 := by
    simpa [prefixWord, tailWord_206293, baseEnd_206293] using wordTrace_append hprefix tailTrace_206293
  have hstable : (prefixWord ++ tailWord_206293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206293).length < 2 ^ (prefixWord ++ tailWord_206293).sum := by decide
  have hdescent : baseEnd_206293 < baseStart_206293 := by decide
  rcases family_descends (prefixWord ++ tailWord_206293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206312 : List Nat := [2, 1, 4, 1, 1, 2, 5, 1, 1, 4]
def baseStart_206312 : Nat := 118140960795 + 206312 * 2 ^ 59
def prefixEnd_206312 : Nat := 4983230072969 + 3 ^ 40 * 206312 * 2
def baseEnd_206312 : Nat := 70624813860334691367463

theorem tailTrace_206312 : CollatzResearch.WordTrace tailWord_206312 prefixEnd_206312 70624813860334691367463 := by
  unfold tailWord_206312
  simp only [CollatzResearch.WordTrace]
  refine ⟨3762408414287167064742595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5016544552382889419656793 3762408414287167064742595)
  ·
    refine ⟨5643612621430750597113893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3762408414287167064742595 5643612621430750597113893)
    ·
      refine ⟨1058177366518265736958855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5643612621430750597113893 1058177366518265736958855)
      ·
        refine ⟨1587266049777398605438283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058177366518265736958855 1587266049777398605438283)
        ·
          refine ⟨2380899074666097908157425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587266049777398605438283 2380899074666097908157425)
          ·
            refine ⟨1785674305999573431118069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2380899074666097908157425 1785674305999573431118069)
            ·
              refine ⟨167406966187460009167319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1785674305999573431118069 167406966187460009167319)
              ·
                refine ⟨251110449281190013750979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167406966187460009167319 251110449281190013750979)
                ·
                  refine ⟨376665673921785020626469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251110449281190013750979 376665673921785020626469)
                  ·
                    refine ⟨70624813860334691367463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 376665673921785020626469 70624813860334691367463)
                    ·
                      rfl

theorem cell22_206312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_206312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206312 prefixEnd_206312 := by exact prefixLift 206312
  have htrace : WordTrace (prefixWord ++ tailWord_206312) baseStart_206312 baseEnd_206312 := by
    simpa [prefixWord, tailWord_206312, baseEnd_206312] using wordTrace_append hprefix tailTrace_206312
  have hstable : (prefixWord ++ tailWord_206312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206312).length < 2 ^ (prefixWord ++ tailWord_206312).sum := by decide
  have hdescent : baseEnd_206312 < baseStart_206312 := by decide
  rcases family_descends (prefixWord ++ tailWord_206312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206323 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 4, 4]
def baseStart_206323 : Nat := 118140960795 + 206323 * 2 ^ 59
def prefixEnd_206323 : Nat := 4983230072969 + 3 ^ 40 * 206323 * 2
def baseEnd_206323 : Nat := 70628579385134329342429

theorem tailTrace_206323 : CollatzResearch.WordTrace tailWord_206323 prefixEnd_206323 70628579385134329342429 := by
  unfold tailWord_206323
  simp only [CollatzResearch.WordTrace]
  refine ⟨7525218031534483008135623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5016812021022988672090415 7525218031534483008135623)
  ·
    refine ⟨11287827047301724512203435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7525218031534483008135623 11287827047301724512203435)
    ·
      refine ⟨16931740570952586768305153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11287827047301724512203435 16931740570952586768305153)
      ·
        refine ⟨12698805428214440076228865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16931740570952586768305153 12698805428214440076228865)
        ·
          refine ⟨9524104071160830057171649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12698805428214440076228865 9524104071160830057171649)
          ·
            refine ⟨7143078053370622542878737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9524104071160830057171649 7143078053370622542878737)
            ·
              refine ⟨5357308540027966907159053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7143078053370622542878737 5357308540027966907159053)
              ·
                refine ⟨2008990702510487590184645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5357308540027966907159053 2008990702510487590184645)
                ·
                  refine ⟨376685756720716423159621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008990702510487590184645 376685756720716423159621)
                  ·
                    refine ⟨70628579385134329342429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 376685756720716423159621 70628579385134329342429)
                    ·
                      rfl

theorem cell22_206323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 4].length) (baseStart_206323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206323 prefixEnd_206323 := by exact prefixLift 206323
  have htrace : WordTrace (prefixWord ++ tailWord_206323) baseStart_206323 baseEnd_206323 := by
    simpa [prefixWord, tailWord_206323, baseEnd_206323] using wordTrace_append hprefix tailTrace_206323
  have hstable : (prefixWord ++ tailWord_206323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206323).length < 2 ^ (prefixWord ++ tailWord_206323).sum := by decide
  have hdescent : baseEnd_206323 < baseStart_206323 := by decide
  rcases family_descends (prefixWord ++ tailWord_206323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206355 : List Nat := [1, 1, 1, 2, 1, 7, 3, 6]
def baseStart_206355 : Nat := 118140960795 + 206355 * 2 ^ 59
def prefixEnd_206355 : Nat := 4983230072969 + 3 ^ 40 * 206355 * 2
def baseEnd_206355 : Nat := 7848837071010768060259

theorem tailTrace_206355 : CollatzResearch.WordTrace tailWord_206355 prefixEnd_206355 7848837071010768060259 := by
  unfold tailWord_206355
  simp only [CollatzResearch.WordTrace]
  refine ⟨7526385167418552473300519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5017590111612368315533679 7526385167418552473300519)
  ·
    refine ⟨11289577751127828709950779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7526385167418552473300519 11289577751127828709950779)
    ·
      refine ⟨16934366626691743064926169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11289577751127828709950779 16934366626691743064926169)
      ·
        refine ⟨12700774970018807298694627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16934366626691743064926169 12700774970018807298694627)
        ·
          refine ⟨19051162455028210948041941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12700774970018807298694627 19051162455028210948041941)
          ·
            refine ⟨446511620039723694094733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 19051162455028210948041941 446511620039723694094733)
            ·
              refine ⟨167441857514896385285525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 446511620039723694094733 167441857514896385285525)
              ·
                refine ⟨7848837071010768060259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167441857514896385285525 7848837071010768060259)
                ·
                  rfl

theorem cell22_206355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 6].length) (baseStart_206355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206355 prefixEnd_206355 := by exact prefixLift 206355
  have htrace : WordTrace (prefixWord ++ tailWord_206355) baseStart_206355 baseEnd_206355 := by
    simpa [prefixWord, tailWord_206355, baseEnd_206355] using wordTrace_append hprefix tailTrace_206355
  have hstable : (prefixWord ++ tailWord_206355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206355).length < 2 ^ (prefixWord ++ tailWord_206355).sum := by decide
  have hdescent : baseEnd_206355 < baseStart_206355 := by decide
  rcases family_descends (prefixWord ++ tailWord_206355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206357 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 2, 4]
def baseStart_206357 : Nat := 118140960795 + 206357 * 2 ^ 59
def prefixEnd_206357 : Nat := 4983230072969 + 3 ^ 40 * 206357 * 2
def baseEnd_206357 : Nat := 70640218279969573992325

theorem tailTrace_206357 : CollatzResearch.WordTrace tailWord_206357 prefixEnd_206357 70640218279969573992325 := by
  unfold tailWord_206357
  simp only [CollatzResearch.WordTrace]
  refine ⟨7526458113411306814873325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5017638742274204543248883 7526458113411306814873325)
  ·
    refine ⟨2822421792529240055577497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7526458113411306814873325 2822421792529240055577497)
    ·
      refine ⟨2116816344396930041683123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2822421792529240055577497 2116816344396930041683123)
      ·
        refine ⟨3175224516595395062524685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116816344396930041683123 3175224516595395062524685)
        ·
          refine ⟨1190709193723273148446757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3175224516595395062524685 1190709193723273148446757)
          ·
            refine ⟨223257973823113715333767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1190709193723273148446757 223257973823113715333767)
            ·
              refine ⟨334886960734670573000651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223257973823113715333767 334886960734670573000651)
              ·
                refine ⟨502330441102005859500977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334886960734670573000651 502330441102005859500977)
                ·
                  refine ⟨376747830826504394625733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502330441102005859500977 376747830826504394625733)
                  ·
                    refine ⟨70640218279969573992325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 376747830826504394625733 70640218279969573992325)
                    ·
                      rfl

theorem cell22_206357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_206357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206357 prefixEnd_206357 := by exact prefixLift 206357
  have htrace : WordTrace (prefixWord ++ tailWord_206357) baseStart_206357 baseEnd_206357 := by
    simpa [prefixWord, tailWord_206357, baseEnd_206357] using wordTrace_append hprefix tailTrace_206357
  have hstable : (prefixWord ++ tailWord_206357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206357).length < 2 ^ (prefixWord ++ tailWord_206357).sum := by decide
  have hdescent : baseEnd_206357 < baseStart_206357 := by decide
  rcases family_descends (prefixWord ++ tailWord_206357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206376 : List Nat := [2, 1, 5, 2, 2, 2, 1, 2, 2, 3]
def baseStart_206376 : Nat := 118140960795 + 206376 * 2 ^ 59
def prefixEnd_206376 : Nat := 4983230072969 + 3 ^ 40 * 206376 * 2
def baseEnd_206376 : Nat := 70646722368259857767267

theorem tailTrace_206376 : CollatzResearch.WordTrace tailWord_206376 prefixEnd_206376 70646722368259857767267 := by
  unfold tailWord_206376
  simp only [CollatzResearch.WordTrace]
  refine ⟨3763575550171236529907491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5018100733561648706543321 3763575550171236529907491)
  ·
    refine ⟨5645363325256854794861237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3763575550171236529907491 5645363325256854794861237)
    ·
      refine ⟨529252811742830137018241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5645363325256854794861237 529252811742830137018241)
      ·
        refine ⟨396939608807122602763681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529252811742830137018241 396939608807122602763681)
        ·
          refine ⟨297704706605341952072761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396939608807122602763681 297704706605341952072761)
          ·
            refine ⟨223278529954006464054571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297704706605341952072761 223278529954006464054571)
            ·
              refine ⟨334917794931009696081857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223278529954006464054571 334917794931009696081857)
              ·
                refine ⟨251188346198257272061393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334917794931009696081857 251188346198257272061393)
                ·
                  refine ⟨188391259648692954046045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251188346198257272061393 188391259648692954046045)
                  ·
                    refine ⟨70646722368259857767267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188391259648692954046045 70646722368259857767267)
                    ·
                      rfl

theorem cell22_206376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_206376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206376 prefixEnd_206376 := by exact prefixLift 206376
  have htrace : WordTrace (prefixWord ++ tailWord_206376) baseStart_206376 baseEnd_206376 := by
    simpa [prefixWord, tailWord_206376, baseEnd_206376] using wordTrace_append hprefix tailTrace_206376
  have hstable : (prefixWord ++ tailWord_206376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206376).length < 2 ^ (prefixWord ++ tailWord_206376).sum := by decide
  have hdescent : baseEnd_206376 < baseStart_206376 := by decide
  rcases family_descends (prefixWord ++ tailWord_206376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206387 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 3, 3]
def baseStart_206387 : Nat := 118140960795 + 206387 * 2 ^ 59
def prefixEnd_206387 : Nat := 4983230072969 + 3 ^ 40 * 206387 * 2
def baseEnd_206387 : Nat := 70650487893059495742233

theorem tailTrace_206387 : CollatzResearch.WordTrace tailWord_206387 prefixEnd_206387 70650487893059495742233 := by
  unfold tailWord_206387
  simp only [CollatzResearch.WordTrace]
  refine ⟨7527552303302621938465415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5018368202201747958976943 7527552303302621938465415)
  ·
    refine ⟨11291328454953932907698123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7527552303302621938465415 11291328454953932907698123)
    ·
      refine ⟨16936992682430899361547185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11291328454953932907698123 16936992682430899361547185)
      ·
        refine ⟨12702744511823174521160389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16936992682430899361547185 12702744511823174521160389)
        ·
          refine ⟨2381764595966845222717573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12702744511823174521160389 2381764595966845222717573)
          ·
            refine ⟨446580861743783479259545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2381764595966845222717573 446580861743783479259545)
            ·
              refine ⟨334935646307837609444659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446580861743783479259545 334935646307837609444659)
              ·
                refine ⟨502403469461756414166989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334935646307837609444659 502403469461756414166989)
                ·
                  refine ⟨188401301048158655312621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502403469461756414166989 188401301048158655312621)
                  ·
                    refine ⟨70650487893059495742233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188401301048158655312621 70650487893059495742233)
                    ·
                      rfl

theorem cell22_206387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 3].length) (baseStart_206387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206387 prefixEnd_206387 := by exact prefixLift 206387
  have htrace : WordTrace (prefixWord ++ tailWord_206387) baseStart_206387 baseEnd_206387 := by
    simpa [prefixWord, tailWord_206387, baseEnd_206387] using wordTrace_append hprefix tailTrace_206387
  have hstable : (prefixWord ++ tailWord_206387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206387).length < 2 ^ (prefixWord ++ tailWord_206387).sum := by decide
  have hdescent : baseEnd_206387 < baseStart_206387 := by decide
  rcases family_descends (prefixWord ++ tailWord_206387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206406 : List Nat := [6, 1, 1, 1, 3, 2, 2, 6]
def baseStart_206406 : Nat := 118140960795 + 206406 * 2 ^ 59
def prefixEnd_206406 : Nat := 4983230072969 + 3 ^ 40 * 206406 * 2
def baseEnd_206406 : Nat := 7850776886816642168575

theorem tailTrace_206406 : CollatzResearch.WordTrace tailWord_206406 prefixEnd_206406 7850776886816642168575 := by
  unfold tailWord_206406
  simp only [CollatzResearch.WordTrace]
  refine ⟨235257665319805880731471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5018830193489192122271381 235257665319805880731471)
  ·
    refine ⟨352886497979708821097207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235257665319805880731471 352886497979708821097207)
    ·
      refine ⟨529329746969563231645811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352886497979708821097207 529329746969563231645811)
      ·
        refine ⟨793994620454344847468717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529329746969563231645811 793994620454344847468717)
        ·
          refine ⟨297747982670379317800769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 793994620454344847468717 297747982670379317800769)
          ·
            refine ⟨223310987002784488350577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297747982670379317800769 223310987002784488350577)
            ·
              refine ⟨167483240252088366262933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223310987002784488350577 167483240252088366262933)
              ·
                refine ⟨7850776886816642168575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167483240252088366262933 7850776886816642168575)
                ·
                  rfl

theorem cell22_206406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_206406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206406 prefixEnd_206406 := by exact prefixLift 206406
  have htrace : WordTrace (prefixWord ++ tailWord_206406) baseStart_206406 baseEnd_206406 := by
    simpa [prefixWord, tailWord_206406, baseEnd_206406] using wordTrace_append hprefix tailTrace_206406
  have hstable : (prefixWord ++ tailWord_206406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206406).length < 2 ^ (prefixWord ++ tailWord_206406).sum := by decide
  have hdescent : baseEnd_206406 < baseStart_206406 := by decide
  rcases family_descends (prefixWord ++ tailWord_206406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206460 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_206460 : Nat := 118140960795 + 206460 * 2 ^ 59
def prefixEnd_206460 : Nat := 4983230072969 + 3 ^ 40 * 206460 * 2
def baseEnd_206460 : Nat := 70675477284911638667009

theorem tailTrace_206460 : CollatzResearch.WordTrace tailWord_206460 prefixEnd_206460 70675477284911638667009 := by
  unfold tailWord_206460
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765107416019077702936417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5020143221358770270581889 3765107416019077702936417)
  ·
    refine ⟨2823830562014308277202313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3765107416019077702936417 2823830562014308277202313)
    ·
      refine ⟨2117872921510731207901735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2823830562014308277202313 2117872921510731207901735)
      ·
        refine ⟨3176809382266096811852603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2117872921510731207901735 3176809382266096811852603)
        ·
          refine ⟨4765214073399145217778905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3176809382266096811852603 4765214073399145217778905)
          ·
            refine ⟨3573910555049358913334179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4765214073399145217778905 3573910555049358913334179)
            ·
              refine ⟨5360865832574038370001269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573910555049358913334179 5360865832574038370001269)
              ·
                refine ⟨502581171803816097187619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5360865832574038370001269 502581171803816097187619)
                ·
                  refine ⟨753871757705724145781429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502581171803816097187619 753871757705724145781429)
                  ·
                    refine ⟨70675477284911638667009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 753871757705724145781429 70675477284911638667009)
                    ·
                      rfl

theorem cell22_206460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_206460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206460 prefixEnd_206460 := by exact prefixLift 206460
  have htrace : WordTrace (prefixWord ++ tailWord_206460) baseStart_206460 baseEnd_206460 := by
    simpa [prefixWord, tailWord_206460, baseEnd_206460] using wordTrace_append hprefix tailTrace_206460
  have hstable : (prefixWord ++ tailWord_206460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206460).length < 2 ^ (prefixWord ++ tailWord_206460).sum := by decide
  have hdescent : baseEnd_206460 < baseStart_206460 := by decide
  rcases family_descends (prefixWord ++ tailWord_206460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206496 : List Nat := [2, 1, 1, 4, 3, 3, 2, 2, 4]
def baseStart_206496 : Nat := 118140960795 + 206496 * 2 ^ 59
def prefixEnd_206496 : Nat := 4983230072969 + 3 ^ 40 * 206496 * 2
def baseEnd_206496 : Nat := 23562600273539848255633

theorem tailTrace_206496 : CollatzResearch.WordTrace tailWord_206496 prefixEnd_206496 23562600273539848255633 := by
  unfold tailWord_206496
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765763929953866777091671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5021018573271822369455561 3765763929953866777091671)
  ·
    refine ⟨5648645894930800165637507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3765763929953866777091671 5648645894930800165637507)
    ·
      refine ⟨8472968842396200248456261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5648645894930800165637507 8472968842396200248456261)
      ·
        refine ⟨1588681657949287546585549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8472968842396200248456261 1588681657949287546585549)
        ·
          refine ⟨595755621730982829969581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1588681657949287546585549 595755621730982829969581)
          ·
            refine ⟨223408358149118561238593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 595755621730982829969581 223408358149118561238593)
            ·
              refine ⟨167556268611838920928945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223408358149118561238593 167556268611838920928945)
              ·
                refine ⟨125667201458879190696709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167556268611838920928945 125667201458879190696709)
                ·
                  refine ⟨23562600273539848255633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125667201458879190696709 23562600273539848255633)
                  ·
                    rfl

theorem cell22_206496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 4].length) (baseStart_206496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206496 prefixEnd_206496 := by exact prefixLift 206496
  have htrace : WordTrace (prefixWord ++ tailWord_206496) baseStart_206496 baseEnd_206496 := by
    simpa [prefixWord, tailWord_206496, baseEnd_206496] using wordTrace_append hprefix tailTrace_206496
  have hstable : (prefixWord ++ tailWord_206496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206496).length < 2 ^ (prefixWord ++ tailWord_206496).sum := by decide
  have hdescent : baseEnd_206496 < baseStart_206496 := by decide
  rcases family_descends (prefixWord ++ tailWord_206496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206522 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 5, 3]
def baseStart_206522 : Nat := 118140960795 + 206522 * 2 ^ 59
def prefixEnd_206522 : Nat := 4983230072969 + 3 ^ 40 * 206522 * 2
def baseEnd_206522 : Nat := 70696701151964143616819

theorem tailTrace_206522 : CollatzResearch.WordTrace tailWord_206522 prefixEnd_206522 70696701151964143616819 := by
  unfold tailWord_206522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1883119039453384998657455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5021650771875693329753213 1883119039453384998657455)
  ·
    refine ⟨2824678559180077497986183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1883119039453384998657455 2824678559180077497986183)
    ·
      refine ⟨4237017838770116246979275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2824678559180077497986183 4237017838770116246979275)
      ·
        refine ⟨6355526758155174370468913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4237017838770116246979275 6355526758155174370468913)
        ·
          refine ⟨4766645068616380777851685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6355526758155174370468913 4766645068616380777851685)
          ·
            refine ⟨893745950365571395847191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4766645068616380777851685 893745950365571395847191)
            ·
              refine ⟨1340618925548357093770787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893745950365571395847191 1340618925548357093770787)
              ·
                refine ⟨2010928388322535640656181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340618925548357093770787 2010928388322535640656181)
                ·
                  refine ⟨188524536405237716311517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2010928388322535640656181 188524536405237716311517)
                  ·
                    refine ⟨70696701151964143616819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188524536405237716311517 70696701151964143616819)
                    ·
                      rfl

theorem cell22_206522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_206522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206522 prefixEnd_206522 := by exact prefixLift 206522
  have htrace : WordTrace (prefixWord ++ tailWord_206522) baseStart_206522 baseEnd_206522 := by
    simpa [prefixWord, tailWord_206522, baseEnd_206522] using wordTrace_append hprefix tailTrace_206522
  have hstable : (prefixWord ++ tailWord_206522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206522).length < 2 ^ (prefixWord ++ tailWord_206522).sum := by decide
  have hdescent : baseEnd_206522 < baseStart_206522 := by decide
  rcases family_descends (prefixWord ++ tailWord_206522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206530 : List Nat := [3, 5, 1, 2, 1, 1, 2, 3, 4]
def baseStart_206530 : Nat := 118140960795 + 206530 * 2 ^ 59
def prefixEnd_206530 : Nat := 4983230072969 + 3 ^ 40 * 206530 * 2
def baseEnd_206530 : Nat := 23566479905151596472265

theorem tailTrace_206530 : CollatzResearch.WordTrace tailWord_206530 prefixEnd_206530 23566479905151596472265 := by
  unfold tailWord_206530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1883191985446139340230261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5021845294523038240614029 1883191985446139340230261)
  ·
    refine ⟨176549248635575563146587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1883191985446139340230261 176549248635575563146587)
    ·
      refine ⟨264823872953363344719881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176549248635575563146587 264823872953363344719881)
      ·
        refine ⟨198617904715022508539911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264823872953363344719881 198617904715022508539911)
        ·
          refine ⟨297926857072533762809867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198617904715022508539911 297926857072533762809867)
          ·
            refine ⟨446890285608800644214801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297926857072533762809867 446890285608800644214801)
            ·
              refine ⟨335167714206600483161101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446890285608800644214801 335167714206600483161101)
              ·
                refine ⟨125687892827475181185413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335167714206600483161101 125687892827475181185413)
                ·
                  refine ⟨23566479905151596472265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125687892827475181185413 23566479905151596472265)
                  ·
                    rfl

theorem cell22_206530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_206530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206530 prefixEnd_206530 := by exact prefixLift 206530
  have htrace : WordTrace (prefixWord ++ tailWord_206530) baseStart_206530 baseEnd_206530 := by
    simpa [prefixWord, tailWord_206530, baseEnd_206530] using wordTrace_append hprefix tailTrace_206530
  have hstable : (prefixWord ++ tailWord_206530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206530).length < 2 ^ (prefixWord ++ tailWord_206530).sum := by decide
  have hdescent : baseEnd_206530 < baseStart_206530 := by decide
  rcases family_descends (prefixWord ++ tailWord_206530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206535 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 7]
def baseStart_206535 : Nat := 118140960795 + 206535 * 2 ^ 59
def prefixEnd_206535 : Nat := 4983230072969 + 3 ^ 40 * 206535 * 2
def baseEnd_206535 : Nat := 23567050439212147680593

theorem tailTrace_206535 : CollatzResearch.WordTrace tailWord_206535 prefixEnd_206535 23567050439212147680593 := by
  unfold tailWord_206535
  simp only [CollatzResearch.WordTrace]
  refine ⟨7532950306766443214853059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5021966871177628809902039 7532950306766443214853059)
  ·
    refine ⟨11299425460149664822279589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7532950306766443214853059 11299425460149664822279589)
    ·
      refine ⟨2118642273778062154177423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11299425460149664822279589 2118642273778062154177423)
      ·
        refine ⟨3177963410667093231266135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2118642273778062154177423 3177963410667093231266135)
        ·
          refine ⟨4766945116000639846899203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177963410667093231266135 4766945116000639846899203)
          ·
            refine ⟨7150417674000959770348805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4766945116000639846899203 7150417674000959770348805)
            ·
              refine ⟨1340703313875179956940401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7150417674000959770348805 1340703313875179956940401)
              ·
                refine ⟨1005527485406384967705301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1340703313875179956940401 1005527485406384967705301)
                ·
                  refine ⟨23567050439212147680593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1005527485406384967705301 23567050439212147680593)
                  ·
                    rfl

theorem cell22_206535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 7].length) (baseStart_206535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206535 prefixEnd_206535 := by exact prefixLift 206535
  have htrace : WordTrace (prefixWord ++ tailWord_206535) baseStart_206535 baseEnd_206535 := by
    simpa [prefixWord, tailWord_206535, baseEnd_206535] using wordTrace_append hprefix tailTrace_206535
  have hstable : (prefixWord ++ tailWord_206535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206535).length < 2 ^ (prefixWord ++ tailWord_206535).sum := by decide
  have hdescent : baseEnd_206535 < baseStart_206535 := by decide
  rcases family_descends (prefixWord ++ tailWord_206535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206590 : List Nat := [4, 2, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_206590 : Nat := 118140960795 + 206590 * 2 ^ 59
def prefixEnd_206590 : Nat := 4983230072969 + 3 ^ 40 * 206590 * 2
def baseEnd_206590 : Nat := 70719978941634632916611

theorem tailTrace_206590 : CollatzResearch.WordTrace tailWord_206590 prefixEnd_206590 70719978941634632916611 := by
  unfold tailWord_206590
  simp only [CollatzResearch.WordTrace]
  refine ⟨941869540195898451013153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5023304214378125072070149 941869540195898451013153)
  ·
    refine ⟨706402155146923838259865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 941869540195898451013153 706402155146923838259865)
    ·
      refine ⟨529801616360192878694899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 706402155146923838259865 529801616360192878694899)
      ·
        refine ⟨794702424540289318042349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529801616360192878694899 794702424540289318042349)
        ·
          refine ⟨298013409202608494265881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 794702424540289318042349 298013409202608494265881)
          ·
            refine ⟨223510056901956370699411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298013409202608494265881 223510056901956370699411)
            ·
              refine ⟨335265085352934556049117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223510056901956370699411 335265085352934556049117)
              ·
                refine ⟨125724407007350458518419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335265085352934556049117 125724407007350458518419)
                ·
                  refine ⟨188586610511025687777629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125724407007350458518419 188586610511025687777629)
                  ·
                    refine ⟨70719978941634632916611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188586610511025687777629 70719978941634632916611)
                    ·
                      rfl

theorem cell22_206590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_206590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206590 prefixEnd_206590 := by exact prefixLift 206590
  have htrace : WordTrace (prefixWord ++ tailWord_206590) baseStart_206590 baseEnd_206590 := by
    simpa [prefixWord, tailWord_206590, baseEnd_206590] using wordTrace_append hprefix tailTrace_206590
  have hstable : (prefixWord ++ tailWord_206590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206590).length < 2 ^ (prefixWord ++ tailWord_206590).sum := by decide
  have hdescent : baseEnd_206590 < baseStart_206590 := by decide
  rcases family_descends (prefixWord ++ tailWord_206590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206642 : List Nat := [3, 2, 1, 1, 3, 2, 2, 8]
def baseStart_206642 : Nat := 118140960795 + 206642 * 2 ^ 59
def prefixEnd_206642 : Nat := 4983230072969 + 3 ^ 40 * 206642 * 2
def baseEnd_206642 : Nat := 7859753289369314512939

theorem tailTrace_206642 : CollatzResearch.WordTrace tailWord_206642 prefixEnd_206642 7859753289369314512939 := by
  unfold tailWord_206642
  simp only [CollatzResearch.WordTrace]
  refine ⟨1884213229344700122249545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5024568611585866992665453 1884213229344700122249545)
  ·
    refine ⟨1413159922008525091687159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1884213229344700122249545 1413159922008525091687159)
    ·
      refine ⟨2119739883012787637530739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1413159922008525091687159 2119739883012787637530739)
      ·
        refine ⟨3179609824519181456296109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2119739883012787637530739 3179609824519181456296109)
        ·
          refine ⟨1192353684194693046111041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3179609824519181456296109 1192353684194693046111041)
          ·
            refine ⟨894265263146019784583281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1192353684194693046111041 894265263146019784583281)
            ·
              refine ⟨670698947359514838437461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894265263146019784583281 670698947359514838437461)
              ·
                refine ⟨7859753289369314512939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 670698947359514838437461 7859753289369314512939)
                ·
                  rfl

theorem cell22_206642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_206642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206642 prefixEnd_206642 := by exact prefixLift 206642
  have htrace : WordTrace (prefixWord ++ tailWord_206642) baseStart_206642 baseEnd_206642 := by
    simpa [prefixWord, tailWord_206642, baseEnd_206642] using wordTrace_append hprefix tailTrace_206642
  have hstable : (prefixWord ++ tailWord_206642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206642).length < 2 ^ (prefixWord ++ tailWord_206642).sum := by decide
  have hdescent : baseEnd_206642 < baseStart_206642 := by decide
  rcases family_descends (prefixWord ++ tailWord_206642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206646 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_206646 : Nat := 118140960795 + 206646 * 2 ^ 59
def prefixEnd_206646 : Nat := 4983230072969 + 3 ^ 40 * 206646 * 2
def baseEnd_206646 : Nat := 70739148886069153516439

theorem tailTrace_206646 : CollatzResearch.WordTrace tailWord_206646 prefixEnd_206646 70739148886069153516439 := by
  unfold tailWord_206646
  simp only [CollatzResearch.WordTrace]
  refine ⟨471062425585269323258987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5024665872909539448095861 471062425585269323258987)
  ·
    refine ⟨706593638377903984888481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 471062425585269323258987 706593638377903984888481)
    ·
      refine ⟨529945228783427988666361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 706593638377903984888481 529945228783427988666361)
      ·
        refine ⟨397458921587570991499771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529945228783427988666361 397458921587570991499771)
        ·
          refine ⟨596188382381356487249657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397458921587570991499771 596188382381356487249657)
          ·
            refine ⟨447141286786017365437243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 596188382381356487249657 447141286786017365437243)
            ·
              refine ⟨670711930179026048155865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447141286786017365437243 670711930179026048155865)
              ·
                refine ⟨503033947634269536116899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670711930179026048155865 503033947634269536116899)
                ·
                  refine ⟨754550921451404304175349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503033947634269536116899 754550921451404304175349)
                  ·
                    refine ⟨70739148886069153516439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 754550921451404304175349 70739148886069153516439)
                    ·
                      rfl

theorem cell22_206646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_206646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206646 prefixEnd_206646 := by exact prefixLift 206646
  have htrace : WordTrace (prefixWord ++ tailWord_206646) baseStart_206646 baseEnd_206646 := by
    simpa [prefixWord, tailWord_206646, baseEnd_206646] using wordTrace_append hprefix tailTrace_206646
  have hstable : (prefixWord ++ tailWord_206646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206646).length < 2 ^ (prefixWord ++ tailWord_206646).sum := by decide
  have hdescent : baseEnd_206646 < baseStart_206646 := by decide
  rcases family_descends (prefixWord ++ tailWord_206646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206691 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 3, 3]
def baseStart_206691 : Nat := 118140960795 + 206691 * 2 ^ 59
def prefixEnd_206691 : Nat := 4983230072969 + 3 ^ 40 * 206691 * 2
def baseEnd_206691 : Nat := 70754553305704036141301

theorem tailTrace_206691 : CollatzResearch.WordTrace tailWord_206691 prefixEnd_206691 70754553305704036141301 := by
  unfold tailWord_206691
  simp only [CollatzResearch.WordTrace]
  refine ⟨7538640094201281857531927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5025760062800854571687951 7538640094201281857531927)
  ·
    refine ⟨11307960141301922786297891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7538640094201281857531927 11307960141301922786297891)
    ·
      refine ⟨16961940211952884179446837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11307960141301922786297891 16961940211952884179446837)
      ·
        refine ⟨1590181894870582891823141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16961940211952884179446837 1590181894870582891823141)
        ·
          refine ⟨298159105288234292216839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1590181894870582891823141 298159105288234292216839)
          ·
            refine ⟨447238657932351438325259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298159105288234292216839 447238657932351438325259)
            ·
              refine ⟨670857986898527157487889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447238657932351438325259 670857986898527157487889)
              ·
                refine ⟨503143490173895368115917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670857986898527157487889 503143490173895368115917)
                ·
                  refine ⟨188678808815210763043469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503143490173895368115917 188678808815210763043469)
                  ·
                    refine ⟨70754553305704036141301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188678808815210763043469 70754553305704036141301)
                    ·
                      rfl

theorem cell22_206691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 3].length) (baseStart_206691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206691 prefixEnd_206691 := by exact prefixLift 206691
  have htrace : WordTrace (prefixWord ++ tailWord_206691) baseStart_206691 baseEnd_206691 := by
    simpa [prefixWord, tailWord_206691, baseEnd_206691] using wordTrace_append hprefix tailTrace_206691
  have hstable : (prefixWord ++ tailWord_206691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206691).length < 2 ^ (prefixWord ++ tailWord_206691).sum := by decide
  have hdescent : baseEnd_206691 < baseStart_206691 := by decide
  rcases family_descends (prefixWord ++ tailWord_206691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206721 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 7]
def baseStart_206721 : Nat := 118140960795 + 206721 * 2 ^ 59
def prefixEnd_206721 : Nat := 4983230072969 + 3 ^ 40 * 206721 * 2
def baseEnd_206721 : Nat := 23588274306264652630403

theorem tailTrace_206721 : CollatzResearch.WordTrace tailWord_206721 prefixEnd_206721 23588274306264652630403 := by
  unfold tailWord_206721
  simp only [CollatzResearch.WordTrace]
  refine ⟨7539734284092596981124017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5026489522728397987416011 7539734284092596981124017)
  ·
    refine ⟨5654800713069447735843013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7539734284092596981124017 5654800713069447735843013)
    ·
      refine ⟨1060275133700521450470565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5654800713069447735843013 1060275133700521450470565)
      ·
        refine ⟨198801587568847771963231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1060275133700521450470565 198801587568847771963231)
        ·
          refine ⟨298202381353271657944847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198801587568847771963231 298202381353271657944847)
          ·
            refine ⟨447303572029907486917271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298202381353271657944847 447303572029907486917271)
            ·
              refine ⟨670955358044861230375907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447303572029907486917271 670955358044861230375907)
              ·
                refine ⟨1006433037067291845563861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670955358044861230375907 1006433037067291845563861)
                ·
                  refine ⟨23588274306264652630403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1006433037067291845563861 23588274306264652630403)
                  ·
                    rfl

theorem cell22_206721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 7].length) (baseStart_206721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206721 prefixEnd_206721 := by exact prefixLift 206721
  have htrace : WordTrace (prefixWord ++ tailWord_206721) baseStart_206721 baseEnd_206721 := by
    simpa [prefixWord, tailWord_206721, baseEnd_206721] using wordTrace_append hprefix tailTrace_206721
  have hstable : (prefixWord ++ tailWord_206721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206721).length < 2 ^ (prefixWord ++ tailWord_206721).sum := by decide
  have hdescent : baseEnd_206721 < baseStart_206721 := by decide
  rcases family_descends (prefixWord ++ tailWord_206721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206738 : List Nat := [3, 2, 3, 2, 1, 2, 3, 1, 5]
def baseStart_206738 : Nat := 118140960795 + 206738 * 2 ^ 59
def prefixEnd_206738 : Nat := 4983230072969 + 3 ^ 40 * 206738 * 2
def baseEnd_206738 : Nat := 23590214122070526738719

theorem tailTrace_206738 : CollatzResearch.WordTrace tailWord_206738 prefixEnd_206738 23590214122070526738719 := by
  unfold tailWord_206738
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885088581257752221123217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5026902883354005922995245 1885088581257752221123217)
  ·
    refine ⟨1413816435943314165842413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1885088581257752221123217 1413816435943314165842413)
    ·
      refine ⟨530181163478742812190905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1413816435943314165842413 530181163478742812190905)
      ·
        refine ⟨397635872609057109143179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530181163478742812190905 397635872609057109143179)
        ·
          refine ⟨596453808913585663714769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397635872609057109143179 596453808913585663714769)
          ·
            refine ⟨447340356685189247786077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 596453808913585663714769 447340356685189247786077)
            ·
              refine ⟨167752633756945967919779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 447340356685189247786077 167752633756945967919779)
              ·
                refine ⟨251628950635418951879669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167752633756945967919779 251628950635418951879669)
                ·
                  refine ⟨23590214122070526738719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 251628950635418951879669 23590214122070526738719)
                  ·
                    rfl

theorem cell22_206738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_206738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206738 prefixEnd_206738 := by exact prefixLift 206738
  have htrace : WordTrace (prefixWord ++ tailWord_206738) baseStart_206738 baseEnd_206738 := by
    simpa [prefixWord, tailWord_206738, baseEnd_206738] using wordTrace_append hprefix tailTrace_206738
  have hstable : (prefixWord ++ tailWord_206738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206738).length < 2 ^ (prefixWord ++ tailWord_206738).sum := by decide
  have hdescent : baseEnd_206738 < baseStart_206738 := by decide
  rcases family_descends (prefixWord ++ tailWord_206738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206749 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 6]
def baseStart_206749 : Nat := 118140960795 + 206749 * 2 ^ 59
def prefixEnd_206749 : Nat := 4983230072969 + 3 ^ 40 * 206749 * 2
def baseEnd_206749 : Nat := 23591469297003739397041

theorem tailTrace_206749 : CollatzResearch.WordTrace tailWord_206749 prefixEnd_206749 23591469297003739397041 := by
  unfold tailWord_206749
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540755527991157763143301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5027170351994105175428867 7540755527991157763143301)
  ·
    refine ⟨1413891661498342080589369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7540755527991157763143301 1413891661498342080589369)
    ·
      refine ⟨1060418746123756560442027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1413891661498342080589369 1060418746123756560442027)
      ·
        refine ⟨1590628119185634840663041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1060418746123756560442027 1590628119185634840663041)
        ·
          refine ⟨1192971089389226130497281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1590628119185634840663041 1192971089389226130497281)
          ·
            refine ⟨894728317041919597872961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1192971089389226130497281 894728317041919597872961)
            ·
              refine ⟨671046237781439698404721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894728317041919597872961 671046237781439698404721)
              ·
                refine ⟨503284678336079773803541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671046237781439698404721 503284678336079773803541)
                ·
                  refine ⟨23591469297003739397041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 503284678336079773803541 23591469297003739397041)
                  ·
                    rfl

theorem cell22_206749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_206749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206749 prefixEnd_206749 := by exact prefixLift 206749
  have htrace : WordTrace (prefixWord ++ tailWord_206749) baseStart_206749 baseEnd_206749 := by
    simpa [prefixWord, tailWord_206749, baseEnd_206749] using wordTrace_append hprefix tailTrace_206749
  have hstable : (prefixWord ++ tailWord_206749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206749).length < 2 ^ (prefixWord ++ tailWord_206749).sum := by decide
  have hdescent : baseEnd_206749 < baseStart_206749 := by decide
  rcases family_descends (prefixWord ++ tailWord_206749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206781 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_206781 : Nat := 118140960795 + 206781 * 2 ^ 59
def prefixEnd_206781 : Nat := 4983230072969 + 3 ^ 40 * 206781 * 2
def baseEnd_206781 : Nat := 70785362144973801391025

theorem tailTrace_206781 : CollatzResearch.WordTrace tailWord_206781 prefixEnd_206781 70785362144973801391025 := by
  unfold tailWord_206781
  simp only [CollatzResearch.WordTrace]
  refine ⟨7541922663875227228308197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5027948442583484818872131 7541922663875227228308197)
  ·
    refine ⟨1414110499476605105307787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7541922663875227228308197 1414110499476605105307787)
    ·
      refine ⟨2121165749214907657961681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414110499476605105307787 2121165749214907657961681)
      ·
        refine ⟨1590874311911180743471261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2121165749214907657961681 1590874311911180743471261)
        ·
          refine ⟨596577866966692778801723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1590874311911180743471261 596577866966692778801723)
          ·
            refine ⟨894866800450039168202585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596577866966692778801723 894866800450039168202585)
            ·
              refine ⟨671150100337529376151939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894866800450039168202585 671150100337529376151939)
              ·
                refine ⟨1006725150506294064227909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671150100337529376151939 1006725150506294064227909)
                ·
                  refine ⟨188760965719930137042733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1006725150506294064227909 188760965719930137042733)
                  ·
                    refine ⟨70785362144973801391025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188760965719930137042733 70785362144973801391025)
                    ·
                      rfl

theorem cell22_206781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_206781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206781 prefixEnd_206781 := by exact prefixLift 206781
  have htrace : WordTrace (prefixWord ++ tailWord_206781) baseStart_206781 baseEnd_206781 := by
    simpa [prefixWord, tailWord_206781, baseEnd_206781] using wordTrace_append hprefix tailTrace_206781
  have hstable : (prefixWord ++ tailWord_206781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206781).length < 2 ^ (prefixWord ++ tailWord_206781).sum := by decide
  have hdescent : baseEnd_206781 < baseStart_206781 := by decide
  rcases family_descends (prefixWord ++ tailWord_206781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206813 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_206813 : Nat := 118140960795 + 206813 * 2 ^ 59
def prefixEnd_206813 : Nat := 4983230072969 + 3 ^ 40 * 206813 * 2
def baseEnd_206813 : Nat := 70796316398936384590927

theorem tailTrace_206813 : CollatzResearch.WordTrace tailWord_206813 prefixEnd_206813 70796316398936384590927 := by
  unfold tailWord_206813
  simp only [CollatzResearch.WordTrace]
  refine ⟨7543089799759296693473093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5028726533172864462315395 7543089799759296693473093)
  ·
    refine ⟨1414329337454868130026205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7543089799759296693473093 1414329337454868130026205)
    ·
      refine ⟨530373501545575548759827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1414329337454868130026205 530373501545575548759827)
      ·
        refine ⟨795560252318363323139741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530373501545575548759827 795560252318363323139741)
        ·
          refine ⟨298335094619386246177403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 795560252318363323139741 298335094619386246177403)
          ·
            refine ⟨447502641929079369266105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298335094619386246177403 447502641929079369266105)
            ·
              refine ⟨335626981446809526949579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447502641929079369266105 335626981446809526949579)
              ·
                refine ⟨503440472170214290424369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335626981446809526949579 503440472170214290424369)
                ·
                  refine ⟨377580354127660717818277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503440472170214290424369 377580354127660717818277)
                  ·
                    refine ⟨70796316398936384590927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 377580354127660717818277 70796316398936384590927)
                    ·
                      rfl

theorem cell22_206813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_206813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206813 prefixEnd_206813 := by exact prefixLift 206813
  have htrace : WordTrace (prefixWord ++ tailWord_206813) baseStart_206813 baseEnd_206813 := by
    simpa [prefixWord, tailWord_206813, baseEnd_206813] using wordTrace_append hprefix tailTrace_206813
  have hstable : (prefixWord ++ tailWord_206813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206813).length < 2 ^ (prefixWord ++ tailWord_206813).sum := by decide
  have hdescent : baseEnd_206813 < baseStart_206813 := by decide
  rcases family_descends (prefixWord ++ tailWord_206813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206899 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 3, 5]
def baseStart_206899 : Nat := 118140960795 + 206899 * 2 ^ 59
def prefixEnd_206899 : Nat := 4983230072969 + 3 ^ 40 * 206899 * 2
def baseEnd_206899 : Nat := 70825755956460826940663

theorem tailTrace_206899 : CollatzResearch.WordTrace tailWord_206899 prefixEnd_206899 70825755956460826940663 := by
  unfold tailWord_206899
  simp only [CollatzResearch.WordTrace]
  refine ⟨7546226477447733381103751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5030817651631822254069167 7546226477447733381103751)
  ·
    refine ⟨11319339716171600071655627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7546226477447733381103751 11319339716171600071655627)
    ·
      refine ⟨16979009574257400107483441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11319339716171600071655627 16979009574257400107483441)
      ·
        refine ⟨12734257180693050080612581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16979009574257400107483441 12734257180693050080612581)
        ·
          refine ⟨2387673221379946890114859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12734257180693050080612581 2387673221379946890114859)
          ·
            refine ⟨3581509832069920335172289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387673221379946890114859 3581509832069920335172289)
            ·
              refine ⟨2686132374052440251379217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3581509832069920335172289 2686132374052440251379217)
              ·
                refine ⟨2014599280539330188534413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2686132374052440251379217 2014599280539330188534413)
                ·
                  refine ⟨755474730202248820700405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2014599280539330188534413 755474730202248820700405)
                  ·
                    refine ⟨70825755956460826940663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 755474730202248820700405 70825755956460826940663)
                    ·
                      rfl

theorem cell22_206899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 5].length) (baseStart_206899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206899 prefixEnd_206899 := by exact prefixLift 206899
  have htrace : WordTrace (prefixWord ++ tailWord_206899) baseStart_206899 baseEnd_206899 := by
    simpa [prefixWord, tailWord_206899, baseEnd_206899] using wordTrace_append hprefix tailTrace_206899
  have hstable : (prefixWord ++ tailWord_206899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206899).length < 2 ^ (prefixWord ++ tailWord_206899).sum := by decide
  have hdescent : baseEnd_206899 < baseStart_206899 := by decide
  rcases family_descends (prefixWord ++ tailWord_206899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206918 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_206918 : Nat := 118140960795 + 206918 * 2 ^ 59
def prefixEnd_206918 : Nat := 4983230072969 + 3 ^ 40 * 206918 * 2
def baseEnd_206918 : Nat := 23610753348250370238535

theorem tailTrace_206918 : CollatzResearch.WordTrace tailWord_206918 prefixEnd_206918 23610753348250370238535 := by
  unfold tailWord_206918
  simp only [CollatzResearch.WordTrace]
  refine ⟨235841233261840613313919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5031279642919266417363605 235841233261840613313919)
  ·
    refine ⟨353761849892760919970879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235841233261840613313919 353761849892760919970879)
    ·
      refine ⟨530642774839141379956319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353761849892760919970879 530642774839141379956319)
      ·
        refine ⟨795964162258712069934479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530642774839141379956319 795964162258712069934479)
        ·
          refine ⟨1193946243388068104901719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795964162258712069934479 1193946243388068104901719)
          ·
            refine ⟨1790919365082102157352579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193946243388068104901719 1790919365082102157352579)
            ·
              refine ⟨2686379047623153236028869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790919365082102157352579 2686379047623153236028869)
              ·
                refine ⟨503696071429341231755413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2686379047623153236028869 503696071429341231755413)
                ·
                  refine ⟨23610753348250370238535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 503696071429341231755413 23610753348250370238535)
                  ·
                    rfl

theorem cell22_206918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_206918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_206918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_206918 prefixEnd_206918 := by exact prefixLift 206918
  have htrace : WordTrace (prefixWord ++ tailWord_206918) baseStart_206918 baseEnd_206918 := by
    simpa [prefixWord, tailWord_206918, baseEnd_206918] using wordTrace_append hprefix tailTrace_206918
  have hstable : (prefixWord ++ tailWord_206918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206918).length < 2 ^ (prefixWord ++ tailWord_206918).sum := by decide
  have hdescent : baseEnd_206918 < baseStart_206918 := by decide
  rcases family_descends (prefixWord ++ tailWord_206918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207008 : List Nat := [2, 1, 1, 4, 2, 3, 2, 2, 5]
def baseStart_207008 : Nat := 118140960795 + 207008 * 2 ^ 59
def prefixEnd_207008 : Nat := 4983230072969 + 3 ^ 40 * 207008 * 2
def baseEnd_207008 : Nat := 23621022961340291988443

theorem tailTrace_207008 : CollatzResearch.WordTrace tailWord_207008 prefixEnd_207008 23621022961340291988443 := by
  unfold tailWord_207008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3775101017026422498410839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5033468022701896664547785 3775101017026422498410839)
  ·
    refine ⟨5662651525539633747616259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3775101017026422498410839 5662651525539633747616259)
    ·
      refine ⟨8493977288309450621424389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5662651525539633747616259 8493977288309450621424389)
      ·
        refine ⟨1592620741558021991517073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8493977288309450621424389 1592620741558021991517073)
        ·
          refine ⟨1194465556168516493637805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1592620741558021991517073 1194465556168516493637805)
          ·
            refine ⟨447924583563193685114177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1194465556168516493637805 447924583563193685114177)
            ·
              refine ⟨335943437672395263835633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447924583563193685114177 335943437672395263835633)
              ·
                refine ⟨251957578254296447876725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335943437672395263835633 251957578254296447876725)
                ·
                  refine ⟨23621022961340291988443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 251957578254296447876725 23621022961340291988443)
                  ·
                    rfl

theorem cell22_207008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 5].length) (baseStart_207008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207008 prefixEnd_207008 := by exact prefixLift 207008
  have htrace : WordTrace (prefixWord ++ tailWord_207008) baseStart_207008 baseEnd_207008 := by
    simpa [prefixWord, tailWord_207008, baseEnd_207008] using wordTrace_append hprefix tailTrace_207008
  have hstable : (prefixWord ++ tailWord_207008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207008).length < 2 ^ (prefixWord ++ tailWord_207008).sum := by decide
  have hdescent : baseEnd_207008 < baseStart_207008 := by decide
  rcases family_descends (prefixWord ++ tailWord_207008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207012 : List Nat := [2, 3, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_207012 : Nat := 118140960795 + 207012 * 2 ^ 59
def prefixEnd_207012 : Nat := 4983230072969 + 3 ^ 40 * 207012 * 2
def baseEnd_207012 : Nat := 70864438165766198865317

theorem tailTrace_207012 : CollatzResearch.WordTrace tailWord_207012 prefixEnd_207012 70864438165766198865317 := by
  unfold tailWord_207012
  simp only [CollatzResearch.WordTrace]
  refine ⟨3775173963019176839983645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5033565284025569119978193 3775173963019176839983645)
  ·
    refine ⟨1415690236132191314993867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3775173963019176839983645 1415690236132191314993867)
    ·
      refine ⟨2123535354198286972490801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1415690236132191314993867 2123535354198286972490801)
      ·
        refine ⟨1592651515648715229368101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2123535354198286972490801 1592651515648715229368101)
        ·
          refine ⟨298622159184134105506519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1592651515648715229368101 298622159184134105506519)
          ·
            refine ⟨447933238776201158259779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298622159184134105506519 447933238776201158259779)
            ·
              refine ⟨671899858164301737389669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447933238776201158259779 671899858164301737389669)
              ·
                refine ⟨125981223405806575760563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 671899858164301737389669 125981223405806575760563)
                ·
                  refine ⟨188971835108709863640845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125981223405806575760563 188971835108709863640845)
                  ·
                    refine ⟨70864438165766198865317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188971835108709863640845 70864438165766198865317)
                    ·
                      rfl

theorem cell22_207012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_207012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207012 prefixEnd_207012 := by exact prefixLift 207012
  have htrace : WordTrace (prefixWord ++ tailWord_207012) baseStart_207012 baseEnd_207012 := by
    simpa [prefixWord, tailWord_207012, baseEnd_207012] using wordTrace_append hprefix tailTrace_207012
  have hstable : (prefixWord ++ tailWord_207012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207012).length < 2 ^ (prefixWord ++ tailWord_207012).sum := by decide
  have hdescent : baseEnd_207012 < baseStart_207012 := by decide
  rcases family_descends (prefixWord ++ tailWord_207012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207051 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 1, 5]
def baseStart_207051 : Nat := 118140960795 + 207051 * 2 ^ 59
def prefixEnd_207051 : Nat := 4983230072969 + 3 ^ 40 * 207051 * 2
def baseEnd_207051 : Nat := 70877788662783097140197

theorem tailTrace_207051 : CollatzResearch.WordTrace tailWord_207051 prefixEnd_207051 70877788662783097140197 := by
  unfold tailWord_207051
  simp only [CollatzResearch.WordTrace]
  refine ⟨7551770372897063340637007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5034513581931375560424671 7551770372897063340637007)
  ·
    refine ⟨11327655559345595010955511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7551770372897063340637007 11327655559345595010955511)
    ·
      refine ⟨16991483339018392516433267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11327655559345595010955511 16991483339018392516433267)
      ·
        refine ⟨25487225008527588774649901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16991483339018392516433267 25487225008527588774649901)
        ·
          refine ⟨9557709378197845790493713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25487225008527588774649901 9557709378197845790493713)
          ·
            refine ⟨7168282033648384342870285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9557709378197845790493713 7168282033648384342870285)
            ·
              refine ⟨2688105762618144128576357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7168282033648384342870285 2688105762618144128576357)
              ·
                refine ⟨504019830490902024108067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2688105762618144128576357 504019830490902024108067)
                ·
                  refine ⟨756029745736353036162101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504019830490902024108067 756029745736353036162101)
                  ·
                    refine ⟨70877788662783097140197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 756029745736353036162101 70877788662783097140197)
                    ·
                      rfl

theorem cell22_207051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 5].length) (baseStart_207051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207051 prefixEnd_207051 := by exact prefixLift 207051
  have htrace : WordTrace (prefixWord ++ tailWord_207051) baseStart_207051 baseEnd_207051 := by
    simpa [prefixWord, tailWord_207051, baseEnd_207051] using wordTrace_append hprefix tailTrace_207051
  have hstable : (prefixWord ++ tailWord_207051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207051).length < 2 ^ (prefixWord ++ tailWord_207051).sum := by decide
  have hdescent : baseEnd_207051 < baseStart_207051 := by decide
  rcases family_descends (prefixWord ++ tailWord_207051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207098 : List Nat := [3, 1, 1, 1, 1, 5, 4, 6]
def baseStart_207098 : Nat := 118140960795 + 207098 * 2 ^ 59
def prefixEnd_207098 : Nat := 4983230072969 + 3 ^ 40 * 207098 * 2
def baseEnd_207098 : Nat := 7877097524810071246117

theorem tailTrace_207098 : CollatzResearch.WordTrace tailWord_207098 prefixEnd_207098 7877097524810071246117 := by
  unfold tailWord_207098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1888371150931697591899487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5035656402484526911731965 1888371150931697591899487)
  ·
    refine ⟨2832556726397546387849231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1888371150931697591899487 2832556726397546387849231)
    ·
      refine ⟨4248835089596319581773847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2832556726397546387849231 4248835089596319581773847)
      ·
        refine ⟨6373252634394479372660771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248835089596319581773847 6373252634394479372660771)
        ·
          refine ⟨9559878951591719058991157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6373252634394479372660771 9559878951591719058991157)
          ·
            refine ⟨896238651711723661780421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9559878951591719058991157 896238651711723661780421)
            ·
              refine ⟨168044747195948186583829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 896238651711723661780421 168044747195948186583829)
              ·
                refine ⟨7877097524810071246117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 168044747195948186583829 7877097524810071246117)
                ·
                  rfl

theorem cell22_207098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_207098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207098 prefixEnd_207098 := by exact prefixLift 207098
  have htrace : WordTrace (prefixWord ++ tailWord_207098) baseStart_207098 baseEnd_207098 := by
    simpa [prefixWord, tailWord_207098, baseEnd_207098] using wordTrace_append hprefix tailTrace_207098
  have hstable : (prefixWord ++ tailWord_207098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207098).length < 2 ^ (prefixWord ++ tailWord_207098).sum := by decide
  have hdescent : baseEnd_207098 < baseStart_207098 := by decide
  rcases family_descends (prefixWord ++ tailWord_207098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207198 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_207198 : Nat := 118140960795 + 207198 * 2 ^ 59
def prefixEnd_207198 : Nat := 4983230072969 + 3 ^ 40 * 207198 * 2
def baseEnd_207198 : Nat := 70928109766923713714747

theorem tailTrace_207198 : CollatzResearch.WordTrace tailWord_207198 prefixEnd_207198 70928109766923713714747 := by
  unfold tailWord_207198
  simp only [CollatzResearch.WordTrace]
  refine ⟨944641487920563430779781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5038087935576338297492165 944641487920563430779781)
  ·
    refine ⟨177120278985105643271209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 944641487920563430779781 177120278985105643271209)
    ·
      refine ⟨132840209238829232453407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177120278985105643271209 132840209238829232453407)
      ·
        refine ⟨199260313858243848680111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132840209238829232453407 199260313858243848680111)
        ·
          refine ⟨298890470787365773020167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199260313858243848680111 298890470787365773020167)
          ·
            refine ⟨448335706181048659530251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298890470787365773020167 448335706181048659530251)
            ·
              refine ⟨672503559271572989295377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448335706181048659530251 672503559271572989295377)
              ·
                refine ⟨504377669453679741971533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672503559271572989295377 504377669453679741971533)
                ·
                  refine ⟨189141626045129903239325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504377669453679741971533 189141626045129903239325)
                  ·
                    refine ⟨70928109766923713714747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189141626045129903239325 70928109766923713714747)
                    ·
                      rfl

theorem cell22_207198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_207198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207198 prefixEnd_207198 := by exact prefixLift 207198
  have htrace : WordTrace (prefixWord ++ tailWord_207198) baseStart_207198 baseEnd_207198 := by
    simpa [prefixWord, tailWord_207198, baseEnd_207198] using wordTrace_append hprefix tailTrace_207198
  have hstable : (prefixWord ++ tailWord_207198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207198).length < 2 ^ (prefixWord ++ tailWord_207198).sum := by decide
  have hdescent : baseEnd_207198 < baseStart_207198 := by decide
  rcases family_descends (prefixWord ++ tailWord_207198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207284 : List Nat := [2, 5, 2, 2, 1, 2, 8]
def baseStart_207284 : Nat := 118140960795 + 207284 * 2 ^ 59
def prefixEnd_207284 : Nat := 4983230072969 + 3 ^ 40 * 207284 * 2
def baseEnd_207284 : Nat := 2628057382386968743129

theorem tailTrace_207284 : CollatzResearch.WordTrace tailWord_207284 prefixEnd_207284 2628057382386968743129 := by
  unfold tailWord_207284
  simp only [CollatzResearch.WordTrace]
  refine ⟨3780134290526472066934453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5040179054035296089245937 3780134290526472066934453)
  ·
    refine ⟨354387589736856756275105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3780134290526472066934453 354387589736856756275105)
    ·
      refine ⟨265790692302642567206329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354387589736856756275105 265790692302642567206329)
      ·
        refine ⟨199343019226981925404747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265790692302642567206329 199343019226981925404747)
        ·
          refine ⟨299014528840472888107121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199343019226981925404747 299014528840472888107121)
          ·
            refine ⟨224260896630354666080341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299014528840472888107121 224260896630354666080341)
            ·
              refine ⟨2628057382386968743129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 224260896630354666080341 2628057382386968743129)
              ·
                rfl

theorem cell22_207284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 8].length) (baseStart_207284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207284 prefixEnd_207284 := by exact prefixLift 207284
  have htrace : WordTrace (prefixWord ++ tailWord_207284) baseStart_207284 baseEnd_207284 := by
    simpa [prefixWord, tailWord_207284, baseEnd_207284] using wordTrace_append hprefix tailTrace_207284
  have hstable : (prefixWord ++ tailWord_207284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207284).length < 2 ^ (prefixWord ++ tailWord_207284).sum := by decide
  have hdescent : baseEnd_207284 < baseStart_207284 := by decide
  rcases family_descends (prefixWord ++ tailWord_207284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207357 : List Nat := [1, 4, 1, 1, 1, 3, 3, 4, 4]
def baseStart_207357 : Nat := 118140960795 + 207357 * 2 ^ 59
def prefixEnd_207357 : Nat := 4983230072969 + 3 ^ 40 * 207357 * 2
def baseEnd_207357 : Nat := 23660846238766766329753

theorem tailTrace_207357 : CollatzResearch.WordTrace tailWord_207357 prefixEnd_207357 23660846238766766329753 := by
  unfold tailWord_207357
  simp only [CollatzResearch.WordTrace]
  refine ⟨7562931109788477601276325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5041954073192318400850883 7562931109788477601276325)
  ·
    refine ⟨1418049583085339550239311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7562931109788477601276325 1418049583085339550239311)
    ·
      refine ⟨2127074374628009325358967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1418049583085339550239311 2127074374628009325358967)
      ·
        refine ⟨3190611561942013988038451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127074374628009325358967 3190611561942013988038451)
        ·
          refine ⟨4785917342913020982057677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3190611561942013988038451 4785917342913020982057677)
          ·
            refine ⟨1794719003592382868271629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4785917342913020982057677 1794719003592382868271629)
            ·
              refine ⟨673019626347143575601861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1794719003592382868271629 673019626347143575601861)
              ·
                refine ⟨126191179940089420425349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 673019626347143575601861 126191179940089420425349)
                ·
                  refine ⟨23660846238766766329753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126191179940089420425349 23660846238766766329753)
                  ·
                    rfl

theorem cell22_207357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_207357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207357 prefixEnd_207357 := by exact prefixLift 207357
  have htrace : WordTrace (prefixWord ++ tailWord_207357) baseStart_207357 baseEnd_207357 := by
    simpa [prefixWord, tailWord_207357, baseEnd_207357] using wordTrace_append hprefix tailTrace_207357
  have hstable : (prefixWord ++ tailWord_207357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207357).length < 2 ^ (prefixWord ++ tailWord_207357).sum := by decide
  have hdescent : baseEnd_207357 < baseStart_207357 := by decide
  rcases family_descends (prefixWord ++ tailWord_207357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207370 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_207370 : Nat := 118140960795 + 207370 * 2 ^ 59
def prefixEnd_207370 : Nat := 4983230072969 + 3 ^ 40 * 207370 * 2
def baseEnd_207370 : Nat := 70986988881972598414219

theorem tailTrace_207370 : CollatzResearch.WordTrace tailWord_207370 prefixEnd_207370 70986988881972598414219 := by
  unfold tailWord_207370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1890851314685345205374891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5042270172494253880999709 1890851314685345205374891)
  ·
    refine ⟨2836276972028017808062337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1890851314685345205374891 2836276972028017808062337)
    ·
      refine ⟨2127207729021013356046753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2836276972028017808062337 2127207729021013356046753)
      ·
        refine ⟨1595405796765760017035065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2127207729021013356046753 1595405796765760017035065)
        ·
          refine ⟨1196554347574320012776299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1595405796765760017035065 1196554347574320012776299)
          ·
            refine ⟨1794831521361480019164449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196554347574320012776299 1794831521361480019164449)
            ·
              refine ⟨1346123641021110014373337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1794831521361480019164449 1346123641021110014373337)
              ·
                refine ⟨1009592730765832510780003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346123641021110014373337 1009592730765832510780003)
                ·
                  refine ⟨1514389096148748766170005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009592730765832510780003 1514389096148748766170005)
                  ·
                    refine ⟨70986988881972598414219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1514389096148748766170005 70986988881972598414219)
                    ·
                      rfl

theorem cell22_207370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_207370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207370 prefixEnd_207370 := by exact prefixLift 207370
  have htrace : WordTrace (prefixWord ++ tailWord_207370) baseStart_207370 baseEnd_207370 := by
    simpa [prefixWord, tailWord_207370, baseEnd_207370] using wordTrace_append hprefix tailTrace_207370
  have hstable : (prefixWord ++ tailWord_207370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207370).length < 2 ^ (prefixWord ++ tailWord_207370).sum := by decide
  have hdescent : baseEnd_207370 < baseStart_207370 := by decide
  rcases family_descends (prefixWord ++ tailWord_207370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207372 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_207372 : Nat := 118140960795 + 207372 * 2 ^ 59
def prefixEnd_207372 : Nat := 4983230072969 + 3 ^ 40 * 207372 * 2
def baseEnd_207372 : Nat := 70987673522845259864213

theorem tailTrace_207372 : CollatzResearch.WordTrace tailWord_207372 prefixEnd_207372 70987673522845259864213 := by
  unfold tailWord_207372
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781739102367067581536185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5042318803156090108714913 3781739102367067581536185)
  ·
    refine ⟨2836304326775300686152139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3781739102367067581536185 2836304326775300686152139)
    ·
      refine ⟨4254456490162951029228209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2836304326775300686152139 4254456490162951029228209)
      ·
        refine ⟨3190842367622213271921157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4254456490162951029228209 3190842367622213271921157)
        ·
          refine ⟨598282943929164988485217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3190842367622213271921157 598282943929164988485217)
          ·
            refine ⟨448712207946873741363913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598282943929164988485217 448712207946873741363913)
            ·
              refine ⟨336534155960155306022935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448712207946873741363913 336534155960155306022935)
              ·
                refine ⟨504801233940232959034403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336534155960155306022935 504801233940232959034403)
                ·
                  refine ⟨757201850910349438551605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504801233940232959034403 757201850910349438551605)
                  ·
                    refine ⟨70987673522845259864213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 757201850910349438551605 70987673522845259864213)
                    ·
                      rfl

theorem cell22_207372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_207372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207372 prefixEnd_207372 := by exact prefixLift 207372
  have htrace : WordTrace (prefixWord ++ tailWord_207372) baseStart_207372 baseEnd_207372 := by
    simpa [prefixWord, tailWord_207372, baseEnd_207372] using wordTrace_append hprefix tailTrace_207372
  have hstable : (prefixWord ++ tailWord_207372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207372).length < 2 ^ (prefixWord ++ tailWord_207372).sum := by decide
  have hdescent : baseEnd_207372 < baseStart_207372 := by decide
  rcases family_descends (prefixWord ++ tailWord_207372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207445 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_207445 : Nat := 118140960795 + 207445 * 2 ^ 59
def prefixEnd_207445 : Nat := 4983230072969 + 3 ^ 40 * 207445 * 2
def baseEnd_207445 : Nat := 71012662914697402788989

theorem tailTrace_207445 : CollatzResearch.WordTrace tailWord_207445 prefixEnd_207445 71012662914697402788989 := by
  unfold tailWord_207445
  simp only [CollatzResearch.WordTrace]
  refine ⟨7566140733469668630479789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5044093822313112420319859 7566140733469668630479789)
  ·
    refine ⟨2837302775051125736429921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7566140733469668630479789 2837302775051125736429921)
    ·
      refine ⟨2127977081288344302322441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2837302775051125736429921 2127977081288344302322441)
      ·
        refine ⟨1595982810966258226741831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2127977081288344302322441 1595982810966258226741831)
        ·
          refine ⟨2393974216449387340112747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595982810966258226741831 2393974216449387340112747)
          ·
            refine ⟨3590961324674081010169121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393974216449387340112747 3590961324674081010169121)
            ·
              refine ⟨2693220993505560757626841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3590961324674081010169121 2693220993505560757626841)
              ·
                refine ⟨2019915745129170568220131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2693220993505560757626841 2019915745129170568220131)
                ·
                  refine ⟨3029873617693755852330197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019915745129170568220131 3029873617693755852330197)
                  ·
                    refine ⟨71012662914697402788989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3029873617693755852330197 71012662914697402788989)
                    ·
                      rfl

theorem cell22_207445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_207445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207445 prefixEnd_207445 := by exact prefixLift 207445
  have htrace : WordTrace (prefixWord ++ tailWord_207445) baseStart_207445 baseEnd_207445 := by
    simpa [prefixWord, tailWord_207445, baseEnd_207445] using wordTrace_append hprefix tailTrace_207445
  have hstable : (prefixWord ++ tailWord_207445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207445).length < 2 ^ (prefixWord ++ tailWord_207445).sum := by decide
  have hdescent : baseEnd_207445 < baseStart_207445 := by decide
  rcases family_descends (prefixWord ++ tailWord_207445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207475 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 6]
def baseStart_207475 : Nat := 118140960795 + 207475 * 2 ^ 59
def prefixEnd_207475 : Nat := 4983230072969 + 3 ^ 40 * 207475 * 2
def baseEnd_207475 : Nat := 23674310842595774846299

theorem tailTrace_207475 : CollatzResearch.WordTrace tailWord_207475 prefixEnd_207475 23674310842595774846299 := by
  unfold tailWord_207475
  simp only [CollatzResearch.WordTrace]
  refine ⟨7567234923360983754071879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5044823282240655836047919 7567234923360983754071879)
  ·
    refine ⟨11350852385041475631107819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7567234923360983754071879 11350852385041475631107819)
    ·
      refine ⟨17026278577562213446661729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11350852385041475631107819 17026278577562213446661729)
      ·
        refine ⟨12769708933171660084996297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17026278577562213446661729 12769708933171660084996297)
        ·
          refine ⟨9577281699878745063747223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12769708933171660084996297 9577281699878745063747223)
          ·
            refine ⟨14365922549818117595620835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9577281699878745063747223 14365922549818117595620835)
            ·
              refine ⟨21548883824727176393431253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14365922549818117595620835 21548883824727176393431253)
              ·
                refine ⟨505051964642043196721045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21548883824727176393431253 505051964642043196721045)
                ·
                  refine ⟨23674310842595774846299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 505051964642043196721045 23674310842595774846299)
                  ·
                    rfl

theorem cell22_207475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 6].length) (baseStart_207475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207475 prefixEnd_207475 := by exact prefixLift 207475
  have htrace : WordTrace (prefixWord ++ tailWord_207475) baseStart_207475 baseEnd_207475 := by
    simpa [prefixWord, tailWord_207475, baseEnd_207475] using wordTrace_append hprefix tailTrace_207475
  have hstable : (prefixWord ++ tailWord_207475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207475).length < 2 ^ (prefixWord ++ tailWord_207475).sum := by decide
  have hdescent : baseEnd_207475 < baseStart_207475 := by decide
  rcases family_descends (prefixWord ++ tailWord_207475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207505 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 5, 6]
def baseStart_207505 : Nat := 118140960795 + 207505 * 2 ^ 59
def prefixEnd_207505 : Nat := 4983230072969 + 3 ^ 40 * 207505 * 2
def baseEnd_207505 : Nat := 71033202140877246288805

theorem tailTrace_207505 : CollatzResearch.WordTrace tailWord_207505 prefixEnd_207505 71033202140877246288805 := by
  unfold tailWord_207505
  simp only [CollatzResearch.WordTrace]
  refine ⟨7568329113252298877663969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5045552742168199251775979 7568329113252298877663969)
  ·
    refine ⟨5676246834939224158247977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7568329113252298877663969 5676246834939224158247977)
    ·
      refine ⟨4257185126204418118685983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5676246834939224158247977 4257185126204418118685983)
      ·
        refine ⟨6385777689306627178028975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4257185126204418118685983 6385777689306627178028975)
        ·
          refine ⟨9578666533959940767043463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6385777689306627178028975 9578666533959940767043463)
          ·
            refine ⟨14367999800939911150565195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9578666533959940767043463 14367999800939911150565195)
            ·
              refine ⟨21551999701409866725847793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14367999800939911150565195 21551999701409866725847793)
              ·
                refine ⟨16163999776057400044385845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21551999701409866725847793 16163999776057400044385845)
                ·
                  refine ⟨1515374979005381254161173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16163999776057400044385845 1515374979005381254161173)
                  ·
                    refine ⟨71033202140877246288805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1515374979005381254161173 71033202140877246288805)
                    ·
                      rfl

theorem cell22_207505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_207505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207505 prefixEnd_207505 := by exact prefixLift 207505
  have htrace : WordTrace (prefixWord ++ tailWord_207505) baseStart_207505 baseEnd_207505 := by
    simpa [prefixWord, tailWord_207505, baseEnd_207505] using wordTrace_append hprefix tailTrace_207505
  have hstable : (prefixWord ++ tailWord_207505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207505).length < 2 ^ (prefixWord ++ tailWord_207505).sum := by decide
  have hdescent : baseEnd_207505 < baseStart_207505 := by decide
  rcases family_descends (prefixWord ++ tailWord_207505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207520 : List Nat := [2, 1, 1, 4, 14]
def baseStart_207520 : Nat := 118140960795 + 207520 * 2 ^ 59
def prefixEnd_207520 : Nat := 4983230072969 + 3 ^ 40 * 207520 * 2
def baseEnd_207520 : Nat := 292338835174576984213

theorem tailTrace_207520 : CollatzResearch.WordTrace tailWord_207520 prefixEnd_207520 292338835174576984213 := by
  unfold tailWord_207520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3784438104098978219730007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5045917472131970959640009 3784438104098978219730007)
  ·
    refine ⟨5676657156148467329595011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3784438104098978219730007 5676657156148467329595011)
    ·
      refine ⟨8514985734222700994392517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5676657156148467329595011 8514985734222700994392517)
      ·
        refine ⟨1596559825166756436448597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8514985734222700994392517 1596559825166756436448597)
        ·
          refine ⟨292338835174576984213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 1596559825166756436448597 292338835174576984213)
          ·
            rfl

theorem cell22_207520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 14].length) (baseStart_207520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207520 prefixEnd_207520 := by exact prefixLift 207520
  have htrace : WordTrace (prefixWord ++ tailWord_207520) baseStart_207520 baseEnd_207520 := by
    simpa [prefixWord, tailWord_207520, baseEnd_207520] using wordTrace_append hprefix tailTrace_207520
  have hstable : (prefixWord ++ tailWord_207520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207520).length < 2 ^ (prefixWord ++ tailWord_207520).sum := by decide
  have hdescent : baseEnd_207520 < baseStart_207520 := by decide
  rcases family_descends (prefixWord ++ tailWord_207520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207541 : List Nat := [1, 3, 3, 3, 1, 1, 2, 3, 2, 3]
def baseStart_207541 : Nat := 118140960795 + 207541 * 2 ^ 59
def prefixEnd_207541 : Nat := 4983230072969 + 3 ^ 40 * 207541 * 2
def baseEnd_207541 : Nat := 71045525676585152388695

theorem tailTrace_207541 : CollatzResearch.WordTrace tailWord_207541 prefixEnd_207541 71045525676585152388695 := by
  unfold tailWord_207541
  simp only [CollatzResearch.WordTrace]
  refine ⟨7569642141121877025974477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5046428094081251350649651 7569642141121877025974477)
  ·
    refine ⟨2838615802920703884740429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7569642141121877025974477 2838615802920703884740429)
    ·
      refine ⟨1064480926095263956777661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2838615802920703884740429 1064480926095263956777661)
      ·
        refine ⟨399180347285723983791623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1064480926095263956777661 399180347285723983791623)
        ·
          refine ⟨598770520928585975687435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399180347285723983791623 598770520928585975687435)
          ·
            refine ⟨898155781392878963531153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598770520928585975687435 898155781392878963531153)
            ·
              refine ⟨673616836044659222648365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 898155781392878963531153 673616836044659222648365)
              ·
                refine ⟨252606313516747208493137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 673616836044659222648365 252606313516747208493137)
                ·
                  refine ⟨189454735137560406369853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252606313516747208493137 189454735137560406369853)
                  ·
                    refine ⟨71045525676585152388695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189454735137560406369853 71045525676585152388695)
                    ·
                      rfl

theorem cell22_207541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_207541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207541 prefixEnd_207541 := by exact prefixLift 207541
  have htrace : WordTrace (prefixWord ++ tailWord_207541) baseStart_207541 baseEnd_207541 := by
    simpa [prefixWord, tailWord_207541, baseEnd_207541] using wordTrace_append hprefix tailTrace_207541
  have hstable : (prefixWord ++ tailWord_207541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207541).length < 2 ^ (prefixWord ++ tailWord_207541).sum := by decide
  have hdescent : baseEnd_207541 < baseStart_207541 := by decide
  rcases family_descends (prefixWord ++ tailWord_207541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207556 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_207556 : Nat := 118140960795 + 207556 * 2 ^ 59
def prefixEnd_207556 : Nat := 4983230072969 + 3 ^ 40 * 207556 * 2
def baseEnd_207556 : Nat := 71050660483130113263649

theorem tailTrace_207556 : CollatzResearch.WordTrace tailWord_207556 prefixEnd_207556 71050660483130113263649 := by
  unfold tailWord_207556
  simp only [CollatzResearch.WordTrace]
  refine ⟨3785094618033767293885261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5046792824045023058513681 3785094618033767293885261)
  ·
    refine ⟨1419410481762662735206973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3785094618033767293885261 1419410481762662735206973)
    ·
      refine ⟨532278930660998525702615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1419410481762662735206973 532278930660998525702615)
      ·
        refine ⟨798418395991497788553923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532278930660998525702615 798418395991497788553923)
        ·
          refine ⟨1197627593987246682830885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798418395991497788553923 1197627593987246682830885)
          ·
            refine ⟨224555173872608753030791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1197627593987246682830885 224555173872608753030791)
            ·
              refine ⟨336832760808913129546187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224555173872608753030791 336832760808913129546187)
              ·
                refine ⟨505249141213369694319281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336832760808913129546187 505249141213369694319281)
                ·
                  refine ⟨378936855910027270739461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505249141213369694319281 378936855910027270739461)
                  ·
                    refine ⟨71050660483130113263649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 378936855910027270739461 71050660483130113263649)
                    ·
                      rfl

theorem cell22_207556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_207556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207556 prefixEnd_207556 := by exact prefixLift 207556
  have htrace : WordTrace (prefixWord ++ tailWord_207556) baseStart_207556 baseEnd_207556 := by
    simpa [prefixWord, tailWord_207556, baseEnd_207556] using wordTrace_append hprefix tailTrace_207556
  have hstable : (prefixWord ++ tailWord_207556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207556).length < 2 ^ (prefixWord ++ tailWord_207556).sum := by decide
  have hdescent : baseEnd_207556 < baseStart_207556 := by decide
  rcases family_descends (prefixWord ++ tailWord_207556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207605 : List Nat := [1, 3, 6, 1, 1, 2, 2, 6]
def baseStart_207605 : Nat := 118140960795 + 207605 * 2 ^ 59
def prefixEnd_207605 : Nat := 4983230072969 + 3 ^ 40 * 207605 * 2
def baseEnd_207605 : Nat := 7896381576056702087611

theorem tailTrace_207605 : CollatzResearch.WordTrace tailWord_207605 prefixEnd_207605 7896381576056702087611 := by
  unfold tailWord_207605
  simp only [CollatzResearch.WordTrace]
  refine ⟨7571976412890015956304269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5047984275260010637536179 7571976412890015956304269)
  ·
    refine ⟨2839491154833755983614101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7571976412890015956304269 2839491154833755983614101)
    ·
      refine ⟨133101147882832311731911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2839491154833755983614101 133101147882832311731911)
      ·
        refine ⟨199651721824248467597867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133101147882832311731911 199651721824248467597867)
        ·
          refine ⟨299477582736372701396801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199651721824248467597867 299477582736372701396801)
          ·
            refine ⟨224608187052279526047601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299477582736372701396801 224608187052279526047601)
            ·
              refine ⟨168456140289209644535701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224608187052279526047601 168456140289209644535701)
              ·
                refine ⟨7896381576056702087611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 168456140289209644535701 7896381576056702087611)
                ·
                  rfl

theorem cell22_207605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 6].length) (baseStart_207605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207605 prefixEnd_207605 := by exact prefixLift 207605
  have htrace : WordTrace (prefixWord ++ tailWord_207605) baseStart_207605 baseEnd_207605 := by
    simpa [prefixWord, tailWord_207605, baseEnd_207605] using wordTrace_append hprefix tailTrace_207605
  have hstable : (prefixWord ++ tailWord_207605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207605).length < 2 ^ (prefixWord ++ tailWord_207605).sum := by decide
  have hdescent : baseEnd_207605 < baseStart_207605 := by decide
  rcases family_descends (prefixWord ++ tailWord_207605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207644 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 6]
def baseStart_207644 : Nat := 118140960795 + 207644 * 2 ^ 59
def prefixEnd_207644 : Nat := 4983230072969 + 3 ^ 40 * 207644 * 2
def baseEnd_207644 : Nat := 23693594893842405687793

theorem tailTrace_207644 : CollatzResearch.WordTrace tailWord_207644 prefixEnd_207644 23693594893842405687793 := by
  unfold tailWord_207644
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786699429874362808486993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5048932573165817077982657 3786699429874362808486993)
  ·
    refine ⟨2840024572405772106365245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3786699429874362808486993 2840024572405772106365245)
    ·
      refine ⟨1065009214652164539886967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2840024572405772106365245 1065009214652164539886967)
      ·
        refine ⟨1597513821978246809830451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065009214652164539886967 1597513821978246809830451)
        ·
          refine ⟨2396270732967370214745677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1597513821978246809830451 2396270732967370214745677)
          ·
            refine ⟨898601524862763830529629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2396270732967370214745677 898601524862763830529629)
            ·
              refine ⟨336975571823536436448611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 898601524862763830529629 336975571823536436448611)
              ·
                refine ⟨505463357735304654672917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336975571823536436448611 505463357735304654672917)
                ·
                  refine ⟨23693594893842405687793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 505463357735304654672917 23693594893842405687793)
                  ·
                    rfl

theorem cell22_207644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_207644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207644 prefixEnd_207644 := by exact prefixLift 207644
  have htrace : WordTrace (prefixWord ++ tailWord_207644) baseStart_207644 baseEnd_207644 := by
    simpa [prefixWord, tailWord_207644, baseEnd_207644] using wordTrace_append hprefix tailTrace_207644
  have hstable : (prefixWord ++ tailWord_207644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207644).length < 2 ^ (prefixWord ++ tailWord_207644).sum := by decide
  have hdescent : baseEnd_207644 < baseStart_207644 := by decide
  rcases family_descends (prefixWord ++ tailWord_207644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207672 : List Nat := [2, 1, 2, 1, 3, 2, 1, 10]
def baseStart_207672 : Nat := 118140960795 + 207672 * 2 ^ 59
def prefixEnd_207672 : Nat := 4983230072969 + 3 ^ 40 * 207672 * 2
def baseEnd_207672 : Nat := 7898929961527164151477

theorem tailTrace_207672 : CollatzResearch.WordTrace tailWord_207672 prefixEnd_207672 7898929961527164151477 := by
  unfold tailWord_207672
  simp only [CollatzResearch.WordTrace]
  refine ⟨3787210051823643199496635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5049613402431524265995513 3787210051823643199496635)
  ·
    refine ⟨5680815077735464799244953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3787210051823643199496635 5680815077735464799244953)
    ·
      refine ⟨4260611308301598599433715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5680815077735464799244953 4260611308301598599433715)
      ·
        refine ⟨6390916962452397899150573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4260611308301598599433715 6390916962452397899150573)
        ·
          refine ⟨2396593860919649212181465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6390916962452397899150573 2396593860919649212181465)
          ·
            refine ⟨1797445395689736909136099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2396593860919649212181465 1797445395689736909136099)
            ·
              refine ⟨2696168093534605363704149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797445395689736909136099 2696168093534605363704149)
              ·
                refine ⟨7898929961527164151477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2696168093534605363704149 7898929961527164151477)
                ·
                  rfl

theorem cell22_207672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 10].length) (baseStart_207672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207672 prefixEnd_207672 := by exact prefixLift 207672
  have htrace : WordTrace (prefixWord ++ tailWord_207672) baseStart_207672 baseEnd_207672 := by
    simpa [prefixWord, tailWord_207672, baseEnd_207672] using wordTrace_append hprefix tailTrace_207672
  have hstable : (prefixWord ++ tailWord_207672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207672).length < 2 ^ (prefixWord ++ tailWord_207672).sum := by decide
  have hdescent : baseEnd_207672 < baseStart_207672 := by decide
  rcases family_descends (prefixWord ++ tailWord_207672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207704 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 7, 3]
def baseStart_207704 : Nat := 118140960795 + 207704 * 2 ^ 59
def prefixEnd_207704 : Nat := 4983230072969 + 3 ^ 40 * 207704 * 2
def baseEnd_207704 : Nat := 71101323907707060563195

theorem tailTrace_207704 : CollatzResearch.WordTrace tailWord_207704 prefixEnd_207704 71101323907707060563195 := by
  unfold tailWord_207704
  simp only [CollatzResearch.WordTrace]
  refine ⟨3787793619765677932079083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5050391493020903909438777 3787793619765677932079083)
  ·
    refine ⟨5681690429648516898118625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3787793619765677932079083 5681690429648516898118625)
    ·
      refine ⟨4261267822236387673588969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5681690429648516898118625 4261267822236387673588969)
      ·
        refine ⟨3195950866677290755191727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4261267822236387673588969 3195950866677290755191727)
        ·
          refine ⟨4793926300015936132787591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3195950866677290755191727 4793926300015936132787591)
          ·
            refine ⟨7190889450023904199181387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4793926300015936132787591 7190889450023904199181387)
            ·
              refine ⟨10786334175035856298772081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7190889450023904199181387 10786334175035856298772081)
              ·
                refine ⟨8089750631276892224079061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10786334175035856298772081 8089750631276892224079061)
                ·
                  refine ⟨189603530420552161501853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8089750631276892224079061 189603530420552161501853)
                  ·
                    refine ⟨71101323907707060563195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189603530420552161501853 71101323907707060563195)
                    ·
                      rfl

theorem cell22_207704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_207704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207704 prefixEnd_207704 := by exact prefixLift 207704
  have htrace : WordTrace (prefixWord ++ tailWord_207704) baseStart_207704 baseEnd_207704 := by
    simpa [prefixWord, tailWord_207704, baseEnd_207704] using wordTrace_append hprefix tailTrace_207704
  have hstable : (prefixWord ++ tailWord_207704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207704).length < 2 ^ (prefixWord ++ tailWord_207704).sum := by decide
  have hdescent : baseEnd_207704 < baseStart_207704 := by decide
  rcases family_descends (prefixWord ++ tailWord_207704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207749 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_207749 : Nat := 118140960795 + 207749 * 2 ^ 59
def prefixEnd_207749 : Nat := 4983230072969 + 3 ^ 40 * 207749 * 2
def baseEnd_207749 : Nat := 71116728327341943188057

theorem tailTrace_207749 : CollatzResearch.WordTrace tailWord_207749 prefixEnd_207749 71116728327341943188057 := by
  unfold tailWord_207749
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577228524368328549546301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5051485682912219033030867 7577228524368328549546301)
  ·
    refine ⟨2841460696638123206079863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7577228524368328549546301 2841460696638123206079863)
    ·
      refine ⟨4262191044957184809119795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2841460696638123206079863 4262191044957184809119795)
      ·
        refine ⟨6393286567435777213679693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4262191044957184809119795 6393286567435777213679693)
        ·
          refine ⟨2397482462788416455129885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6393286567435777213679693 2397482462788416455129885)
          ·
            refine ⟨899055923545656170673707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2397482462788416455129885 899055923545656170673707)
            ·
              refine ⟨1348583885318484256010561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899055923545656170673707 1348583885318484256010561)
              ·
                refine ⟨1011437913988863192007921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1348583885318484256010561 1011437913988863192007921)
                ·
                  refine ⟨758578435491647394005941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1011437913988863192007921 758578435491647394005941)
                  ·
                    refine ⟨71116728327341943188057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 758578435491647394005941 71116728327341943188057)
                    ·
                      rfl

theorem cell22_207749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_207749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207749 prefixEnd_207749 := by exact prefixLift 207749
  have htrace : WordTrace (prefixWord ++ tailWord_207749) baseStart_207749 baseEnd_207749 := by
    simpa [prefixWord, tailWord_207749, baseEnd_207749] using wordTrace_append hprefix tailTrace_207749
  have hstable : (prefixWord ++ tailWord_207749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207749).length < 2 ^ (prefixWord ++ tailWord_207749).sum := by decide
  have hdescent : baseEnd_207749 < baseStart_207749 := by decide
  rcases family_descends (prefixWord ++ tailWord_207749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207751 : List Nat := [1, 1, 4, 2, 3, 1, 3, 2, 5]
def baseStart_207751 : Nat := 118140960795 + 207751 * 2 ^ 59
def prefixEnd_207751 : Nat := 4983230072969 + 3 ^ 40 * 207751 * 2
def baseEnd_207751 : Nat := 23705804322738201546017

theorem tailTrace_207751 : CollatzResearch.WordTrace tailWord_207751 prefixEnd_207751 23705804322738201546017 := by
  unfold tailWord_207751
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577301470361082891119107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5051534313574055260746071 7577301470361082891119107)
  ·
    refine ⟨11365952205541624336678661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7577301470361082891119107 11365952205541624336678661)
    ·
      refine ⟨2131116038539054563127249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11365952205541624336678661 2131116038539054563127249)
      ·
        refine ⟨1598337028904290922345437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2131116038539054563127249 1598337028904290922345437)
        ·
          refine ⟨599376385839109095879539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1598337028904290922345437 599376385839109095879539)
          ·
            refine ⟨899064578758663643819309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599376385839109095879539 899064578758663643819309)
            ·
              refine ⟨337149217034498866432241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 899064578758663643819309 337149217034498866432241)
              ·
                refine ⟨252861912775874149824181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337149217034498866432241 252861912775874149824181)
                ·
                  refine ⟨23705804322738201546017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252861912775874149824181 23705804322738201546017)
                  ·
                    rfl

theorem cell22_207751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 5].length) (baseStart_207751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207751 prefixEnd_207751 := by exact prefixLift 207751
  have htrace : WordTrace (prefixWord ++ tailWord_207751) baseStart_207751 baseEnd_207751 := by
    simpa [prefixWord, tailWord_207751, baseEnd_207751] using wordTrace_append hprefix tailTrace_207751
  have hstable : (prefixWord ++ tailWord_207751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207751).length < 2 ^ (prefixWord ++ tailWord_207751).sum := by decide
  have hdescent : baseEnd_207751 < baseStart_207751 := by decide
  rcases family_descends (prefixWord ++ tailWord_207751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207779 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 6]
def baseStart_207779 : Nat := 118140960795 + 207779 * 2 ^ 59
def prefixEnd_207779 : Nat := 4983230072969 + 3 ^ 40 * 207779 * 2
def baseEnd_207779 : Nat := 23708999313477288312655

theorem tailTrace_207779 : CollatzResearch.WordTrace tailWord_207779 prefixEnd_207779 23708999313477288312655 := by
  unfold tailWord_207779
  simp only [CollatzResearch.WordTrace]
  refine ⟨7578322714259643673138391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5052215142839762448758927 7578322714259643673138391)
  ·
    refine ⟨11367484071389465509707587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7578322714259643673138391 11367484071389465509707587)
    ·
      refine ⟨17051226107084198264561381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11367484071389465509707587 17051226107084198264561381)
      ·
        refine ⟨3197104895078287174605259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17051226107084198264561381 3197104895078287174605259)
        ·
          refine ⟨4795657342617430761907889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3197104895078287174605259 4795657342617430761907889)
          ·
            refine ⟨3596743006963073071430917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4795657342617430761907889 3596743006963073071430917)
            ·
              refine ⟨674389313805576200893297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3596743006963073071430917 674389313805576200893297)
              ·
                refine ⟨505791985354182150669973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674389313805576200893297 505791985354182150669973)
                ·
                  refine ⟨23708999313477288312655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 505791985354182150669973 23708999313477288312655)
                  ·
                    rfl

theorem cell22_207779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 6].length) (baseStart_207779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207779 prefixEnd_207779 := by exact prefixLift 207779
  have htrace : WordTrace (prefixWord ++ tailWord_207779) baseStart_207779 baseEnd_207779 := by
    simpa [prefixWord, tailWord_207779, baseEnd_207779] using wordTrace_append hprefix tailTrace_207779
  have hstable : (prefixWord ++ tailWord_207779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207779).length < 2 ^ (prefixWord ++ tailWord_207779).sum := by decide
  have hdescent : baseEnd_207779 < baseStart_207779 := by decide
  rcases family_descends (prefixWord ++ tailWord_207779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207789 : List Nat := [1, 5, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_207789 : Nat := 118140960795 + 207789 * 2 ^ 59
def prefixEnd_207789 : Nat := 4983230072969 + 3 ^ 40 * 207789 * 2
def baseEnd_207789 : Nat := 71130421144795172187935

theorem tailTrace_207789 : CollatzResearch.WordTrace tailWord_207789 prefixEnd_207789 71130421144795172187935 := by
  unfold tailWord_207789
  simp only [CollatzResearch.WordTrace]
  refine ⟨7578687444223415381002421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5052458296148943587334947 7578687444223415381002421)
  ·
    refine ⟨710501947895945191968977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7578687444223415381002421 710501947895945191968977)
    ·
      refine ⟨532876460921958893976733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 710501947895945191968977 532876460921958893976733)
      ·
        refine ⟨199828672845734585241275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 532876460921958893976733 199828672845734585241275)
        ·
          refine ⟨299743009268601877861913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199828672845734585241275 299743009268601877861913)
          ·
            refine ⟨224807256951451408396435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299743009268601877861913 224807256951451408396435)
            ·
              refine ⟨337210885427177112594653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224807256951451408396435 337210885427177112594653)
              ·
                refine ⟨126454082035191417222995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337210885427177112594653 126454082035191417222995)
                ·
                  refine ⟨189681123052787125834493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126454082035191417222995 189681123052787125834493)
                  ·
                    refine ⟨71130421144795172187935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189681123052787125834493 71130421144795172187935)
                    ·
                      rfl

theorem cell22_207789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_207789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207789 prefixEnd_207789 := by exact prefixLift 207789
  have htrace : WordTrace (prefixWord ++ tailWord_207789) baseStart_207789 baseEnd_207789 := by
    simpa [prefixWord, tailWord_207789, baseEnd_207789] using wordTrace_append hprefix tailTrace_207789
  have hstable : (prefixWord ++ tailWord_207789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207789).length < 2 ^ (prefixWord ++ tailWord_207789).sum := by decide
  have hdescent : baseEnd_207789 < baseStart_207789 := by decide
  rcases family_descends (prefixWord ++ tailWord_207789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207858 : List Nat := [3, 2, 1, 5, 2, 9]
def baseStart_207858 : Nat := 118140960795 + 207858 * 2 ^ 59
def prefixEnd_207858 : Nat := 4983230072969 + 3 ^ 40 * 207858 * 2
def baseEnd_207858 : Nat := 878444953764222126083

theorem tailTrace_207858 : CollatzResearch.WordTrace tailWord_207858 prefixEnd_207858 878444953764222126083 := by
  unfold tailWord_207858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1895301020243360041316057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5054136053982293443509485 1895301020243360041316057)
  ·
    refine ⟨1421475765182520030987043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1895301020243360041316057 1421475765182520030987043)
    ·
      refine ⟨2132213647773780046480565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1421475765182520030987043 2132213647773780046480565)
      ·
        refine ⟨199895029478791879357553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2132213647773780046480565 199895029478791879357553)
        ·
          refine ⟨149921272109093909518165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199895029478791879357553 149921272109093909518165)
          ·
            refine ⟨878444953764222126083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 149921272109093909518165 878444953764222126083)
            ·
              rfl

theorem cell22_207858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 9].length) (baseStart_207858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207858 prefixEnd_207858 := by exact prefixLift 207858
  have htrace : WordTrace (prefixWord ++ tailWord_207858) baseStart_207858 baseEnd_207858 := by
    simpa [prefixWord, tailWord_207858, baseEnd_207858] using wordTrace_append hprefix tailTrace_207858
  have hstable : (prefixWord ++ tailWord_207858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207858).length < 2 ^ (prefixWord ++ tailWord_207858).sum := by decide
  have hdescent : baseEnd_207858 < baseStart_207858 := by decide
  rcases family_descends (prefixWord ++ tailWord_207858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207958 : List Nat := [5, 2, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_207958 : Nat := 118140960795 + 207958 * 2 ^ 59
def prefixEnd_207958 : Nat := 4983230072969 + 3 ^ 40 * 207958 * 2
def baseEnd_207958 : Nat := 71188273298535064712417

theorem tailTrace_207958 : CollatzResearch.WordTrace tailWord_207958 prefixEnd_207958 71188273298535064712417 := by
  unfold tailWord_207958
  simp only [CollatzResearch.WordTrace]
  refine ⟨474053211288197327744033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5056567587074104829269685 474053211288197327744033)
  ·
    refine ⟨355539908466147995808025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 474053211288197327744033 355539908466147995808025)
    ·
      refine ⟨266654931349610996856019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355539908466147995808025 266654931349610996856019)
      ·
        refine ⟨399982397024416495284029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266654931349610996856019 399982397024416495284029)
        ·
          refine ⟨149993398884156185731511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399982397024416495284029 149993398884156185731511)
          ·
            refine ⟨224990098326234278597267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149993398884156185731511 224990098326234278597267)
            ·
              refine ⟨337485147489351417895901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224990098326234278597267 337485147489351417895901)
              ·
                refine ⟨126556930308506781710963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337485147489351417895901 126556930308506781710963)
                ·
                  refine ⟨189835395462760172566445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126556930308506781710963 189835395462760172566445)
                  ·
                    refine ⟨71188273298535064712417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189835395462760172566445 71188273298535064712417)
                    ·
                      rfl

theorem cell22_207958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_207958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207958 prefixEnd_207958 := by exact prefixLift 207958
  have htrace : WordTrace (prefixWord ++ tailWord_207958) baseStart_207958 baseEnd_207958 := by
    simpa [prefixWord, tailWord_207958, baseEnd_207958] using wordTrace_append hprefix tailTrace_207958
  have hstable : (prefixWord ++ tailWord_207958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207958).length < 2 ^ (prefixWord ++ tailWord_207958).sum := by decide
  have hdescent : baseEnd_207958 < baseStart_207958 := by decide
  rcases family_descends (prefixWord ++ tailWord_207958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207978 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_207978 : Nat := 118140960795 + 207978 * 2 ^ 59
def prefixEnd_207978 : Nat := 4983230072969 + 3 ^ 40 * 207978 * 2
def baseEnd_207978 : Nat := 71195119707261679212355

theorem tailTrace_207978 : CollatzResearch.WordTrace tailWord_207978 prefixEnd_207978 71195119707261679212355 := by
  unfold tailWord_207978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1896395210134675164908147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5057053893692467106421725 1896395210134675164908147)
  ·
    refine ⟨2844592815202012747362221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1896395210134675164908147 2844592815202012747362221)
    ·
      refine ⟨1066722305700754780260833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2844592815202012747362221 1066722305700754780260833)
      ·
        refine ⟨800041729275566085195625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1066722305700754780260833 800041729275566085195625)
        ·
          refine ⟨600031296956674563896719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 800041729275566085195625 600031296956674563896719)
          ·
            refine ⟨900046945435011845845079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600031296956674563896719 900046945435011845845079)
            ·
              refine ⟨1350070418152517768767619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900046945435011845845079 1350070418152517768767619)
              ·
                refine ⟨2025105627228776653151429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350070418152517768767619 2025105627228776653151429)
                ·
                  refine ⟨379707305105395622465893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2025105627228776653151429 379707305105395622465893)
                  ·
                    refine ⟨71195119707261679212355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 379707305105395622465893 71195119707261679212355)
                    ·
                      rfl

theorem cell22_207978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_207978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207978 prefixEnd_207978 := by exact prefixLift 207978
  have htrace : WordTrace (prefixWord ++ tailWord_207978) baseStart_207978 baseEnd_207978 := by
    simpa [prefixWord, tailWord_207978, baseEnd_207978] using wordTrace_append hprefix tailTrace_207978
  have hstable : (prefixWord ++ tailWord_207978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207978).length < 2 ^ (prefixWord ++ tailWord_207978).sum := by decide
  have hdescent : baseEnd_207978 < baseStart_207978 := by decide
  rcases family_descends (prefixWord ++ tailWord_207978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207982 : List Nat := [4, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_207982 : Nat := 118140960795 + 207982 * 2 ^ 59
def prefixEnd_207982 : Nat := 4983230072969 + 3 ^ 40 * 207982 * 2
def baseEnd_207982 : Nat := 23732162996335667370781

theorem tailTrace_207982 : CollatzResearch.WordTrace tailWord_207982 prefixEnd_207982 23732162996335667370781 := by
  unfold tailWord_207982
  simp only [CollatzResearch.WordTrace]
  refine ⟨948215841565526167847275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5057151155016139561852133 948215841565526167847275)
  ·
    refine ⟨1422323762348289251770913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 948215841565526167847275 1422323762348289251770913)
    ·
      refine ⟨1066742821761216938828185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1422323762348289251770913 1066742821761216938828185)
      ·
        refine ⟨800057116320912704121139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1066742821761216938828185 800057116320912704121139)
        ·
          refine ⟨1200085674481369056181709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800057116320912704121139 1200085674481369056181709)
          ·
            refine ⟨450032127930513396068141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1200085674481369056181709 450032127930513396068141)
            ·
              refine ⟨168762047973942523525553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 450032127930513396068141 168762047973942523525553)
              ·
                refine ⟨126571535980456892644165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168762047973942523525553 126571535980456892644165)
                ·
                  refine ⟨23732162996335667370781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126571535980456892644165 23732162996335667370781)
                  ·
                    rfl

theorem cell22_207982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_207982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207982 prefixEnd_207982 := by exact prefixLift 207982
  have htrace : WordTrace (prefixWord ++ tailWord_207982) baseStart_207982 baseEnd_207982 := by
    simpa [prefixWord, tailWord_207982, baseEnd_207982] using wordTrace_append hprefix tailTrace_207982
  have hstable : (prefixWord ++ tailWord_207982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207982).length < 2 ^ (prefixWord ++ tailWord_207982).sum := by decide
  have hdescent : baseEnd_207982 < baseStart_207982 := by decide
  rcases family_descends (prefixWord ++ tailWord_207982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207993 : List Nat := [1, 2, 1, 3, 5, 1, 2, 7]
def baseStart_207993 : Nat := 118140960795 + 207993 * 2 ^ 59
def prefixEnd_207993 : Nat := 4983230072969 + 3 ^ 40 * 207993 * 2
def baseEnd_207993 : Nat := 7911139390422960009701

theorem tailTrace_207993 : CollatzResearch.WordTrace tailWord_207993 prefixEnd_207993 7911139390422960009701 := by
  unfold tailWord_207993
  simp only [CollatzResearch.WordTrace]
  refine ⟨7586127935484358221428633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5057418623656238814285755 7586127935484358221428633)
  ·
    refine ⟨5689595951613268666071475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7586127935484358221428633 5689595951613268666071475)
    ·
      refine ⟨8534393927419902999107213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5689595951613268666071475 8534393927419902999107213)
      ·
        refine ⟨3200397722782463624665205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8534393927419902999107213 3200397722782463624665205)
        ·
          refine ⟨300037286510855964812363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3200397722782463624665205 300037286510855964812363)
          ·
            refine ⟨450055929766283947218545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300037286510855964812363 450055929766283947218545)
            ·
              refine ⟨337541947324712960413909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450055929766283947218545 337541947324712960413909)
              ·
                refine ⟨7911139390422960009701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 337541947324712960413909 7911139390422960009701)
                ·
                  rfl

theorem cell22_207993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 7].length) (baseStart_207993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_207993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_207993 prefixEnd_207993 := by exact prefixLift 207993
  have htrace : WordTrace (prefixWord ++ tailWord_207993) baseStart_207993 baseEnd_207993 := by
    simpa [prefixWord, tailWord_207993, baseEnd_207993] using wordTrace_append hprefix tailTrace_207993
  have hstable : (prefixWord ++ tailWord_207993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207993).length < 2 ^ (prefixWord ++ tailWord_207993).sum := by decide
  have hdescent : baseEnd_207993 < baseStart_207993 := by decide
  rcases family_descends (prefixWord ++ tailWord_207993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208021 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 7]
def baseStart_208021 : Nat := 118140960795 + 208021 * 2 ^ 59
def prefixEnd_208021 : Nat := 4983230072969 + 3 ^ 40 * 208021 * 2
def baseEnd_208021 : Nat := 23736613162007966795741

theorem tailTrace_208021 : CollatzResearch.WordTrace tailWord_208021 prefixEnd_208021 23736613162007966795741 := by
  unfold tailWord_208021
  simp only [CollatzResearch.WordTrace]
  refine ⟨7587149179382919003447917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5058099452921946002298611 7587149179382919003447917)
  ·
    refine ⟨2845180942268594626292969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7587149179382919003447917 2845180942268594626292969)
    ·
      refine ⟨2133885706701445969719727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2845180942268594626292969 2133885706701445969719727)
      ·
        refine ⟨3200828560052168954579591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2133885706701445969719727 3200828560052168954579591)
        ·
          refine ⟨4801242840078253431869387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3200828560052168954579591 4801242840078253431869387)
          ·
            refine ⟨7201864260117380147804081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4801242840078253431869387 7201864260117380147804081)
            ·
              refine ⟨5401398195088035110853061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7201864260117380147804081 5401398195088035110853061)
              ·
                refine ⟨1012762161579006583284949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5401398195088035110853061 1012762161579006583284949)
                ·
                  refine ⟨23736613162007966795741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1012762161579006583284949 23736613162007966795741)
                  ·
                    rfl

theorem cell22_208021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_208021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208021 prefixEnd_208021 := by exact prefixLift 208021
  have htrace : WordTrace (prefixWord ++ tailWord_208021) baseStart_208021 baseEnd_208021 := by
    simpa [prefixWord, tailWord_208021, baseEnd_208021] using wordTrace_append hprefix tailTrace_208021
  have hstable : (prefixWord ++ tailWord_208021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208021).length < 2 ^ (prefixWord ++ tailWord_208021).sum := by decide
  have hdescent : baseEnd_208021 < baseStart_208021 := by decide
  rcases family_descends (prefixWord ++ tailWord_208021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208100 : List Nat := [2, 3, 1, 1, 1, 2, 4, 4, 4]
def baseStart_208100 : Nat := 118140960795 + 208100 * 2 ^ 59
def prefixEnd_208100 : Nat := 4983230072969 + 3 ^ 40 * 208100 * 2
def baseEnd_208100 : Nat := 23745627600164675887327

theorem tailTrace_208100 : CollatzResearch.WordTrace tailWord_208100 prefixEnd_208100 23745627600164675887327 := by
  unfold tailWord_208100
  simp only [CollatzResearch.WordTrace]
  refine ⟨3795015273048357747786877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5060020364064476997049169 3795015273048357747786877)
  ·
    refine ⟨1423130727393134155420079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3795015273048357747786877 1423130727393134155420079)
    ·
      refine ⟨2134696091089701233130119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1423130727393134155420079 2134696091089701233130119)
      ·
        refine ⟨3202044136634551849695179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134696091089701233130119 3202044136634551849695179)
        ·
          refine ⟨4803066204951827774542769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3202044136634551849695179 4803066204951827774542769)
          ·
            refine ⟨3602299653713870830907077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4803066204951827774542769 3602299653713870830907077)
            ·
              refine ⟨675431185071350780795077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3602299653713870830907077 675431185071350780795077)
              ·
                refine ⟨126643347200878271399077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 675431185071350780795077 126643347200878271399077)
                ·
                  refine ⟨23745627600164675887327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126643347200878271399077 23745627600164675887327)
                  ·
                    rfl

theorem cell22_208100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_208100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208100 prefixEnd_208100 := by exact prefixLift 208100
  have htrace : WordTrace (prefixWord ++ tailWord_208100) baseStart_208100 baseEnd_208100 := by
    simpa [prefixWord, tailWord_208100, baseEnd_208100] using wordTrace_append hprefix tailTrace_208100
  have hstable : (prefixWord ++ tailWord_208100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208100).length < 2 ^ (prefixWord ++ tailWord_208100).sum := by decide
  have hdescent : baseEnd_208100 < baseStart_208100 := by decide
  rcases family_descends (prefixWord ++ tailWord_208100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208115 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 1, 5]
def baseStart_208115 : Nat := 118140960795 + 208115 * 2 ^ 59
def prefixEnd_208115 : Nat := 4983230072969 + 3 ^ 40 * 208115 * 2
def baseEnd_208115 : Nat := 71242017607038988536935

theorem tailTrace_208115 : CollatzResearch.WordTrace tailWord_208115 prefixEnd_208115 71242017607038988536935 := by
  unfold tailWord_208115
  simp only [CollatzResearch.WordTrace]
  refine ⟨7590577641042373057369799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5060385094028248704913199 7590577641042373057369799)
  ·
    refine ⟨11385866461563559586054699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7590577641042373057369799 11385866461563559586054699)
    ·
      refine ⟨17078799692345339379082049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11385866461563559586054699 17078799692345339379082049)
      ·
        refine ⟨12809099769259004534311537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17078799692345339379082049 12809099769259004534311537)
        ·
          refine ⟨9606824826944253400733653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12809099769259004534311537 9606824826944253400733653)
          ·
            refine ⟨225159956881505939079695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 9606824826944253400733653 225159956881505939079695)
            ·
              refine ⟨337739935322258908619543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225159956881505939079695 337739935322258908619543)
              ·
                refine ⟨506609902983388362929315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337739935322258908619543 506609902983388362929315)
                ·
                  refine ⟨759914854475082544393973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506609902983388362929315 759914854475082544393973)
                  ·
                    refine ⟨71242017607038988536935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 759914854475082544393973 71242017607038988536935)
                    ·
                      rfl

theorem cell22_208115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 5].length) (baseStart_208115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208115 prefixEnd_208115 := by exact prefixLift 208115
  have htrace : WordTrace (prefixWord ++ tailWord_208115) baseStart_208115 baseEnd_208115 := by
    simpa [prefixWord, tailWord_208115, baseEnd_208115] using wordTrace_append hprefix tailTrace_208115
  have hstable : (prefixWord ++ tailWord_208115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208115).length < 2 ^ (prefixWord ++ tailWord_208115).sum := by decide
  have hdescent : baseEnd_208115 < baseStart_208115 := by decide
  rcases family_descends (prefixWord ++ tailWord_208115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208250 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 6, 3]
def baseStart_208250 : Nat := 118140960795 + 208250 * 2 ^ 59
def prefixEnd_208250 : Nat := 4983230072969 + 3 ^ 40 * 208250 * 2
def baseEnd_208250 : Nat := 71288230865943636411521

theorem tailTrace_208250 : CollatzResearch.WordTrace tailWord_208250 prefixEnd_208250 71288230865943636411521 := by
  unfold tailWord_208250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1898875373888322778383551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5063667663702194075689469 1898875373888322778383551)
  ·
    refine ⟨2848313060832484167575327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1898875373888322778383551 2848313060832484167575327)
    ·
      refine ⟨4272469591248726251362991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2848313060832484167575327 4272469591248726251362991)
      ·
        refine ⟨6408704386873089377044487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4272469591248726251362991 6408704386873089377044487)
        ·
          refine ⟨9613056580309634065566731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6408704386873089377044487 9613056580309634065566731)
          ·
            refine ⟨14419584870464451098350097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9613056580309634065566731 14419584870464451098350097)
            ·
              refine ⟨10814688652848338323762573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14419584870464451098350097 10814688652848338323762573)
              ·
                refine ⟨4055508244818126871410965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10814688652848338323762573 4055508244818126871410965)
                ·
                  refine ⟨190101948975849697097389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4055508244818126871410965 190101948975849697097389)
                  ·
                    refine ⟨71288230865943636411521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190101948975849697097389 71288230865943636411521)
                    ·
                      rfl

theorem cell22_208250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_208250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208250 prefixEnd_208250 := by exact prefixLift 208250
  have htrace : WordTrace (prefixWord ++ tailWord_208250) baseStart_208250 baseEnd_208250 := by
    simpa [prefixWord, tailWord_208250, baseEnd_208250] using wordTrace_append hprefix tailTrace_208250
  have hstable : (prefixWord ++ tailWord_208250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208250).length < 2 ^ (prefixWord ++ tailWord_208250).sum := by decide
  have hdescent : baseEnd_208250 < baseStart_208250 := by decide
  rcases family_descends (prefixWord ++ tailWord_208250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208252 : List Nat := [2, 2, 2, 1, 1, 1, 6, 3, 4]
def baseStart_208252 : Nat := 118140960795 + 208252 * 2 ^ 59
def prefixEnd_208252 : Nat := 4983230072969 + 3 ^ 40 * 208252 * 2
def baseEnd_208252 : Nat := 23762971835605432620505

theorem tailTrace_208252 : CollatzResearch.WordTrace tailWord_208252 prefixEnd_208252 23762971835605432620505 := by
  unfold tailWord_208252
  simp only [CollatzResearch.WordTrace]
  refine ⟨3797787220773022727553505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5063716294364030303404673 3797787220773022727553505)
  ·
    refine ⟨2848340415579767045665129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3797787220773022727553505 2848340415579767045665129)
    ·
      refine ⟨2136255311684825284248847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2848340415579767045665129 2136255311684825284248847)
      ·
        refine ⟨3204382967527237926373271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136255311684825284248847 3204382967527237926373271)
        ·
          refine ⟨4806574451290856889559907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3204382967527237926373271 4806574451290856889559907)
          ·
            refine ⟨7209861676936285334339861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806574451290856889559907 7209861676936285334339861)
            ·
              refine ⟨337962266106388375047181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7209861676936285334339861 337962266106388375047181)
              ·
                refine ⟨126735849789895640642693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337962266106388375047181 126735849789895640642693)
                ·
                  refine ⟨23762971835605432620505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126735849789895640642693 23762971835605432620505)
                  ·
                    rfl

theorem cell22_208252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_208252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208252 prefixEnd_208252 := by exact prefixLift 208252
  have htrace : WordTrace (prefixWord ++ tailWord_208252) baseStart_208252 baseEnd_208252 := by
    simpa [prefixWord, tailWord_208252, baseEnd_208252] using wordTrace_append hprefix tailTrace_208252
  have hstable : (prefixWord ++ tailWord_208252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208252).length < 2 ^ (prefixWord ++ tailWord_208252).sum := by decide
  have hdescent : baseEnd_208252 < baseStart_208252 := by decide
  rcases family_descends (prefixWord ++ tailWord_208252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208295 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 2, 7]
def baseStart_208295 : Nat := 118140960795 + 208295 * 2 ^ 59
def prefixEnd_208295 : Nat := 4983230072969 + 3 ^ 40 * 208295 * 2
def baseEnd_208295 : Nat := 71303635285578519036383

theorem tailTrace_208295 : CollatzResearch.WordTrace tailWord_208295 prefixEnd_208295 71303635285578519036383 := by
  unfold tailWord_208295
  simp only [CollatzResearch.WordTrace]
  refine ⟨7597142780390263798922339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5064761853593509199281559 7597142780390263798922339)
  ·
    refine ⟨11395714170585395698383509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7597142780390263798922339 11395714170585395698383509)
    ·
      refine ⟨534174101746190423361727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11395714170585395698383509 534174101746190423361727)
      ·
        refine ⟨801261152619285635042591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534174101746190423361727 801261152619285635042591)
        ·
          refine ⟨1201891728928928452563887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801261152619285635042591 1201891728928928452563887)
          ·
            refine ⟨1802837593393392678845831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201891728928928452563887 1802837593393392678845831)
            ·
              refine ⟨2704256390090089018268747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802837593393392678845831 2704256390090089018268747)
              ·
                refine ⟨4056384585135133527403121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2704256390090089018268747 4056384585135133527403121)
                ·
                  refine ⟨3042288438851350145552341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4056384585135133527403121 3042288438851350145552341)
                  ·
                    refine ⟨71303635285578519036383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3042288438851350145552341 71303635285578519036383)
                    ·
                      rfl

theorem cell22_208295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_208295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208295 prefixEnd_208295 := by exact prefixLift 208295
  have htrace : WordTrace (prefixWord ++ tailWord_208295) baseStart_208295 baseEnd_208295 := by
    simpa [prefixWord, tailWord_208295, baseEnd_208295] using wordTrace_append hprefix tailTrace_208295
  have hstable : (prefixWord ++ tailWord_208295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208295).length < 2 ^ (prefixWord ++ tailWord_208295).sum := by decide
  have hdescent : baseEnd_208295 < baseStart_208295 := by decide
  rcases family_descends (prefixWord ++ tailWord_208295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208415 : List Nat := [1, 1, 2, 4, 1, 1, 2, 10]
def baseStart_208415 : Nat := 118140960795 + 208415 * 2 ^ 59
def prefixEnd_208415 : Nat := 4983230072969 + 3 ^ 40 * 208415 * 2
def baseEnd_208415 : Nat := 7927190415326467337335

theorem tailTrace_208415 : CollatzResearch.WordTrace tailWord_208415 prefixEnd_208415 7927190415326467337335 := by
  unfold tailWord_208415
  simp only [CollatzResearch.WordTrace]
  refine ⟨7601519539955524293290699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5067679693303682862193799 7601519539955524293290699)
  ·
    refine ⟨11402279309933286439936049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7601519539955524293290699 11402279309933286439936049)
    ·
      refine ⟨8551709482449964829952037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11402279309933286439936049 8551709482449964829952037)
      ·
        refine ⟨1603445527959368405616007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8551709482449964829952037 1603445527959368405616007)
        ·
          refine ⟨2405168291939052608424011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1603445527959368405616007 2405168291939052608424011)
          ·
            refine ⟨3607752437908578912636017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405168291939052608424011 3607752437908578912636017)
            ·
              refine ⟨2705814328431434184477013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3607752437908578912636017 2705814328431434184477013)
              ·
                refine ⟨7927190415326467337335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2705814328431434184477013 7927190415326467337335)
                ·
                  rfl

theorem cell22_208415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 10].length) (baseStart_208415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208415 prefixEnd_208415 := by exact prefixLift 208415
  have htrace : WordTrace (prefixWord ++ tailWord_208415) baseStart_208415 baseEnd_208415 := by
    simpa [prefixWord, tailWord_208415, baseEnd_208415] using wordTrace_append hprefix tailTrace_208415
  have hstable : (prefixWord ++ tailWord_208415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208415).length < 2 ^ (prefixWord ++ tailWord_208415).sum := by decide
  have hdescent : baseEnd_208415 < baseStart_208415 := by decide
  rcases family_descends (prefixWord ++ tailWord_208415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208417 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 1, 6]
def baseStart_208417 : Nat := 118140960795 + 208417 * 2 ^ 59
def prefixEnd_208417 : Nat := 4983230072969 + 3 ^ 40 * 208417 * 2
def baseEnd_208417 : Nat := 71345398378810867486009

theorem tailTrace_208417 : CollatzResearch.WordTrace tailWord_208417 prefixEnd_208417 71345398378810867486009 := by
  unfold tailWord_208417
  simp only [CollatzResearch.WordTrace]
  refine ⟨7601592485948278634863505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5067728323965519089909003 7601592485948278634863505)
  ·
    refine ⟨5701194364461208976147629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7601592485948278634863505 5701194364461208976147629)
    ·
      refine ⟨2137947886672953366055361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5701194364461208976147629 2137947886672953366055361)
      ·
        refine ⟨1603460915004715024541521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2137947886672953366055361 1603460915004715024541521)
        ·
          refine ⟨1202595686253536268406141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1603460915004715024541521 1202595686253536268406141)
          ·
            refine ⟨450973382345076100652303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1202595686253536268406141 450973382345076100652303)
            ·
              refine ⟨676460073517614150978455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450973382345076100652303 676460073517614150978455)
              ·
                refine ⟨1014690110276421226467683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676460073517614150978455 1014690110276421226467683)
                ·
                  refine ⟨1522035165414631839701525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014690110276421226467683 1522035165414631839701525)
                  ·
                    refine ⟨71345398378810867486009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1522035165414631839701525 71345398378810867486009)
                    ·
                      rfl

theorem cell22_208417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_208417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208417 prefixEnd_208417 := by exact prefixLift 208417
  have htrace : WordTrace (prefixWord ++ tailWord_208417) baseStart_208417 baseEnd_208417 := by
    simpa [prefixWord, tailWord_208417, baseEnd_208417] using wordTrace_append hprefix tailTrace_208417
  have hstable : (prefixWord ++ tailWord_208417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208417).length < 2 ^ (prefixWord ++ tailWord_208417).sum := by decide
  have hdescent : baseEnd_208417 < baseStart_208417 := by decide
  rcases family_descends (prefixWord ++ tailWord_208417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208507 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 3, 4]
def baseStart_208507 : Nat := 118140960795 + 208507 * 2 ^ 59
def prefixEnd_208507 : Nat := 4983230072969 + 3 ^ 40 * 208507 * 2
def baseEnd_208507 : Nat := 71376207218080632735733

theorem tailTrace_208507 : CollatzResearch.WordTrace tailWord_208507 prefixEnd_208507 71376207218080632735733 := by
  unfold tailWord_208507
  simp only [CollatzResearch.WordTrace]
  refine ⟨7604875055622224005639775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5069916703748149337093183 7604875055622224005639775)
  ·
    refine ⟨11407312583433336008459663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7604875055622224005639775 11407312583433336008459663)
    ·
      refine ⟨17110968875150004012689495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11407312583433336008459663 17110968875150004012689495)
      ·
        refine ⟨25666453312725006019034243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17110968875150004012689495 25666453312725006019034243)
        ·
          refine ⟨38499679969087509028551365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25666453312725006019034243 38499679969087509028551365)
          ·
            refine ⟨7218689994203907942853381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38499679969087509028551365 7218689994203907942853381)
            ·
              refine ⟨1353504373913232739285009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7218689994203907942853381 1353504373913232739285009)
              ·
                refine ⟨1015128280434924554463757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353504373913232739285009 1015128280434924554463757)
                ·
                  refine ⟨380673105163096707923909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015128280434924554463757 380673105163096707923909)
                  ·
                    refine ⟨71376207218080632735733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 380673105163096707923909 71376207218080632735733)
                    ·
                      rfl

theorem cell22_208507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 4].length) (baseStart_208507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208507 prefixEnd_208507 := by exact prefixLift 208507
  have htrace : WordTrace (prefixWord ++ tailWord_208507) baseStart_208507 baseEnd_208507 := by
    simpa [prefixWord, tailWord_208507, baseEnd_208507] using wordTrace_append hprefix tailTrace_208507
  have hstable : (prefixWord ++ tailWord_208507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208507).length < 2 ^ (prefixWord ++ tailWord_208507).sum := by decide
  have hdescent : baseEnd_208507 < baseStart_208507 := by decide
  rcases family_descends (prefixWord ++ tailWord_208507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208584 : List Nat := [2, 1, 3, 1, 2, 2, 5, 6]
def baseStart_208584 : Nat := 118140960795 + 208584 * 2 ^ 59
def prefixEnd_208584 : Nat := 4983230072969 + 3 ^ 40 * 208584 * 2
def baseEnd_208584 : Nat := 7933618432408677617833

theorem tailTrace_208584 : CollatzResearch.WordTrace tailWord_208584 prefixEnd_208584 7933618432408677617833 := by
  unfold tailWord_208584
  simp only [CollatzResearch.WordTrace]
  refine ⟨3803841738171633078096403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5071788984228844104128537 3803841738171633078096403)
  ·
    refine ⟨5705762607257449617144605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3803841738171633078096403 5705762607257449617144605)
    ·
      refine ⟨2139660977721543606429227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5705762607257449617144605 2139660977721543606429227)
      ·
        refine ⟨3209491466582315409643841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139660977721543606429227 3209491466582315409643841)
        ·
          refine ⟨2407118599936736557232881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3209491466582315409643841 2407118599936736557232881)
          ·
            refine ⟨1805338949952552417924661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2407118599936736557232881 1805338949952552417924661)
            ·
              refine ⟨169250526558051789180437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1805338949952552417924661 169250526558051789180437)
              ·
                refine ⟨7933618432408677617833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 169250526558051789180437 7933618432408677617833)
                ·
                  rfl

theorem cell22_208584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 6].length) (baseStart_208584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208584 prefixEnd_208584 := by exact prefixLift 208584
  have htrace : WordTrace (prefixWord ++ tailWord_208584) baseStart_208584 baseEnd_208584 := by
    simpa [prefixWord, tailWord_208584, baseEnd_208584] using wordTrace_append hprefix tailTrace_208584
  have hstable : (prefixWord ++ tailWord_208584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208584).length < 2 ^ (prefixWord ++ tailWord_208584).sum := by decide
  have hdescent : baseEnd_208584 < baseStart_208584 := by decide
  rcases family_descends (prefixWord ++ tailWord_208584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208599 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 5, 3]
def baseStart_208599 : Nat := 118140960795 + 208599 * 2 ^ 59
def prefixEnd_208599 : Nat := 4983230072969 + 3 ^ 40 * 208599 * 2
def baseEnd_208599 : Nat := 71407700698223059435451

theorem tailTrace_208599 : CollatzResearch.WordTrace tailWord_208599 prefixEnd_208599 71407700698223059435451 := by
  unfold tailWord_208599
  simp only [CollatzResearch.WordTrace]
  refine ⟨7608230571288923717988851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5072153714192615811992567 7608230571288923717988851)
  ·
    refine ⟨11412345856933385576983277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7608230571288923717988851 11412345856933385576983277)
    ·
      refine ⟨4279629696350019591368729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11412345856933385576983277 4279629696350019591368729)
      ·
        refine ⟨3209722272262514693526547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4279629696350019591368729 3209722272262514693526547)
        ·
          refine ⟨4814583408393772040289821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3209722272262514693526547 4814583408393772040289821)
          ·
            refine ⟨1805468778147664515108683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4814583408393772040289821 1805468778147664515108683)
            ·
              refine ⟨2708203167221496772663025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1805468778147664515108683 2708203167221496772663025)
              ·
                refine ⟨2031152375416122579497269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2708203167221496772663025 2031152375416122579497269)
                ·
                  refine ⟨190420535195261491827869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2031152375416122579497269 190420535195261491827869)
                  ·
                    refine ⟨71407700698223059435451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190420535195261491827869 71407700698223059435451)
                    ·
                      rfl

theorem cell22_208599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_208599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208599 prefixEnd_208599 := by exact prefixLift 208599
  have htrace : WordTrace (prefixWord ++ tailWord_208599) baseStart_208599 baseEnd_208599 := by
    simpa [prefixWord, tailWord_208599, baseEnd_208599] using wordTrace_append hprefix tailTrace_208599
  have hstable : (prefixWord ++ tailWord_208599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208599).length < 2 ^ (prefixWord ++ tailWord_208599).sum := by decide
  have hdescent : baseEnd_208599 < baseStart_208599 := by decide
  rcases family_descends (prefixWord ++ tailWord_208599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208616 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 3, 3]
def baseStart_208616 : Nat := 118140960795 + 208616 * 2 ^ 59
def prefixEnd_208616 : Nat := 4983230072969 + 3 ^ 40 * 208616 * 2
def baseEnd_208616 : Nat := 71413520145640681760399

theorem tailTrace_208616 : CollatzResearch.WordTrace tailWord_208616 prefixEnd_208616 71413520145640681760399 := by
  unfold tailWord_208616
  simp only [CollatzResearch.WordTrace]
  refine ⟨3804425306113667810678851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5072567074818223747571801 3804425306113667810678851)
  ·
    refine ⟨5706637959170501716018277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3804425306113667810678851 5706637959170501716018277)
    ·
      refine ⟨1069994617344469071753427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5706637959170501716018277 1069994617344469071753427)
      ·
        refine ⟨1604991926016703607630141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1069994617344469071753427 1604991926016703607630141)
        ·
          refine ⟨601871972256263852861303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1604991926016703607630141 601871972256263852861303)
          ·
            refine ⟨902807958384395779291955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601871972256263852861303 902807958384395779291955)
            ·
              refine ⟨1354211937576593668937933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902807958384395779291955 1354211937576593668937933)
              ·
                refine ⟨507829476591222625851725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1354211937576593668937933 507829476591222625851725)
                ·
                  refine ⟨190436053721708484694397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507829476591222625851725 190436053721708484694397)
                  ·
                    refine ⟨71413520145640681760399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190436053721708484694397 71413520145640681760399)
                    ·
                      rfl

theorem cell22_208616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_208616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208616 prefixEnd_208616 := by exact prefixLift 208616
  have htrace : WordTrace (prefixWord ++ tailWord_208616) baseStart_208616 baseEnd_208616 := by
    simpa [prefixWord, tailWord_208616, baseEnd_208616] using wordTrace_append hprefix tailTrace_208616
  have hstable : (prefixWord ++ tailWord_208616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208616).length < 2 ^ (prefixWord ++ tailWord_208616).sum := by decide
  have hdescent : baseEnd_208616 < baseStart_208616 := by decide
  rcases family_descends (prefixWord ++ tailWord_208616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208650 : List Nat := [3, 1, 2, 2, 1, 5, 1, 3, 1, 3]
def baseStart_208650 : Nat := 118140960795 + 208650 * 2 ^ 59
def prefixEnd_208650 : Nat := 4983230072969 + 3 ^ 40 * 208650 * 2
def baseEnd_208650 : Nat := 71425159040475926410295

theorem tailTrace_208650 : CollatzResearch.WordTrace tailWord_208650 prefixEnd_208650 71425159040475926410295 := by
  unfold tailWord_208650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1902522673526039857023851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5073393796069439618730269 1902522673526039857023851)
  ·
    refine ⟨2853784010289059785535777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1902522673526039857023851 2853784010289059785535777)
    ·
      refine ⟨2140338007716794839151833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2853784010289059785535777 2140338007716794839151833)
      ·
        refine ⟨1605253505787596129363875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2140338007716794839151833 1605253505787596129363875)
        ·
          refine ⟨2407880258681394194045813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605253505787596129363875 2407880258681394194045813)
          ·
            refine ⟨225738774251380705691795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2407880258681394194045813 225738774251380705691795)
            ·
              refine ⟨338608161377071058537693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225738774251380705691795 338608161377071058537693)
              ·
                refine ⟨126978060516401646951635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338608161377071058537693 126978060516401646951635)
                ·
                  refine ⟨190467090774602470427453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126978060516401646951635 190467090774602470427453)
                  ·
                    refine ⟨71425159040475926410295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190467090774602470427453 71425159040475926410295)
                    ·
                      rfl

theorem cell22_208650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_208650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208650 prefixEnd_208650 := by exact prefixLift 208650
  have htrace : WordTrace (prefixWord ++ tailWord_208650) baseStart_208650 baseEnd_208650 := by
    simpa [prefixWord, tailWord_208650, baseEnd_208650] using wordTrace_append hprefix tailTrace_208650
  have hstable : (prefixWord ++ tailWord_208650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208650).length < 2 ^ (prefixWord ++ tailWord_208650).sum := by decide
  have hdescent : baseEnd_208650 < baseStart_208650 := by decide
  rcases family_descends (prefixWord ++ tailWord_208650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208721 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 2, 4]
def baseStart_208721 : Nat := 118140960795 + 208721 * 2 ^ 59
def prefixEnd_208721 : Nat := 4983230072969 + 3 ^ 40 * 208721 * 2
def baseEnd_208721 : Nat := 71449463791455407885077

theorem tailTrace_208721 : CollatzResearch.WordTrace tailWord_208721 prefixEnd_208721 71449463791455407885077 := by
  unfold tailWord_208721
  simp only [CollatzResearch.WordTrace]
  refine ⟨7612680276846938553930017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5075120184564625702620011 7612680276846938553930017)
  ·
    refine ⟨5709510207635203915447513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7612680276846938553930017 5709510207635203915447513)
    ·
      refine ⟨4282132655726402936585635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5709510207635203915447513 4282132655726402936585635)
      ·
        refine ⟨6423198983589604404878453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4282132655726402936585635 6423198983589604404878453)
        ·
          refine ⟨602174904711525412957355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6423198983589604404878453 602174904711525412957355)
          ·
            refine ⟨903262357067288119436033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602174904711525412957355 903262357067288119436033)
            ·
              refine ⟨677446767800466089577025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 903262357067288119436033 677446767800466089577025)
              ·
                refine ⟨508085075850349567182769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677446767800466089577025 508085075850349567182769)
                ·
                  refine ⟨381063806887762175387077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508085075850349567182769 381063806887762175387077)
                  ·
                    refine ⟨71449463791455407885077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 381063806887762175387077 71449463791455407885077)
                    ·
                      rfl

theorem cell22_208721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_208721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208721 prefixEnd_208721 := by exact prefixLift 208721
  have htrace : WordTrace (prefixWord ++ tailWord_208721) baseStart_208721 baseEnd_208721 := by
    simpa [prefixWord, tailWord_208721, baseEnd_208721] using wordTrace_append hprefix tailTrace_208721
  have hstable : (prefixWord ++ tailWord_208721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208721).length < 2 ^ (prefixWord ++ tailWord_208721).sum := by decide
  have hdescent : baseEnd_208721 < baseStart_208721 := by decide
  rcases family_descends (prefixWord ++ tailWord_208721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208725 : List Nat := [1, 3, 2, 2, 2, 4, 2, 2, 4]
def baseStart_208725 : Nat := 118140960795 + 208725 * 2 ^ 59
def prefixEnd_208725 : Nat := 4983230072969 + 3 ^ 40 * 208725 * 2
def baseEnd_208725 : Nat := 23816944357733576928355

theorem tailTrace_208725 : CollatzResearch.WordTrace tailWord_208725 prefixEnd_208725 23816944357733576928355 := by
  unfold tailWord_208725
  simp only [CollatzResearch.WordTrace]
  refine ⟨7612826168832447237075629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5075217445888298158050419 7612826168832447237075629)
  ·
    refine ⟨2854809813312167713903361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7612826168832447237075629 2854809813312167713903361)
    ·
      refine ⟨2141107359984125785427521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2854809813312167713903361 2141107359984125785427521)
      ·
        refine ⟨1605830519988094339070641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2141107359984125785427521 1605830519988094339070641)
        ·
          refine ⟨1204372889991070754302981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1605830519988094339070641 1204372889991070754302981)
          ·
            refine ⟨225819916873325766431809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1204372889991070754302981 225819916873325766431809)
            ·
              refine ⟨169364937654994324823857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225819916873325766431809 169364937654994324823857)
              ·
                refine ⟨127023703241245743617893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169364937654994324823857 127023703241245743617893)
                ·
                  refine ⟨23816944357733576928355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127023703241245743617893 23816944357733576928355)
                  ·
                    rfl

theorem cell22_208725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_208725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208725 prefixEnd_208725 := by exact prefixLift 208725
  have htrace : WordTrace (prefixWord ++ tailWord_208725) baseStart_208725 baseEnd_208725 := by
    simpa [prefixWord, tailWord_208725, baseEnd_208725] using wordTrace_append hprefix tailTrace_208725
  have hstable : (prefixWord ++ tailWord_208725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208725).length < 2 ^ (prefixWord ++ tailWord_208725).sum := by decide
  have hdescent : baseEnd_208725 < baseStart_208725 := by decide
  rcases family_descends (prefixWord ++ tailWord_208725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208736 : List Nat := [2, 1, 1, 3, 3, 4, 1, 7]
def baseStart_208736 : Nat := 118140960795 + 208736 * 2 ^ 59
def prefixEnd_208736 : Nat := 4983230072969 + 3 ^ 40 * 208736 * 2
def baseEnd_208736 : Nat := 7939399844222263195559

theorem tailTrace_208736 : CollatzResearch.WordTrace tailWord_208736 prefixEnd_208736 7939399844222263195559 := by
  unfold tailWord_208736
  simp only [CollatzResearch.WordTrace]
  refine ⟨3806613685896298057863031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5075484914528397410484041 3806613685896298057863031)
  ·
    refine ⟨5709920528844447086794547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3806613685896298057863031 5709920528844447086794547)
    ·
      refine ⟨8564880793266670630191821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5709920528844447086794547 8564880793266670630191821)
      ·
        refine ⟨3211830297475001486321933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8564880793266670630191821 3211830297475001486321933)
        ·
          refine ⟨1204436361553125557370725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3211830297475001486321933 1204436361553125557370725)
          ·
            refine ⟨225831817791211042007011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1204436361553125557370725 225831817791211042007011)
            ·
              refine ⟨338747726686816563010517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225831817791211042007011 338747726686816563010517)
              ·
                refine ⟨7939399844222263195559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 338747726686816563010517 7939399844222263195559)
                ·
                  rfl

theorem cell22_208736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 7].length) (baseStart_208736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208736 prefixEnd_208736 := by exact prefixLift 208736
  have htrace : WordTrace (prefixWord ++ tailWord_208736) baseStart_208736 baseEnd_208736 := by
    simpa [prefixWord, tailWord_208736, baseEnd_208736] using wordTrace_append hprefix tailTrace_208736
  have hstable : (prefixWord ++ tailWord_208736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208736).length < 2 ^ (prefixWord ++ tailWord_208736).sum := by decide
  have hdescent : baseEnd_208736 < baseStart_208736 := by decide
  rcases family_descends (prefixWord ++ tailWord_208736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208809 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 8]
def baseStart_208809 : Nat := 118140960795 + 208809 * 2 ^ 59
def prefixEnd_208809 : Nat := 4983230072969 + 3 ^ 40 * 208809 * 2
def baseEnd_208809 : Nat := 23826529329950837228269

theorem tailTrace_208809 : CollatzResearch.WordTrace tailWord_208809 prefixEnd_208809 23826529329950837228269 := by
  unfold tailWord_208809
  simp only [CollatzResearch.WordTrace]
  refine ⟨7615889900528129583133481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5077259933685419722088987 7615889900528129583133481)
  ·
    refine ⟨5711917425396097187350111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7615889900528129583133481 5711917425396097187350111)
    ·
      refine ⟨8567876138094145781025167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5711917425396097187350111 8567876138094145781025167)
      ·
        refine ⟨12851814207141218671537751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8567876138094145781025167 12851814207141218671537751)
        ·
          refine ⟨19277721310711828007306627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12851814207141218671537751 19277721310711828007306627)
          ·
            refine ⟨28916581966067742010959941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19277721310711828007306627 28916581966067742010959941)
            ·
              refine ⟨5421859118637701627054989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28916581966067742010959941 5421859118637701627054989)
              ·
                refine ⟨2033197169489138110145621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5421859118637701627054989 2033197169489138110145621)
                ·
                  refine ⟨23826529329950837228269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2033197169489138110145621 23826529329950837228269)
                  ·
                    rfl

theorem cell22_208809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_208809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208809 prefixEnd_208809 := by exact prefixLift 208809
  have htrace : WordTrace (prefixWord ++ tailWord_208809) baseStart_208809 baseEnd_208809 := by
    simpa [prefixWord, tailWord_208809, baseEnd_208809] using wordTrace_append hprefix tailTrace_208809
  have hstable : (prefixWord ++ tailWord_208809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208809).length < 2 ^ (prefixWord ++ tailWord_208809).sum := by decide
  have hdescent : baseEnd_208809 < baseStart_208809 := by decide
  rcases family_descends (prefixWord ++ tailWord_208809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208856 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 4, 4]
def baseStart_208856 : Nat := 118140960795 + 208856 * 2 ^ 59
def prefixEnd_208856 : Nat := 4983230072969 + 3 ^ 40 * 208856 * 2
def baseEnd_208856 : Nat := 71495677050360055759663

theorem tailTrace_208856 : CollatzResearch.WordTrace tailWord_208856 prefixEnd_208856 71495677050360055759663 := by
  unfold tailWord_208856
  simp only [CollatzResearch.WordTrace]
  refine ⟨3808802065678928305047211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5078402754238571073396281 3808802065678928305047211)
  ·
    refine ⟨5713203098518392457570817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3808802065678928305047211 5713203098518392457570817)
    ·
      refine ⟨4284902323888794343178113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5713203098518392457570817 4284902323888794343178113)
      ·
        refine ⟨3213676742916595757383585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4284902323888794343178113 3213676742916595757383585)
        ·
          refine ⟨2410257557187446818037689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3213676742916595757383585 2410257557187446818037689)
          ·
            refine ⟨1807693167890585113528267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2410257557187446818037689 1807693167890585113528267)
            ·
              refine ⟨2711539751835877670292401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1807693167890585113528267 2711539751835877670292401)
              ·
                refine ⟨2033654813876908252719301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2711539751835877670292401 2033654813876908252719301)
                ·
                  refine ⟨381310277601920297384869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2033654813876908252719301 381310277601920297384869)
                  ·
                    refine ⟨71495677050360055759663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 381310277601920297384869 71495677050360055759663)
                    ·
                      rfl

theorem cell22_208856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_208856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208856 prefixEnd_208856 := by exact prefixLift 208856
  have htrace : WordTrace (prefixWord ++ tailWord_208856) baseStart_208856 baseEnd_208856 := by
    simpa [prefixWord, tailWord_208856, baseEnd_208856] using wordTrace_append hprefix tailTrace_208856
  have hstable : (prefixWord ++ tailWord_208856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208856).length < 2 ^ (prefixWord ++ tailWord_208856).sum := by decide
  have hdescent : baseEnd_208856 < baseStart_208856 := by decide
  rcases family_descends (prefixWord ++ tailWord_208856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208894 : List Nat := [4, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_208894 : Nat := 118140960795 + 208894 * 2 ^ 59
def prefixEnd_208894 : Nat := 4983230072969 + 3 ^ 40 * 208894 * 2
def baseEnd_208894 : Nat := 23836228408980207769849

theorem tailTrace_208894 : CollatzResearch.WordTrace tailWord_208894 prefixEnd_208894 23836228408980207769849 := by
  unfold tailWord_208894
  simp only [CollatzResearch.WordTrace]
  refine ⟨952373763152523637497217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5079326736813459399985157 952373763152523637497217)
  ·
    refine ⟨714280322364392728122913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 952373763152523637497217 714280322364392728122913)
    ·
      refine ⟨535710241773294546092185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 714280322364392728122913 535710241773294546092185)
      ·
        refine ⟨401782681329970909569139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535710241773294546092185 401782681329970909569139)
        ·
          refine ⟨602674021994956364353709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401782681329970909569139 602674021994956364353709)
          ·
            refine ⟨226002758248108636632641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 602674021994956364353709 226002758248108636632641)
            ·
              refine ⟨169502068686081477474481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226002758248108636632641 169502068686081477474481)
              ·
                refine ⟨127126551514561108105861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169502068686081477474481 127126551514561108105861)
                ·
                  refine ⟨23836228408980207769849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127126551514561108105861 23836228408980207769849)
                  ·
                    rfl

theorem cell22_208894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_208894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208894 prefixEnd_208894 := by exact prefixLift 208894
  have htrace : WordTrace (prefixWord ++ tailWord_208894) baseStart_208894 baseEnd_208894 := by
    simpa [prefixWord, tailWord_208894, baseEnd_208894] using wordTrace_append hprefix tailTrace_208894
  have hstable : (prefixWord ++ tailWord_208894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208894).length < 2 ^ (prefixWord ++ tailWord_208894).sum := by decide
  have hdescent : baseEnd_208894 < baseStart_208894 := by decide
  rcases family_descends (prefixWord ++ tailWord_208894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208901 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_208901 : Nat := 118140960795 + 208901 * 2 ^ 59
def prefixEnd_208901 : Nat := 4983230072969 + 3 ^ 40 * 208901 * 2
def baseEnd_208901 : Nat := 71511081469994938384525

theorem tailTrace_208901 : CollatzResearch.WordTrace tailWord_208901 prefixEnd_208901 71511081469994938384525 := by
  unfold tailWord_208901
  simp only [CollatzResearch.WordTrace]
  refine ⟨7619245416194829295482557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5079496944129886196988371 7619245416194829295482557)
  ·
    refine ⟨2857217031073060985805959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7619245416194829295482557 2857217031073060985805959)
    ·
      refine ⟨4285825546609591478708939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2857217031073060985805959 4285825546609591478708939)
      ·
        refine ⟨6428738319914387218063409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4285825546609591478708939 6428738319914387218063409)
        ·
          refine ⟨4821553739935790413547557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6428738319914387218063409 4821553739935790413547557)
          ·
            refine ⟨904041326237960702540167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4821553739935790413547557 904041326237960702540167)
            ·
              refine ⟨1356061989356941053810251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904041326237960702540167 1356061989356941053810251)
              ·
                refine ⟨2034092984035411580715377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1356061989356941053810251 2034092984035411580715377)
                ·
                  refine ⟨1525569738026558685536533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2034092984035411580715377 1525569738026558685536533)
                  ·
                    refine ⟨71511081469994938384525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1525569738026558685536533 71511081469994938384525)
                    ·
                      rfl

theorem cell22_208901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_208901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208901 prefixEnd_208901 := by exact prefixLift 208901
  have htrace : WordTrace (prefixWord ++ tailWord_208901) baseStart_208901 baseEnd_208901 := by
    simpa [prefixWord, tailWord_208901, baseEnd_208901] using wordTrace_append hprefix tailTrace_208901
  have hstable : (prefixWord ++ tailWord_208901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208901).length < 2 ^ (prefixWord ++ tailWord_208901).sum := by decide
  have hdescent : baseEnd_208901 < baseStart_208901 := by decide
  rcases family_descends (prefixWord ++ tailWord_208901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208909 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_208909 : Nat := 118140960795 + 208909 * 2 ^ 59
def prefixEnd_208909 : Nat := 4983230072969 + 3 ^ 40 * 208909 * 2
def baseEnd_208909 : Nat := 71513820033485584184501

theorem tailTrace_208909 : CollatzResearch.WordTrace tailWord_208909 prefixEnd_208909 71513820033485584184501 := by
  unfold tailWord_208909
  simp only [CollatzResearch.WordTrace]
  refine ⟨7619537200165846661773781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5079691466777231107849187 7619537200165846661773781)
  ·
    refine ⟨178582903128887031135323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7619537200165846661773781 178582903128887031135323)
    ·
      refine ⟨267874354693330546702985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178582903128887031135323 267874354693330546702985)
      ·
        refine ⟨200905766019997910027239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267874354693330546702985 200905766019997910027239)
        ·
          refine ⟨301358649029996865040859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200905766019997910027239 301358649029996865040859)
          ·
            refine ⟨452037973544995297561289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301358649029996865040859 452037973544995297561289)
            ·
              refine ⟨339028480158746473170967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452037973544995297561289 339028480158746473170967)
              ·
                refine ⟨508542720238119709756451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339028480158746473170967 508542720238119709756451)
                ·
                  refine ⟨762814080357179564634677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508542720238119709756451 762814080357179564634677)
                  ·
                    refine ⟨71513820033485584184501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 762814080357179564634677 71513820033485584184501)
                    ·
                      rfl

theorem cell22_208909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_208909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208909 prefixEnd_208909 := by exact prefixLift 208909
  have htrace : WordTrace (prefixWord ++ tailWord_208909) baseStart_208909 baseEnd_208909 := by
    simpa [prefixWord, tailWord_208909, baseEnd_208909] using wordTrace_append hprefix tailTrace_208909
  have hstable : (prefixWord ++ tailWord_208909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208909).length < 2 ^ (prefixWord ++ tailWord_208909).sum := by decide
  have hdescent : baseEnd_208909 < baseStart_208909 := by decide
  rcases family_descends (prefixWord ++ tailWord_208909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208931 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 1, 7]
def baseStart_208931 : Nat := 118140960795 + 208931 * 2 ^ 59
def prefixEnd_208931 : Nat := 4983230072969 + 3 ^ 40 * 208931 * 2
def baseEnd_208931 : Nat := 71521351083084860134433

theorem tailTrace_208931 : CollatzResearch.WordTrace tailWord_208931 prefixEnd_208931 71521351083084860134433 := by
  unfold tailWord_208931
  simp only [CollatzResearch.WordTrace]
  refine ⟨7620339606086144419074647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5080226404057429612716431 7620339606086144419074647)
  ·
    refine ⟨11430509409129216628611971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7620339606086144419074647 11430509409129216628611971)
    ·
      refine ⟨17145764113693824942917957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11430509409129216628611971 17145764113693824942917957)
      ·
        refine ⟨3214830771317592176797117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17145764113693824942917957 3214830771317592176797117)
        ·
          refine ⟨1205561539244097066298919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3214830771317592176797117 1205561539244097066298919)
          ·
            refine ⟨1808342308866145599448379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205561539244097066298919 1808342308866145599448379)
            ·
              refine ⟨2712513463299218399172569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1808342308866145599448379 2712513463299218399172569)
              ·
                refine ⟨2034385097474413799379427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2712513463299218399172569 2034385097474413799379427)
                ·
                  refine ⟨3051577646211620699069141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034385097474413799379427 3051577646211620699069141)
                  ·
                    refine ⟨71521351083084860134433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3051577646211620699069141 71521351083084860134433)
                    ·
                      rfl

theorem cell22_208931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_208931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208931 prefixEnd_208931 := by exact prefixLift 208931
  have htrace : WordTrace (prefixWord ++ tailWord_208931) baseStart_208931 baseEnd_208931 := by
    simpa [prefixWord, tailWord_208931, baseEnd_208931] using wordTrace_append hprefix tailTrace_208931
  have hstable : (prefixWord ++ tailWord_208931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208931).length < 2 ^ (prefixWord ++ tailWord_208931).sum := by decide
  have hdescent : baseEnd_208931 < baseStart_208931 := by decide
  rcases family_descends (prefixWord ++ tailWord_208931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208995 : List Nat := [1, 1, 1, 5, 1, 1, 5, 3, 4]
def baseStart_208995 : Nat := 118140960795 + 208995 * 2 ^ 59
def prefixEnd_208995 : Nat := 4983230072969 + 3 ^ 40 * 208995 * 2
def baseEnd_208995 : Nat := 23847753197003342178079

theorem tailTrace_208995 : CollatzResearch.WordTrace tailWord_208995 prefixEnd_208995 23847753197003342178079 := by
  unfold tailWord_208995
  simp only [CollatzResearch.WordTrace]
  refine ⟨7622673877854283349404439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5081782585236188899602959 7622673877854283349404439)
  ·
    refine ⟨11434010816781425024106659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7622673877854283349404439 11434010816781425024106659)
    ·
      refine ⟨17151016225172137536159989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11434010816781425024106659 17151016225172137536159989)
      ·
        refine ⟨1607907771109887894014999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17151016225172137536159989 1607907771109887894014999)
        ·
          refine ⟨2411861656664831841022499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1607907771109887894014999 2411861656664831841022499)
          ·
            refine ⟨3617792484997247761533749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411861656664831841022499 3617792484997247761533749)
            ·
              refine ⟨339168045468491977643789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3617792484997247761533749 339168045468491977643789)
              ·
                refine ⟨127188017050684491616421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339168045468491977643789 127188017050684491616421)
                ·
                  refine ⟨23847753197003342178079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127188017050684491616421 23847753197003342178079)
                  ·
                    rfl

theorem cell22_208995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 4].length) (baseStart_208995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_208995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_208995 prefixEnd_208995 := by exact prefixLift 208995
  have htrace : WordTrace (prefixWord ++ tailWord_208995) baseStart_208995 baseEnd_208995 := by
    simpa [prefixWord, tailWord_208995, baseEnd_208995] using wordTrace_append hprefix tailTrace_208995
  have hstable : (prefixWord ++ tailWord_208995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208995).length < 2 ^ (prefixWord ++ tailWord_208995).sum := by decide
  have hdescent : baseEnd_208995 < baseStart_208995 := by decide
  rcases family_descends (prefixWord ++ tailWord_208995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209008 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 4, 4]
def baseStart_209008 : Nat := 118140960795 + 209008 * 2 ^ 59
def prefixEnd_209008 : Nat := 4983230072969 + 3 ^ 40 * 209008 * 2
def baseEnd_209008 : Nat := 71547709756682325959197

theorem tailTrace_209008 : CollatzResearch.WordTrace tailWord_209008 prefixEnd_209008 71547709756682325959197 := by
  unfold tailWord_209008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3811574013403593284813839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5082098684538124379751785 3811574013403593284813839)
  ·
    refine ⟨5717361020105389927220759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3811574013403593284813839 5717361020105389927220759)
    ·
      refine ⟨8576041530158084890831139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5717361020105389927220759 8576041530158084890831139)
      ·
        refine ⟨12864062295237127336246709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8576041530158084890831139 12864062295237127336246709)
        ·
          refine ⟨1206005840178480687773129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12864062295237127336246709 1206005840178480687773129)
          ·
            refine ⟨904504380133860515829847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206005840178480687773129 904504380133860515829847)
            ·
              refine ⟨1356756570200790773744771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904504380133860515829847 1356756570200790773744771)
              ·
                refine ⟨2035134855301186160617157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1356756570200790773744771 2035134855301186160617157)
                ·
                  refine ⟨381587785368972405115717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2035134855301186160617157 381587785368972405115717)
                  ·
                    refine ⟨71547709756682325959197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 381587785368972405115717 71547709756682325959197)
                    ·
                      rfl

theorem cell22_209008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_209008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209008 prefixEnd_209008 := by exact prefixLift 209008
  have htrace : WordTrace (prefixWord ++ tailWord_209008) baseStart_209008 baseEnd_209008 := by
    simpa [prefixWord, tailWord_209008, baseEnd_209008] using wordTrace_append hprefix tailTrace_209008
  have hstable : (prefixWord ++ tailWord_209008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209008).length < 2 ^ (prefixWord ++ tailWord_209008).sum := by decide
  have hdescent : baseEnd_209008 < baseStart_209008 := by decide
  rcases family_descends (prefixWord ++ tailWord_209008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209010 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_209010 : Nat := 118140960795 + 209010 * 2 ^ 59
def prefixEnd_209010 : Nat := 4983230072969 + 3 ^ 40 * 209010 * 2
def baseEnd_209010 : Nat := 71548394397554987409191

theorem tailTrace_209010 : CollatzResearch.WordTrace tailWord_209010 prefixEnd_209010 71548394397554987409191 := by
  unfold tailWord_209010
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905805243199985227800121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5082147315199960607466989 1905805243199985227800121)
  ·
    refine ⟨1429353932399988920850091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1905805243199985227800121 1429353932399988920850091)
    ·
      refine ⟨2144030898599983381275137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1429353932399988920850091 2144030898599983381275137)
      ·
        refine ⟨1608023173949987535956353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2144030898599983381275137 1608023173949987535956353)
        ·
          refine ⟨1206017380462490651967265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1608023173949987535956353 1206017380462490651967265)
          ·
            refine ⟨904513035346867988975449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206017380462490651967265 904513035346867988975449)
            ·
              refine ⟨678384776510150991731587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 904513035346867988975449 678384776510150991731587)
              ·
                refine ⟨1017577164765226487597381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678384776510150991731587 1017577164765226487597381)
                ·
                  refine ⟨190795718393479966424509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1017577164765226487597381 190795718393479966424509)
                  ·
                    refine ⟨71548394397554987409191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190795718393479966424509 71548394397554987409191)
                    ·
                      rfl

theorem cell22_209010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_209010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209010 prefixEnd_209010 := by exact prefixLift 209010
  have htrace : WordTrace (prefixWord ++ tailWord_209010) baseStart_209010 baseEnd_209010 := by
    simpa [prefixWord, tailWord_209010, baseEnd_209010] using wordTrace_append hprefix tailTrace_209010
  have hstable : (prefixWord ++ tailWord_209010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209010).length < 2 ^ (prefixWord ++ tailWord_209010).sum := by decide
  have hdescent : baseEnd_209010 < baseStart_209010 := by decide
  rcases family_descends (prefixWord ++ tailWord_209010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209027 : List Nat := [1, 1, 1, 3, 3, 3, 4, 1, 2, 3]
def baseStart_209027 : Nat := 118140960795 + 209027 * 2 ^ 59
def prefixEnd_209027 : Nat := 4983230072969 + 3 ^ 40 * 209027 * 2
def baseEnd_209027 : Nat := 71554213844972609734139

theorem tailTrace_209027 : CollatzResearch.WordTrace tailWord_209027 prefixEnd_209027 71554213844972609734139 := by
  unfold tailWord_209027
  simp only [CollatzResearch.WordTrace]
  refine ⟨7623841013738352814569335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5082560675825568543046223 7623841013738352814569335)
  ·
    refine ⟨11435761520607529221854003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7623841013738352814569335 11435761520607529221854003)
    ·
      refine ⟨17153642280911293832781005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11435761520607529221854003 17153642280911293832781005)
      ·
        refine ⟨6432615855341735187292877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17153642280911293832781005 6432615855341735187292877)
        ·
          refine ⟨2412230945753150695234829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6432615855341735187292877 2412230945753150695234829)
          ·
            refine ⟨904586604657431510713061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2412230945753150695234829 904586604657431510713061)
            ·
              refine ⟨169609988373268408258699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 904586604657431510713061 169609988373268408258699)
              ·
                refine ⟨254414982559902612388049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169609988373268408258699 254414982559902612388049)
                ·
                  refine ⟨190811236919926959291037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254414982559902612388049 190811236919926959291037)
                  ·
                    refine ⟨71554213844972609734139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190811236919926959291037 71554213844972609734139)
                    ·
                      rfl

theorem cell22_209027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 2, 3].length) (baseStart_209027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209027 prefixEnd_209027 := by exact prefixLift 209027
  have htrace : WordTrace (prefixWord ++ tailWord_209027) baseStart_209027 baseEnd_209027 := by
    simpa [prefixWord, tailWord_209027, baseEnd_209027] using wordTrace_append hprefix tailTrace_209027
  have hstable : (prefixWord ++ tailWord_209027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209027).length < 2 ^ (prefixWord ++ tailWord_209027).sum := by decide
  have hdescent : baseEnd_209027 < baseStart_209027 := by decide
  rcases family_descends (prefixWord ++ tailWord_209027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209083 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 2, 5]
def baseStart_209083 : Nat := 118140960795 + 209083 * 2 ^ 59
def prefixEnd_209083 : Nat := 4983230072969 + 3 ^ 40 * 209083 * 2
def baseEnd_209083 : Nat := 71573383789407130333967

theorem tailTrace_209083 : CollatzResearch.WordTrace tailWord_209083 prefixEnd_209083 71573383789407130333967 := by
  unfold tailWord_209083
  simp only [CollatzResearch.WordTrace]
  refine ⟨7625883501535474378607903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5083922334356982919071935 7625883501535474378607903)
  ·
    refine ⟨11438825252303211567911855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7625883501535474378607903 11438825252303211567911855)
    ·
      refine ⟨17158237878454817351867783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11438825252303211567911855 17158237878454817351867783)
      ·
        refine ⟨25737356817682226027801675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17158237878454817351867783 25737356817682226027801675)
        ·
          refine ⟨38606035226523339041702513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25737356817682226027801675 38606035226523339041702513)
          ·
            refine ⟨28954526419892504281276885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38606035226523339041702513 28954526419892504281276885)
            ·
              refine ⟨678621712966230569092427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28954526419892504281276885 678621712966230569092427)
              ·
                refine ⟨1017932569449345853638641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678621712966230569092427 1017932569449345853638641)
                ·
                  refine ⟨763449427087009390228981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1017932569449345853638641 763449427087009390228981)
                  ·
                    refine ⟨71573383789407130333967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 763449427087009390228981 71573383789407130333967)
                    ·
                      rfl

theorem cell22_209083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 5].length) (baseStart_209083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209083 prefixEnd_209083 := by exact prefixLift 209083
  have htrace : WordTrace (prefixWord ++ tailWord_209083) baseStart_209083 baseEnd_209083 := by
    simpa [prefixWord, tailWord_209083, baseEnd_209083] using wordTrace_append hprefix tailTrace_209083
  have hstable : (prefixWord ++ tailWord_209083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209083).length < 2 ^ (prefixWord ++ tailWord_209083).sum := by decide
  have hdescent : baseEnd_209083 < baseStart_209083 := by decide
  rcases family_descends (prefixWord ++ tailWord_209083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209089 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 3, 3]
def baseStart_209089 : Nat := 118140960795 + 209089 * 2 ^ 59
def prefixEnd_209089 : Nat := 4983230072969 + 3 ^ 40 * 209089 * 2
def baseEnd_209089 : Nat := 71575437712025114683949

theorem tailTrace_209089 : CollatzResearch.WordTrace tailWord_209089 prefixEnd_209089 71575437712025114683949 := by
  unfold tailWord_209089
  simp only [CollatzResearch.WordTrace]
  refine ⟨7626102339513737403326321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5084068226342491602217547 7626102339513737403326321)
  ·
    refine ⟨5719576754635303052494741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7626102339513737403326321 5719576754635303052494741)
    ·
      refine ⟨268105160373529830585691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5719576754635303052494741 268105160373529830585691)
      ·
        refine ⟨402157740560294745878537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268105160373529830585691 402157740560294745878537)
        ·
          refine ⟨301618305420221059408903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402157740560294745878537 301618305420221059408903)
          ·
            refine ⟨452427458130331589113355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301618305420221059408903 452427458130331589113355)
            ·
              refine ⟨678641187195497383670033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452427458130331589113355 678641187195497383670033)
              ·
                refine ⟨508980890396623037752525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678641187195497383670033 508980890396623037752525)
                ·
                  refine ⟨190867833898733639157197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508980890396623037752525 190867833898733639157197)
                  ·
                    refine ⟨71575437712025114683949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190867833898733639157197 71575437712025114683949)
                    ·
                      rfl

theorem cell22_209089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_209089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209089 prefixEnd_209089 := by exact prefixLift 209089
  have htrace : WordTrace (prefixWord ++ tailWord_209089) baseStart_209089 baseEnd_209089 := by
    simpa [prefixWord, tailWord_209089, baseEnd_209089] using wordTrace_append hprefix tailTrace_209089
  have hstable : (prefixWord ++ tailWord_209089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209089).length < 2 ^ (prefixWord ++ tailWord_209089).sum := by decide
  have hdescent : baseEnd_209089 < baseStart_209089 := by decide
  rcases family_descends (prefixWord ++ tailWord_209089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209130 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 6]
def baseStart_209130 : Nat := 118140960795 + 209130 * 2 ^ 59
def prefixEnd_209130 : Nat := 4983230072969 + 3 ^ 40 * 209130 * 2
def baseEnd_209130 : Nat := 23863157616638224802941

theorem tailTrace_209130 : CollatzResearch.WordTrace tailWord_209130 prefixEnd_209130 23863157616638224802941 := by
  unfold tailWord_209130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906899433091300351392211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5085065154910134270379229 1906899433091300351392211)
  ·
    refine ⟨2860349149636950527088317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1906899433091300351392211 2860349149636950527088317)
    ·
      refine ⟨1072630931113856447658119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2860349149636950527088317 1072630931113856447658119)
      ·
        refine ⟨1608946396670784671487179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072630931113856447658119 1608946396670784671487179)
        ·
          refine ⟨2413419595006177007230769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1608946396670784671487179 2413419595006177007230769)
          ·
            refine ⟨1810064696254632755423077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2413419595006177007230769 1810064696254632755423077)
            ·
              refine ⟨339387130547743641641827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1810064696254632755423077 339387130547743641641827)
              ·
                refine ⟨509080695821615462462741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339387130547743641641827 509080695821615462462741)
                ·
                  refine ⟨23863157616638224802941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 509080695821615462462741 23863157616638224802941)
                  ·
                    rfl

theorem cell22_209130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_209130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209130 prefixEnd_209130 := by exact prefixLift 209130
  have htrace : WordTrace (prefixWord ++ tailWord_209130) baseStart_209130 baseEnd_209130 := by
    simpa [prefixWord, tailWord_209130, baseEnd_209130] using wordTrace_append hprefix tailTrace_209130
  have hstable : (prefixWord ++ tailWord_209130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209130).length < 2 ^ (prefixWord ++ tailWord_209130).sum := by decide
  have hdescent : baseEnd_209130 < baseStart_209130 := by decide
  rcases family_descends (prefixWord ++ tailWord_209130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209160 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 1, 6]
def baseStart_209160 : Nat := 118140960795 + 209160 * 2 ^ 59
def prefixEnd_209160 : Nat := 4983230072969 + 3 ^ 40 * 209160 * 2
def baseEnd_209160 : Nat := 71599742463004596158731

theorem tailTrace_209160 : CollatzResearch.WordTrace tailWord_209160 prefixEnd_209160 71599742463004596158731 := by
  unfold tailWord_209160
  simp only [CollatzResearch.WordTrace]
  refine ⟨3814345961128258264580467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5085794614837677686107289 3814345961128258264580467)
  ·
    refine ⟨5721518941692387396870701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3814345961128258264580467 5721518941692387396870701)
    ·
      refine ⟨2145569603134645273826513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5721518941692387396870701 2145569603134645273826513)
      ·
        refine ⟨1609177202350983955369885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2145569603134645273826513 1609177202350983955369885)
        ·
          refine ⟨603441450881618983263707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1609177202350983955369885 603441450881618983263707)
          ·
            refine ⟨905162176322428474895561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603441450881618983263707 905162176322428474895561)
            ·
              refine ⟨678871632241821356171671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905162176322428474895561 678871632241821356171671)
              ·
                refine ⟨1018307448362732034257507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678871632241821356171671 1018307448362732034257507)
                ·
                  refine ⟨1527461172544098051386261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018307448362732034257507 1527461172544098051386261)
                  ·
                    refine ⟨71599742463004596158731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1527461172544098051386261 71599742463004596158731)
                    ·
                      rfl

theorem cell22_209160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_209160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209160 prefixEnd_209160 := by exact prefixLift 209160
  have htrace : WordTrace (prefixWord ++ tailWord_209160) baseStart_209160 baseEnd_209160 := by
    simpa [prefixWord, tailWord_209160, baseEnd_209160] using wordTrace_append hprefix tailTrace_209160
  have hstable : (prefixWord ++ tailWord_209160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209160).length < 2 ^ (prefixWord ++ tailWord_209160).sum := by decide
  have hdescent : baseEnd_209160 < baseStart_209160 := by decide
  rcases family_descends (prefixWord ++ tailWord_209160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209175 : List Nat := [1, 1, 3, 4, 1, 4, 8]
def baseStart_209175 : Nat := 118140960795 + 209175 * 2 ^ 59
def prefixEnd_209175 : Nat := 4983230072969 + 3 ^ 40 * 209175 * 2
def baseEnd_209175 : Nat := 2652032491464798408655

theorem tailTrace_209175 : CollatzResearch.WordTrace tailWord_209175 prefixEnd_209175 2652032491464798408655 := by
  unfold tailWord_209175
  simp only [CollatzResearch.WordTrace]
  refine ⟨7629239017202174090956979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5086159344801449393971319 7629239017202174090956979)
  ·
    refine ⟨11443858525803261136435469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7629239017202174090956979 11443858525803261136435469)
    ·
      refine ⟨4291446947176222926163301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11443858525803261136435469 4291446947176222926163301)
      ·
        refine ⟨804646302595541798655619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4291446947176222926163301 804646302595541798655619)
        ·
          refine ⟨1206969453893312697983429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804646302595541798655619 1206969453893312697983429)
          ·
            refine ⟨226306772604996130871893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1206969453893312697983429 226306772604996130871893)
            ·
              refine ⟨2652032491464798408655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 226306772604996130871893 2652032491464798408655)
              ·
                rfl

theorem cell22_209175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 8].length) (baseStart_209175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209175 prefixEnd_209175 := by exact prefixLift 209175
  have htrace : WordTrace (prefixWord ++ tailWord_209175) baseStart_209175 baseEnd_209175 := by
    simpa [prefixWord, tailWord_209175, baseEnd_209175] using wordTrace_append hprefix tailTrace_209175
  have hstable : (prefixWord ++ tailWord_209175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209175).length < 2 ^ (prefixWord ++ tailWord_209175).sum := by decide
  have hdescent : baseEnd_209175 < baseStart_209175 := by decide
  rcases family_descends (prefixWord ++ tailWord_209175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209181 : List Nat := [1, 4, 2, 3, 2, 1, 3, 2, 4]
def baseStart_209181 : Nat := 118140960795 + 209181 * 2 ^ 59
def prefixEnd_209181 : Nat := 4983230072969 + 3 ^ 40 * 209181 * 2
def baseEnd_209181 : Nat := 23868977064055847127889

theorem tailTrace_209181 : CollatzResearch.WordTrace tailWord_209181 prefixEnd_209181 23868977064055847127889 := by
  unfold tailWord_209181
  simp only [CollatzResearch.WordTrace]
  refine ⟨7629457855180437115675397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5086305236786958077116931 7629457855180437115675397)
  ·
    refine ⟨1430523347846331959189137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7629457855180437115675397 1430523347846331959189137)
    ·
      refine ⟨1072892510884748969391853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1430523347846331959189137 1072892510884748969391853)
      ·
        refine ⟨402334691581780863521945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1072892510884748969391853 402334691581780863521945)
        ·
          refine ⟨301751018686335647641459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402334691581780863521945 301751018686335647641459)
          ·
            refine ⟨452626528029503471462189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301751018686335647641459 452626528029503471462189)
            ·
              refine ⟨169734948011063801798321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 452626528029503471462189 169734948011063801798321)
              ·
                refine ⟨127301211008297851348741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169734948011063801798321 127301211008297851348741)
                ·
                  refine ⟨23868977064055847127889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127301211008297851348741 23868977064055847127889)
                  ·
                    rfl

theorem cell22_209181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_209181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209181 prefixEnd_209181 := by exact prefixLift 209181
  have htrace : WordTrace (prefixWord ++ tailWord_209181) baseStart_209181 baseEnd_209181 := by
    simpa [prefixWord, tailWord_209181, baseEnd_209181] using wordTrace_append hprefix tailTrace_209181
  have hstable : (prefixWord ++ tailWord_209181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209181).length < 2 ^ (prefixWord ++ tailWord_209181).sum := by decide
  have hdescent : baseEnd_209181 < baseStart_209181 := by decide
  rcases family_descends (prefixWord ++ tailWord_209181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209192 : List Nat := [2, 1, 5, 1, 3, 1, 2, 7]
def baseStart_209192 : Nat := 118140960795 + 209192 * 2 ^ 59
def prefixEnd_209192 : Nat := 4983230072969 + 3 ^ 40 * 209192 * 2
def baseEnd_209192 : Nat := 7956744079663019928737

theorem tailTrace_209192 : CollatzResearch.WordTrace tailWord_209192 prefixEnd_209192 7956744079663019928737 := by
  unfold tailWord_209192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3814929529070292997162915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5086572705427057329550553 3814929529070292997162915)
  ·
    refine ⟨5722394293605439495744373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3814929529070292997162915 5722394293605439495744373)
    ·
      refine ⟨536474465025509952726035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5722394293605439495744373 536474465025509952726035)
      ·
        refine ⟨804711697538264929089053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536474465025509952726035 804711697538264929089053)
        ·
          refine ⟨301766886576849348408395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 804711697538264929089053 301766886576849348408395)
          ·
            refine ⟨452650329865274022612593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301766886576849348408395 452650329865274022612593)
            ·
              refine ⟨339487747398955516959445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452650329865274022612593 339487747398955516959445)
              ·
                refine ⟨7956744079663019928737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 339487747398955516959445 7956744079663019928737)
                ·
                  rfl

theorem cell22_209192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 7].length) (baseStart_209192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209192 prefixEnd_209192 := by exact prefixLift 209192
  have htrace : WordTrace (prefixWord ++ tailWord_209192) baseStart_209192 baseEnd_209192 := by
    simpa [prefixWord, tailWord_209192, baseEnd_209192] using wordTrace_append hprefix tailTrace_209192
  have hstable : (prefixWord ++ tailWord_209192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209192).length < 2 ^ (prefixWord ++ tailWord_209192).sum := by decide
  have hdescent : baseEnd_209192 < baseStart_209192 := by decide
  rcases family_descends (prefixWord ++ tailWord_209192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209333 : List Nat := [1, 3, 3, 2, 4, 1, 1, 3, 4]
def baseStart_209333 : Nat := 118140960795 + 209333 * 2 ^ 59
def prefixEnd_209333 : Nat := 4983230072969 + 3 ^ 40 * 209333 * 2
def baseEnd_209333 : Nat := 23886321299496603861067

theorem tailTrace_209333 : CollatzResearch.WordTrace tailWord_209333 prefixEnd_209333 23886321299496603861067 := by
  unfold tailWord_209333
  simp only [CollatzResearch.WordTrace]
  refine ⟨7635001750629767075208653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5090001167086511383472435 7635001750629767075208653)
  ·
    refine ⟨2863125656486162653203245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7635001750629767075208653 2863125656486162653203245)
    ·
      refine ⟨1073672121182310994951217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2863125656486162653203245 1073672121182310994951217)
      ·
        refine ⟨805254090886733246213413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1073672121182310994951217 805254090886733246213413)
        ·
          refine ⟨150985142041262483665015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 805254090886733246213413 150985142041262483665015)
          ·
            refine ⟨226477713061893725497523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150985142041262483665015 226477713061893725497523)
            ·
              refine ⟨339716569592840588246285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226477713061893725497523 339716569592840588246285)
              ·
                refine ⟨127393713597315220592357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339716569592840588246285 127393713597315220592357)
                ·
                  refine ⟨23886321299496603861067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127393713597315220592357 23886321299496603861067)
                  ·
                    rfl

theorem cell22_209333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_209333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209333 prefixEnd_209333 := by exact prefixLift 209333
  have htrace : WordTrace (prefixWord ++ tailWord_209333) baseStart_209333 baseEnd_209333 := by
    simpa [prefixWord, tailWord_209333, baseEnd_209333] using wordTrace_append hprefix tailTrace_209333
  have hstable : (prefixWord ++ tailWord_209333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209333).length < 2 ^ (prefixWord ++ tailWord_209333).sum := by decide
  have hdescent : baseEnd_209333 < baseStart_209333 := by decide
  rcases family_descends (prefixWord ++ tailWord_209333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209410 : List Nat := [3, 4, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_209410 : Nat := 118140960795 + 209410 * 2 ^ 59
def prefixEnd_209410 : Nat := 4983230072969 + 3 ^ 40 * 209410 * 2
def baseEnd_209410 : Nat := 71685322572087277407965

theorem tailTrace_209410 : CollatzResearch.WordTrace tailWord_209410 prefixEnd_209410 71685322572087277407965 := by
  unfold tailWord_209410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909452542837702306440421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5091873447567206150507789 1909452542837702306440421)
  ·
    refine ⟨358022351782069182457579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1909452542837702306440421 358022351782069182457579)
    ·
      refine ⟨537033527673103773686369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358022351782069182457579 537033527673103773686369)
      ·
        refine ⟨402775145754827830264777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537033527673103773686369 402775145754827830264777)
        ·
          refine ⟨302081359316120872698583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402775145754827830264777 302081359316120872698583)
          ·
            refine ⟨453122038974181309047875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302081359316120872698583 453122038974181309047875)
            ·
              refine ⟨679683058461271963571813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453122038974181309047875 679683058461271963571813)
              ·
                refine ⟨127440573461488493169715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679683058461271963571813 127440573461488493169715)
                ·
                  refine ⟨191160860192232739754573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127440573461488493169715 191160860192232739754573)
                  ·
                    refine ⟨71685322572087277407965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 191160860192232739754573 71685322572087277407965)
                    ·
                      rfl

theorem cell22_209410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_209410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209410 prefixEnd_209410 := by exact prefixLift 209410
  have htrace : WordTrace (prefixWord ++ tailWord_209410) baseStart_209410 baseEnd_209410 := by
    simpa [prefixWord, tailWord_209410, baseEnd_209410] using wordTrace_append hprefix tailTrace_209410
  have hstable : (prefixWord ++ tailWord_209410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209410).length < 2 ^ (prefixWord ++ tailWord_209410).sum := by decide
  have hdescent : baseEnd_209410 < baseStart_209410 := by decide
  rcases family_descends (prefixWord ++ tailWord_209410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209421 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_209421 : Nat := 118140960795 + 209421 * 2 ^ 59
def prefixEnd_209421 : Nat := 4983230072969 + 3 ^ 40 * 209421 * 2
def baseEnd_209421 : Nat := 71689088096886915382931

theorem tailTrace_209421 : CollatzResearch.WordTrace tailWord_209421 prefixEnd_209421 71689088096886915382931 := by
  unfold tailWord_209421
  simp only [CollatzResearch.WordTrace]
  refine ⟨7638211374310958104412117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5092140916207305402941411 7638211374310958104412117)
  ·
    refine ⟨179020579085413080572159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7638211374310958104412117 179020579085413080572159)
    ·
      refine ⟨268530868628119620858239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179020579085413080572159 268530868628119620858239)
      ·
        refine ⟨402796302942179431287359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268530868628119620858239 402796302942179431287359)
        ·
          refine ⟨604194454413269146931039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402796302942179431287359 604194454413269146931039)
          ·
            refine ⟨906291681619903720396559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604194454413269146931039 906291681619903720396559)
            ·
              refine ⟨1359437522429855580594839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906291681619903720396559 1359437522429855580594839)
              ·
                refine ⟨2039156283644783370892259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359437522429855580594839 2039156283644783370892259)
                ·
                  refine ⟨3058734425467175056338389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039156283644783370892259 3058734425467175056338389)
                  ·
                    refine ⟨71689088096886915382931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3058734425467175056338389 71689088096886915382931)
                    ·
                      rfl

theorem cell22_209421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_209421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209421 prefixEnd_209421 := by exact prefixLift 209421
  have htrace : WordTrace (prefixWord ++ tailWord_209421) baseStart_209421 baseEnd_209421 := by
    simpa [prefixWord, tailWord_209421, baseEnd_209421] using wordTrace_append hprefix tailTrace_209421
  have hstable : (prefixWord ++ tailWord_209421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209421).length < 2 ^ (prefixWord ++ tailWord_209421).sum := by decide
  have hdescent : baseEnd_209421 < baseStart_209421 := by decide
  rcases family_descends (prefixWord ++ tailWord_209421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209466 : List Nat := [3, 1, 1, 1, 3, 3, 3, 2, 2, 3]
def baseStart_209466 : Nat := 118140960795 + 209466 * 2 ^ 59
def prefixEnd_209466 : Nat := 4983230072969 + 3 ^ 40 * 209466 * 2
def baseEnd_209466 : Nat := 71704492516521798007793

theorem tailTrace_209466 : CollatzResearch.WordTrace tailWord_209466 prefixEnd_209466 71704492516521798007793 := by
  unfold tailWord_209466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909963164786982697450063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5093235106098620526533501 1909963164786982697450063)
  ·
    refine ⟨2864944747180474046175095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1909963164786982697450063 2864944747180474046175095)
    ·
      refine ⟨4297417120770711069262643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2864944747180474046175095 4297417120770711069262643)
      ·
        refine ⟨6446125681156066603893965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4297417120770711069262643 6446125681156066603893965)
        ·
          refine ⟨2417297130433524976460237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6446125681156066603893965 2417297130433524976460237)
          ·
            refine ⟨906486423912571866172589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2417297130433524976460237 906486423912571866172589)
            ·
              refine ⟨339932408967214449814721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 906486423912571866172589 339932408967214449814721)
              ·
                refine ⟨254949306725410837361041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339932408967214449814721 254949306725410837361041)
                ·
                  refine ⟨191211980044058128020781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254949306725410837361041 191211980044058128020781)
                  ·
                    refine ⟨71704492516521798007793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 191211980044058128020781 71704492516521798007793)
                    ·
                      rfl

theorem cell22_209466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_209466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209466 prefixEnd_209466 := by exact prefixLift 209466
  have htrace : WordTrace (prefixWord ++ tailWord_209466) baseStart_209466 baseEnd_209466 := by
    simpa [prefixWord, tailWord_209466, baseEnd_209466] using wordTrace_append hprefix tailTrace_209466
  have hstable : (prefixWord ++ tailWord_209466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209466).length < 2 ^ (prefixWord ++ tailWord_209466).sum := by decide
  have hdescent : baseEnd_209466 < baseStart_209466 := by decide
  rcases family_descends (prefixWord ++ tailWord_209466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209507 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 9]
def baseStart_209507 : Nat := 118140960795 + 209507 * 2 ^ 59
def prefixEnd_209507 : Nat := 4983230072969 + 3 ^ 40 * 209507 * 2
def baseEnd_209507 : Nat := 23906175884803785910889

theorem tailTrace_209507 : CollatzResearch.WordTrace tailWord_209507 prefixEnd_209507 23906175884803785910889 := by
  unfold tailWord_209507
  simp only [CollatzResearch.WordTrace]
  refine ⟨7641348051999394792042775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5094232034666263194695183 7641348051999394792042775)
  ·
    refine ⟨11462022077999092188064163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7641348051999394792042775 11462022077999092188064163)
    ·
      refine ⟨17193033116998638282096245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11462022077999092188064163 17193033116998638282096245)
      ·
        refine ⟨1611846854718622338946523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17193033116998638282096245 1611846854718622338946523)
        ·
          refine ⟨2417770282077933508419785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611846854718622338946523 2417770282077933508419785)
          ·
            refine ⟨1813327711558450131314839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2417770282077933508419785 1813327711558450131314839)
            ·
              refine ⟨2719991567337675196972259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813327711558450131314839 2719991567337675196972259)
              ·
                refine ⟨4079987351006512795458389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719991567337675196972259 4079987351006512795458389)
                ·
                  refine ⟨23906175884803785910889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4079987351006512795458389 23906175884803785910889)
                  ·
                    rfl

theorem cell22_209507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 9].length) (baseStart_209507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209507 prefixEnd_209507 := by exact prefixLift 209507
  have htrace : WordTrace (prefixWord ++ tailWord_209507) baseStart_209507 baseEnd_209507 := by
    simpa [prefixWord, tailWord_209507, baseEnd_209507] using wordTrace_append hprefix tailTrace_209507
  have hstable : (prefixWord ++ tailWord_209507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209507).length < 2 ^ (prefixWord ++ tailWord_209507).sum := by decide
  have hdescent : baseEnd_209507 < baseStart_209507 := by decide
  rcases family_descends (prefixWord ++ tailWord_209507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209541 : List Nat := [1, 3, 1, 1, 4, 2, 4, 1, 5]
def baseStart_209541 : Nat := 118140960795 + 209541 * 2 ^ 59
def prefixEnd_209541 : Nat := 4983230072969 + 3 ^ 40 * 209541 * 2
def baseEnd_209541 : Nat := 23910055516415534127521

theorem tailTrace_209541 : CollatzResearch.WordTrace tailWord_209541 prefixEnd_209541 23910055516415534127521 := by
  unfold tailWord_209541
  simp only [CollatzResearch.WordTrace]
  refine ⟨7642588133876218598780477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5095058755917479065853651 7642588133876218598780477)
  ·
    refine ⟨2865970550203581974542679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7642588133876218598780477 2865970550203581974542679)
    ·
      refine ⟨4298955825305372961814019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2865970550203581974542679 4298955825305372961814019)
      ·
        refine ⟨6448433737958059442721029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4298955825305372961814019 6448433737958059442721029)
        ·
          refine ⟨1209081325867136145510193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6448433737958059442721029 1209081325867136145510193)
          ·
            refine ⟨906810994400352109132645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1209081325867136145510193 906810994400352109132645)
            ·
              refine ⟨170027061450066020462371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 906810994400352109132645 170027061450066020462371)
              ·
                refine ⟨255040592175099030693557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170027061450066020462371 255040592175099030693557)
                ·
                  refine ⟨23910055516415534127521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255040592175099030693557 23910055516415534127521)
                  ·
                    rfl

theorem cell22_209541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_209541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209541 prefixEnd_209541 := by exact prefixLift 209541
  have htrace : WordTrace (prefixWord ++ tailWord_209541) baseStart_209541 baseEnd_209541 := by
    simpa [prefixWord, tailWord_209541, baseEnd_209541] using wordTrace_append hprefix tailTrace_209541
  have hstable : (prefixWord ++ tailWord_209541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209541).length < 2 ^ (prefixWord ++ tailWord_209541).sum := by decide
  have hdescent : baseEnd_209541 < baseStart_209541 := by decide
  rcases family_descends (prefixWord ++ tailWord_209541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209620 : List Nat := [2, 4, 1, 3, 2, 1, 2, 3, 4]
def baseStart_209620 : Nat := 118140960795 + 209620 * 2 ^ 59
def prefixEnd_209620 : Nat := 4983230072969 + 3 ^ 40 * 209620 * 2
def baseEnd_209620 : Nat := 23919069954572243219107

theorem tailTrace_209620 : CollatzResearch.WordTrace tailWord_209620 prefixEnd_209620 23919069954572243219107 := by
  unfold tailWord_209620
  simp only [CollatzResearch.WordTrace]
  refine ⟨3822734750295007545453157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5096979667060010060604209 3822734750295007545453157)
  ·
    refine ⟨716762765680313914772467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3822734750295007545453157 716762765680313914772467)
    ·
      refine ⟨1075144148520470872158701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 716762765680313914772467 1075144148520470872158701)
      ·
        refine ⟨403179055695176577059513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1075144148520470872158701 403179055695176577059513)
        ·
          refine ⟨302384291771382432794635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403179055695176577059513 302384291771382432794635)
          ·
            refine ⟨453576437657073649191953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302384291771382432794635 453576437657073649191953)
            ·
              refine ⟨340182328242805236893965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453576437657073649191953 340182328242805236893965)
              ·
                refine ⟨127568373091051963835237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340182328242805236893965 127568373091051963835237)
                ·
                  refine ⟨23919069954572243219107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127568373091051963835237 23919069954572243219107)
                  ·
                    rfl

theorem cell22_209620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_209620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209620 prefixEnd_209620 := by exact prefixLift 209620
  have htrace : WordTrace (prefixWord ++ tailWord_209620) baseStart_209620 baseEnd_209620 := by
    simpa [prefixWord, tailWord_209620, baseEnd_209620] using wordTrace_append hprefix tailTrace_209620
  have hstable : (prefixWord ++ tailWord_209620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209620).length < 2 ^ (prefixWord ++ tailWord_209620).sum := by decide
  have hdescent : baseEnd_209620 < baseStart_209620 := by decide
  rcases family_descends (prefixWord ++ tailWord_209620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209635 : List Nat := [1, 1, 1, 7, 1, 3, 1, 2, 2, 3]
def baseStart_209635 : Nat := 118140960795 + 209635 * 2 ^ 59
def prefixEnd_209635 : Nat := 4983230072969 + 3 ^ 40 * 209635 * 2
def baseEnd_209635 : Nat := 71762344670261690532275

theorem tailTrace_209635 : CollatzResearch.WordTrace tailWord_209635 prefixEnd_209635 71762344670261690532275 := by
  unfold tailWord_209635
  simp only [CollatzResearch.WordTrace]
  refine ⟨7646016595535672652702359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5097344397023781768468239 7646016595535672652702359)
  ·
    refine ⟨11469024893303508979053539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7646016595535672652702359 11469024893303508979053539)
    ·
      refine ⟨17203537339955263468580309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11469024893303508979053539 17203537339955263468580309)
      ·
        refine ⟨403207906405201487544851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 17203537339955263468580309 403207906405201487544851)
        ·
          refine ⟨604811859607802231317277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403207906405201487544851 604811859607802231317277)
          ·
            refine ⟨226804447352925836743979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 604811859607802231317277 226804447352925836743979)
            ·
              refine ⟨340206671029388755115969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226804447352925836743979 340206671029388755115969)
              ·
                refine ⟨255155003272041566336977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340206671029388755115969 255155003272041566336977)
                ·
                  refine ⟨191366252454031174752733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255155003272041566336977 191366252454031174752733)
                  ·
                    refine ⟨71762344670261690532275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 191366252454031174752733 71762344670261690532275)
                    ·
                      rfl

theorem cell22_209635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 3].length) (baseStart_209635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209635 prefixEnd_209635 := by exact prefixLift 209635
  have htrace : WordTrace (prefixWord ++ tailWord_209635) baseStart_209635 baseEnd_209635 := by
    simpa [prefixWord, tailWord_209635, baseEnd_209635] using wordTrace_append hprefix tailTrace_209635
  have hstable : (prefixWord ++ tailWord_209635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209635).length < 2 ^ (prefixWord ++ tailWord_209635).sum := by decide
  have hdescent : baseEnd_209635 < baseStart_209635 := by decide
  rcases family_descends (prefixWord ++ tailWord_209635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209652 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_209652 : Nat := 118140960795 + 209652 * 2 ^ 59
def prefixEnd_209652 : Nat := 4983230072969 + 3 ^ 40 * 209652 * 2
def baseEnd_209652 : Nat := 71768164117679312857223

theorem tailTrace_209652 : CollatzResearch.WordTrace tailWord_209652 prefixEnd_209652 71768164117679312857223 := by
  unfold tailWord_209652
  simp only [CollatzResearch.WordTrace]
  refine ⟨3823318318237042278035605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5097757757649389704047473 3823318318237042278035605)
  ·
    refine ⟨179218046167361356782919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3823318318237042278035605 179218046167361356782919)
    ·
      refine ⟨268827069251042035174379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179218046167361356782919 268827069251042035174379)
      ·
        refine ⟨403240603876563052761569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268827069251042035174379 403240603876563052761569)
        ·
          refine ⟨302430452907422289571177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403240603876563052761569 302430452907422289571177)
          ·
            refine ⟨226822839680566717178383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302430452907422289571177 226822839680566717178383)
            ·
              refine ⟨340234259520850075767575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226822839680566717178383 340234259520850075767575)
              ·
                refine ⟨510351389281275113651363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340234259520850075767575 510351389281275113651363)
                ·
                  refine ⟨765527083921912670477045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510351389281275113651363 765527083921912670477045)
                  ·
                    refine ⟨71768164117679312857223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 765527083921912670477045 71768164117679312857223)
                    ·
                      rfl

theorem cell22_209652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_209652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209652 prefixEnd_209652 := by exact prefixLift 209652
  have htrace : WordTrace (prefixWord ++ tailWord_209652) baseStart_209652 baseEnd_209652 := by
    simpa [prefixWord, tailWord_209652, baseEnd_209652] using wordTrace_append hprefix tailTrace_209652
  have hstable : (prefixWord ++ tailWord_209652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209652).length < 2 ^ (prefixWord ++ tailWord_209652).sum := by decide
  have hdescent : baseEnd_209652 < baseStart_209652 := by decide
  rcases family_descends (prefixWord ++ tailWord_209652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209710 : List Nat := [4, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_209710 : Nat := 118140960795 + 209710 * 2 ^ 59
def prefixEnd_209710 : Nat := 4983230072969 + 3 ^ 40 * 209710 * 2
def baseEnd_209710 : Nat := 23929339567662164969015

theorem tailTrace_209710 : CollatzResearch.WordTrace tailWord_209710 prefixEnd_209710 23929339567662164969015 := by
  unfold tailWord_209710
  simp only [CollatzResearch.WordTrace]
  refine ⟨956094008782995057710323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5099168046842640307788389 956094008782995057710323)
  ·
    refine ⟨1434141013174492586565485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 956094008782995057710323 1434141013174492586565485)
    ·
      refine ⟨537802879940434719962057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1434141013174492586565485 537802879940434719962057)
      ·
        refine ⟨403352159955326039971543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537802879940434719962057 403352159955326039971543)
        ·
          refine ⟨605028239932989059957315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403352159955326039971543 605028239932989059957315)
          ·
            refine ⟨907542359899483589935973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605028239932989059957315 907542359899483589935973)
            ·
              refine ⟨170164192481153173112995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 907542359899483589935973 170164192481153173112995)
              ·
                refine ⟨255246288721729759669493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170164192481153173112995 255246288721729759669493)
                ·
                  refine ⟨23929339567662164969015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255246288721729759669493 23929339567662164969015)
                  ·
                    rfl

theorem cell22_209710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_209710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209710 prefixEnd_209710 := by exact prefixLift 209710
  have htrace : WordTrace (prefixWord ++ tailWord_209710) baseStart_209710 baseEnd_209710 := by
    simpa [prefixWord, tailWord_209710, baseEnd_209710] using wordTrace_append hprefix tailTrace_209710
  have hstable : (prefixWord ++ tailWord_209710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209710).length < 2 ^ (prefixWord ++ tailWord_209710).sum := by decide
  have hdescent : baseEnd_209710 < baseStart_209710 := by decide
  rcases family_descends (prefixWord ++ tailWord_209710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209736 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 1, 5]
def baseStart_209736 : Nat := 118140960795 + 209736 * 2 ^ 59
def prefixEnd_209736 : Nat := 4983230072969 + 3 ^ 40 * 209736 * 2
def baseEnd_209736 : Nat := 71796919034331093756965

theorem tailTrace_209736 : CollatzResearch.WordTrace tailWord_209736 prefixEnd_209736 71796919034331093756965 := by
  unfold tailWord_209736
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824850184084883451064531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5099800245446511268086041 3824850184084883451064531)
  ·
    refine ⟨5737275276127325176596797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3824850184084883451064531 5737275276127325176596797)
    ·
      refine ⟨2151478228547746941223799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5737275276127325176596797 2151478228547746941223799)
      ·
        refine ⟨3227217342821620411835699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2151478228547746941223799 3227217342821620411835699)
        ·
          refine ⟨4840826014232430617753549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3227217342821620411835699 4840826014232430617753549)
          ·
            refine ⟨1815309755337161481657581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4840826014232430617753549 1815309755337161481657581)
            ·
              refine ⟨680741158251435555621593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1815309755337161481657581 680741158251435555621593)
              ·
                refine ⟨510555868688576666716195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 680741158251435555621593 510555868688576666716195)
                ·
                  refine ⟨765833803032865000074293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510555868688576666716195 765833803032865000074293)
                  ·
                    refine ⟨71796919034331093756965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 765833803032865000074293 71796919034331093756965)
                    ·
                      rfl

theorem cell22_209736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_209736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209736 prefixEnd_209736 := by exact prefixLift 209736
  have htrace : WordTrace (prefixWord ++ tailWord_209736) baseStart_209736 baseEnd_209736 := by
    simpa [prefixWord, tailWord_209736, baseEnd_209736] using wordTrace_append hprefix tailTrace_209736
  have hstable : (prefixWord ++ tailWord_209736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209736).length < 2 ^ (prefixWord ++ tailWord_209736).sum := by decide
  have hdescent : baseEnd_209736 < baseStart_209736 := by decide
  rcases family_descends (prefixWord ++ tailWord_209736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209740 : List Nat := [2, 2, 1, 3, 3, 2, 3, 1, 1, 4]
def baseStart_209740 : Nat := 118140960795 + 209740 * 2 ^ 59
def prefixEnd_209740 : Nat := 4983230072969 + 3 ^ 40 * 209740 * 2
def baseEnd_209740 : Nat := 71798288316076416656953

theorem tailTrace_209740 : CollatzResearch.WordTrace tailWord_209740 prefixEnd_209740 71798288316076416656953 := by
  unfold tailWord_209740
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824923130077637792637337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5099897506770183723516449 3824923130077637792637337)
  ·
    refine ⟨2868692347558228344478003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3824923130077637792637337 2868692347558228344478003)
    ·
      refine ⟨4303038521337342516717005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2868692347558228344478003 4303038521337342516717005)
      ·
        refine ⟨1613639445501503443768877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4303038521337342516717005 1613639445501503443768877)
        ·
          refine ⟨605114792063063791413329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1613639445501503443768877 605114792063063791413329)
          ·
            refine ⟨453836094047297843559997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605114792063063791413329 453836094047297843559997)
            ·
              refine ⟨170188535267736691334999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 453836094047297843559997 170188535267736691334999)
              ·
                refine ⟨255282802901605037002499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170188535267736691334999 255282802901605037002499)
                ·
                  refine ⟨382924204352407555503749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255282802901605037002499 382924204352407555503749)
                  ·
                    refine ⟨71798288316076416656953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 382924204352407555503749 71798288316076416656953)
                    ·
                      rfl

theorem cell22_209740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_209740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209740 prefixEnd_209740 := by exact prefixLift 209740
  have htrace : WordTrace (prefixWord ++ tailWord_209740) baseStart_209740 baseEnd_209740 := by
    simpa [prefixWord, tailWord_209740, baseEnd_209740] using wordTrace_append hprefix tailTrace_209740
  have hstable : (prefixWord ++ tailWord_209740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209740).length < 2 ^ (prefixWord ++ tailWord_209740).sum := by decide
  have hdescent : baseEnd_209740 < baseStart_209740 := by decide
  rcases family_descends (prefixWord ++ tailWord_209740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209753 : List Nat := [1, 2, 1, 2, 2, 4, 1, 4, 2, 3]
def baseStart_209753 : Nat := 118140960795 + 209753 * 2 ^ 59
def prefixEnd_209753 : Nat := 4983230072969 + 3 ^ 40 * 209753 * 2
def baseEnd_209753 : Nat := 71802738481748716081913

theorem tailTrace_209753 : CollatzResearch.WordTrace tailWord_209753 prefixEnd_209753 71802738481748716081913 := by
  unfold tailWord_209753
  simp only [CollatzResearch.WordTrace]
  refine ⟨7650320409108178805497913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5100213606072119203665275 7650320409108178805497913)
  ·
    refine ⟨5737740306831134104123435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7650320409108178805497913 5737740306831134104123435)
    ·
      refine ⟨8606610460246701156185153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5737740306831134104123435 8606610460246701156185153)
      ·
        refine ⟨6454957845185025867138865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8606610460246701156185153 6454957845185025867138865)
        ·
          refine ⟨4841218383888769400354149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6454957845185025867138865 4841218383888769400354149)
          ·
            refine ⟨907728446979144262566403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4841218383888769400354149 907728446979144262566403)
            ·
              refine ⟨1361592670468716393849605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907728446979144262566403 1361592670468716393849605)
              ·
                refine ⟨255298625712884323846801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1361592670468716393849605 255298625712884323846801)
                ·
                  refine ⟨191473969284663242885101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255298625712884323846801 191473969284663242885101)
                  ·
                    refine ⟨71802738481748716081913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 191473969284663242885101 71802738481748716081913)
                    ·
                      rfl

theorem cell22_209753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 3].length) (baseStart_209753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209753 prefixEnd_209753 := by exact prefixLift 209753
  have htrace : WordTrace (prefixWord ++ tailWord_209753) baseStart_209753 baseEnd_209753 := by
    simpa [prefixWord, tailWord_209753, baseEnd_209753] using wordTrace_append hprefix tailTrace_209753
  have hstable : (prefixWord ++ tailWord_209753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209753).length < 2 ^ (prefixWord ++ tailWord_209753).sum := by decide
  have hdescent : baseEnd_209753 < baseStart_209753 := by decide
  rcases family_descends (prefixWord ++ tailWord_209753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209811 : List Nat := [1, 1, 1, 2, 1, 2, 1, 8, 5]
def baseStart_209811 : Nat := 118140960795 + 209811 * 2 ^ 59
def prefixEnd_209811 : Nat := 4983230072969 + 3 ^ 40 * 209811 * 2
def baseEnd_209811 : Nat := 23940864355685299377245

theorem tailTrace_209811 : CollatzResearch.WordTrace tailWord_209811 prefixEnd_209811 23940864355685299377245 := by
  unfold tailWord_209811
  simp only [CollatzResearch.WordTrace]
  refine ⟨7652435842898054711109287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5101623895265369807406191 7652435842898054711109287)
  ·
    refine ⟨11478653764347082066663931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7652435842898054711109287 11478653764347082066663931)
    ·
      refine ⟨17217980646520623099995897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11478653764347082066663931 17217980646520623099995897)
      ·
        refine ⟨12913485484890467324996923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17217980646520623099995897 12913485484890467324996923)
        ·
          refine ⟨19370228227335700987495385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12913485484890467324996923 19370228227335700987495385)
          ·
            refine ⟨14527671170501775740621539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19370228227335700987495385 14527671170501775740621539)
            ·
              refine ⟨21791506755752663610932309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14527671170501775740621539 21791506755752663610932309)
              ·
                refine ⟨255369219793976526690613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 21791506755752663610932309 255369219793976526690613)
                ·
                  refine ⟨23940864355685299377245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255369219793976526690613 23940864355685299377245)
                  ·
                    rfl

theorem cell22_209811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 5].length) (baseStart_209811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209811 prefixEnd_209811 := by exact prefixLift 209811
  have htrace : WordTrace (prefixWord ++ tailWord_209811) baseStart_209811 baseEnd_209811 := by
    simpa [prefixWord, tailWord_209811, baseEnd_209811] using wordTrace_append hprefix tailTrace_209811
  have hstable : (prefixWord ++ tailWord_209811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209811).length < 2 ^ (prefixWord ++ tailWord_209811).sum := by decide
  have hdescent : baseEnd_209811 < baseStart_209811 := by decide
  rcases family_descends (prefixWord ++ tailWord_209811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209815 : List Nat := [1, 1, 3, 3, 1, 2, 1, 6, 1, 3]
def baseStart_209815 : Nat := 118140960795 + 209815 * 2 ^ 59
def prefixEnd_209815 : Nat := 4983230072969 + 3 ^ 40 * 209815 * 2
def baseEnd_209815 : Nat := 71823962348801221031723

theorem tailTrace_209815 : CollatzResearch.WordTrace tailWord_209815 prefixEnd_209815 71823962348801221031723 := by
  unfold tailWord_209815
  simp only [CollatzResearch.WordTrace]
  refine ⟨7652581734883563394254899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5101721156589042262836599 7652581734883563394254899)
  ·
    refine ⟨11478872602325345091382349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7652581734883563394254899 11478872602325345091382349)
    ·
      refine ⟨4304577225872004409268381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11478872602325345091382349 4304577225872004409268381)
      ·
        refine ⟨1614216459702001653475643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4304577225872004409268381 1614216459702001653475643)
        ·
          refine ⟨2421324689553002480213465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1614216459702001653475643 2421324689553002480213465)
          ·
            refine ⟨1815993517164751860160099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2421324689553002480213465 1815993517164751860160099)
            ·
              refine ⟨2723990275747127790240149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815993517164751860160099 2723990275747127790240149)
              ·
                refine ⟨127687044175646615167507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2723990275747127790240149 127687044175646615167507)
                ·
                  refine ⟨191530566263469922751261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127687044175646615167507 191530566263469922751261)
                  ·
                    refine ⟨71823962348801221031723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 191530566263469922751261 71823962348801221031723)
                    ·
                      rfl

theorem cell22_209815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_209815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209815 prefixEnd_209815 := by exact prefixLift 209815
  have htrace : WordTrace (prefixWord ++ tailWord_209815) baseStart_209815 baseEnd_209815 := by
    simpa [prefixWord, tailWord_209815, baseEnd_209815] using wordTrace_append hprefix tailTrace_209815
  have hstable : (prefixWord ++ tailWord_209815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209815).length < 2 ^ (prefixWord ++ tailWord_209815).sum := by decide
  have hdescent : baseEnd_209815 < baseStart_209815 := by decide
  rcases family_descends (prefixWord ++ tailWord_209815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209903 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 2, 4]
def baseStart_209903 : Nat := 118140960795 + 209903 * 2 ^ 59
def prefixEnd_209903 : Nat := 4983230072969 + 3 ^ 40 * 209903 * 2
def baseEnd_209903 : Nat := 71854086547198324831453

theorem tailTrace_209903 : CollatzResearch.WordTrace tailWord_209903 prefixEnd_209903 71854086547198324831453 := by
  unfold tailWord_209903
  simp only [CollatzResearch.WordTrace]
  refine ⟨7655791358564754423458363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5103860905709836282305575 7655791358564754423458363)
  ·
    refine ⟨11483687037847131635187545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7655791358564754423458363 11483687037847131635187545)
    ·
      refine ⟨8612765278385348726390659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11483687037847131635187545 8612765278385348726390659)
      ·
        refine ⟨12919147917578023089585989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8612765278385348726390659 12919147917578023089585989)
        ·
          refine ⟨2422340234545879329297373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12919147917578023089585989 2422340234545879329297373)
          ·
            refine ⟨908377587954704748486515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2422340234545879329297373 908377587954704748486515)
            ·
              refine ⟨1362566381932057122729773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908377587954704748486515 1362566381932057122729773)
              ·
                refine ⟨510962393224521421023665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1362566381932057122729773 510962393224521421023665)
                ·
                  refine ⟨383221794918391065767749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510962393224521421023665 383221794918391065767749)
                  ·
                    refine ⟨71854086547198324831453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 383221794918391065767749 71854086547198324831453)
                    ·
                      rfl

theorem cell22_209903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_209903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209903 prefixEnd_209903 := by exact prefixLift 209903
  have htrace : WordTrace (prefixWord ++ tailWord_209903) baseStart_209903 baseEnd_209903 := by
    simpa [prefixWord, tailWord_209903, baseEnd_209903] using wordTrace_append hprefix tailTrace_209903
  have hstable : (prefixWord ++ tailWord_209903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209903).length < 2 ^ (prefixWord ++ tailWord_209903).sum := by decide
  have hdescent : baseEnd_209903 < baseStart_209903 := by decide
  rcases family_descends (prefixWord ++ tailWord_209903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209918 : List Nat := [4, 2, 2, 2, 12]
def baseStart_209918 : Nat := 118140960795 + 209918 * 2 ^ 59
def prefixEnd_209918 : Nat := 4983230072969 + 3 ^ 40 * 209918 * 2
def baseEnd_209918 : Nat := 295716960303470311549

theorem tailTrace_209918 : CollatzResearch.WordTrace tailWord_209918 prefixEnd_209918 295716960303470311549 := by
  unfold tailWord_209918
  simp only [CollatzResearch.WordTrace]
  refine ⟨957042306688801498156801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5104225635673607990169605 957042306688801498156801)
  ·
    refine ⟨717781730016601123617601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 957042306688801498156801 717781730016601123617601)
    ·
      refine ⟨538336297512450842713201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 717781730016601123617601 538336297512450842713201)
      ·
        refine ⟨403752223134338132034901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538336297512450842713201 403752223134338132034901)
        ·
          refine ⟨295716960303470311549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 403752223134338132034901 295716960303470311549)
          ·
            rfl

theorem cell22_209918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 12].length) (baseStart_209918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209918 prefixEnd_209918 := by exact prefixLift 209918
  have htrace : WordTrace (prefixWord ++ tailWord_209918) baseStart_209918 baseEnd_209918 := by
    simpa [prefixWord, tailWord_209918, baseEnd_209918] using wordTrace_append hprefix tailTrace_209918
  have hstable : (prefixWord ++ tailWord_209918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209918).length < 2 ^ (prefixWord ++ tailWord_209918).sum := by decide
  have hdescent : baseEnd_209918 < baseStart_209918 := by decide
  rcases family_descends (prefixWord ++ tailWord_209918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209952 : List Nat := [2, 1, 1, 7, 1, 1, 3, 6]
def baseStart_209952 : Nat := 118140960795 + 209952 * 2 ^ 59
def prefixEnd_209952 : Nat := 4983230072969 + 3 ^ 40 * 209952 * 2
def baseEnd_209952 : Nat := 7985651138730947817367

theorem tailTrace_209952 : CollatzResearch.WordTrace tailWord_209952 prefixEnd_209952 7985651138730947817367 := by
  unfold tailWord_209952
  simp only [CollatzResearch.WordTrace]
  refine ⟨3828789267693617895996055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5105052356924823861328073 3828789267693617895996055)
  ·
    refine ⟨5743183901540426843994083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3828789267693617895996055 5743183901540426843994083)
    ·
      refine ⟨8614775852310640265991125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5743183901540426843994083 8614775852310640265991125)
      ·
        refine ⟨201908809038530631234167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 8614775852310640265991125 201908809038530631234167)
        ·
          refine ⟨302863213557795946851251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201908809038530631234167 302863213557795946851251)
          ·
            refine ⟨454294820336693920276877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302863213557795946851251 454294820336693920276877)
            ·
              refine ⟨170360557626260220103829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 454294820336693920276877 170360557626260220103829)
              ·
                refine ⟨7985651138730947817367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170360557626260220103829 7985651138730947817367)
                ·
                  rfl

theorem cell22_209952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 6].length) (baseStart_209952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209952 prefixEnd_209952 := by exact prefixLift 209952
  have htrace : WordTrace (prefixWord ++ tailWord_209952) baseStart_209952 baseEnd_209952 := by
    simpa [prefixWord, tailWord_209952, baseEnd_209952] using wordTrace_append hprefix tailTrace_209952
  have hstable : (prefixWord ++ tailWord_209952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209952).length < 2 ^ (prefixWord ++ tailWord_209952).sum := by decide
  have hdescent : baseEnd_209952 < baseStart_209952 := by decide
  rcases family_descends (prefixWord ++ tailWord_209952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209978 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_209978 : Nat := 118140960795 + 209978 * 2 ^ 59
def prefixEnd_209978 : Nat := 4983230072969 + 3 ^ 40 * 209978 * 2
def baseEnd_209978 : Nat := 71879760579923129206223

theorem tailTrace_209978 : CollatzResearch.WordTrace tailWord_209978 prefixEnd_209978 71879760579923129206223 := by
  unfold tailWord_209978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914631708323260558109647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5105684555528694821625725 1914631708323260558109647)
  ·
    refine ⟨2871947562484890837164471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1914631708323260558109647 2871947562484890837164471)
    ·
      refine ⟨4307921343727336255746707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2871947562484890837164471 4307921343727336255746707)
      ·
        refine ⟨6461882015591004383620061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4307921343727336255746707 6461882015591004383620061)
        ·
          refine ⟨2423205755846626643857523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6461882015591004383620061 2423205755846626643857523)
          ·
            refine ⟨3634808633769939965786285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423205755846626643857523 3634808633769939965786285)
            ·
              refine ⟨1363053237663727487169857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3634808633769939965786285 1363053237663727487169857)
              ·
                refine ⟨1022289928247795615377393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363053237663727487169857 1022289928247795615377393)
                ·
                  refine ⟨766717446185846711533045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1022289928247795615377393 766717446185846711533045)
                  ·
                    refine ⟨71879760579923129206223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 766717446185846711533045 71879760579923129206223)
                    ·
                      rfl

theorem cell22_209978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_209978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209978 prefixEnd_209978 := by exact prefixLift 209978
  have htrace : WordTrace (prefixWord ++ tailWord_209978) baseStart_209978 baseEnd_209978 := by
    simpa [prefixWord, tailWord_209978, baseEnd_209978] using wordTrace_append hprefix tailTrace_209978
  have hstable : (prefixWord ++ tailWord_209978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209978).length < 2 ^ (prefixWord ++ tailWord_209978).sum := by decide
  have hdescent : baseEnd_209978 < baseStart_209978 := by decide
  rcases family_descends (prefixWord ++ tailWord_209978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209980 : List Nat := [2, 2, 2, 2, 2, 2, 3, 2, 5]
def baseStart_209980 : Nat := 118140960795 + 209980 * 2 ^ 59
def prefixEnd_209980 : Nat := 4983230072969 + 3 ^ 40 * 209980 * 2
def baseEnd_209980 : Nat := 23960148406931930218739

theorem tailTrace_209980 : CollatzResearch.WordTrace tailWord_209980 prefixEnd_209980 23960148406931930218739 := by
  unfold tailWord_209980
  simp only [CollatzResearch.WordTrace]
  refine ⟨3829299889642898287005697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5105733186190531049340929 3829299889642898287005697)
  ·
    refine ⟨2871974917232173715254273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3829299889642898287005697 2871974917232173715254273)
    ·
      refine ⟨2153981187924130286440705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2871974917232173715254273 2153981187924130286440705)
      ·
        refine ⟨1615485890943097714830529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2153981187924130286440705 1615485890943097714830529)
        ·
          refine ⟨1211614418207323286122897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1615485890943097714830529 1211614418207323286122897)
          ·
            refine ⟨908710813655492464592173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1211614418207323286122897 908710813655492464592173)
            ·
              refine ⟨340766555120809674222065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 908710813655492464592173 340766555120809674222065)
              ·
                refine ⟨255574916340607255666549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340766555120809674222065 255574916340607255666549)
                ·
                  refine ⟨23960148406931930218739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255574916340607255666549 23960148406931930218739)
                  ·
                    rfl

theorem cell22_209980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_209980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209980 prefixEnd_209980 := by exact prefixLift 209980
  have htrace : WordTrace (prefixWord ++ tailWord_209980) baseStart_209980 baseEnd_209980 := by
    simpa [prefixWord, tailWord_209980, baseEnd_209980] using wordTrace_append hprefix tailTrace_209980
  have hstable : (prefixWord ++ tailWord_209980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209980).length < 2 ^ (prefixWord ++ tailWord_209980).sum := by decide
  have hdescent : baseEnd_209980 < baseStart_209980 := by decide
  rcases family_descends (prefixWord ++ tailWord_209980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209993 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 3, 4]
def baseStart_209993 : Nat := 118140960795 + 209993 * 2 ^ 59
def prefixEnd_209993 : Nat := 4983230072969 + 3 ^ 40 * 209993 * 2
def baseEnd_209993 : Nat := 71884895386468090081177

theorem tailTrace_209993 : CollatzResearch.WordTrace tailWord_209993 prefixEnd_209993 71884895386468090081177 := by
  unfold tailWord_209993
  simp only [CollatzResearch.WordTrace]
  refine ⟨7659073928238699794234633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5106049285492466529489755 7659073928238699794234633)
  ·
    refine ⟨5744305446179024845675975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7659073928238699794234633 5744305446179024845675975)
    ·
      refine ⟨8616458169268537268513963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5744305446179024845675975 8616458169268537268513963)
      ·
        refine ⟨12924687253902805902770945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8616458169268537268513963 12924687253902805902770945)
        ·
          refine ⟨9693515440427104427078209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12924687253902805902770945 9693515440427104427078209)
          ·
            refine ⟨7270136580320328320308657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9693515440427104427078209 7270136580320328320308657)
            ·
              refine ⟨5452602435240246240231493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7270136580320328320308657 5452602435240246240231493)
              ·
                refine ⟨1022362956607546170043405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5452602435240246240231493 1022362956607546170043405)
                ·
                  refine ⟨383386108727829813766277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022362956607546170043405 383386108727829813766277)
                  ·
                    refine ⟨71884895386468090081177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 383386108727829813766277 71884895386468090081177)
                    ·
                      rfl

theorem cell22_209993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_209993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_209993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_209993 prefixEnd_209993 := by exact prefixLift 209993
  have htrace : WordTrace (prefixWord ++ tailWord_209993) baseStart_209993 baseEnd_209993 := by
    simpa [prefixWord, tailWord_209993, baseEnd_209993] using wordTrace_append hprefix tailTrace_209993
  have hstable : (prefixWord ++ tailWord_209993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209993).length < 2 ^ (prefixWord ++ tailWord_209993).sum := by decide
  have hdescent : baseEnd_209993 < baseStart_209993 := by decide
  rcases family_descends (prefixWord ++ tailWord_209993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210008 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 6]
def baseStart_210008 : Nat := 118140960795 + 210008 * 2 ^ 59
def prefixEnd_210008 : Nat := 4983230072969 + 3 ^ 40 * 210008 * 2
def baseEnd_210008 : Nat := 23963343397671016985377

theorem tailTrace_210008 : CollatzResearch.WordTrace tailWord_210008 prefixEnd_210008 23963343397671016985377 := by
  unfold tailWord_210008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3829810511592178678015339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5106414015456238237353785 3829810511592178678015339)
  ·
    refine ⟨5744715767388268017023009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3829810511592178678015339 5744715767388268017023009)
    ·
      refine ⟨4308536825541201012767257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5744715767388268017023009 4308536825541201012767257)
      ·
        refine ⟨3231402619155900759575443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4308536825541201012767257 3231402619155900759575443)
        ·
          refine ⟨4847103928733851139363165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3231402619155900759575443 4847103928733851139363165)
          ·
            refine ⟨1817663973275194177261187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4847103928733851139363165 1817663973275194177261187)
            ·
              refine ⟨2726495959912791265891781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817663973275194177261187 2726495959912791265891781)
              ·
                refine ⟨511217992483648362354709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2726495959912791265891781 511217992483648362354709)
                ·
                  refine ⟨23963343397671016985377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 511217992483648362354709 23963343397671016985377)
                  ·
                    rfl

theorem cell22_210008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_210008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210008 prefixEnd_210008 := by exact prefixLift 210008
  have htrace : WordTrace (prefixWord ++ tailWord_210008) baseStart_210008 baseEnd_210008 := by
    simpa [prefixWord, tailWord_210008, baseEnd_210008] using wordTrace_append hprefix tailTrace_210008
  have hstable : (prefixWord ++ tailWord_210008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210008).length < 2 ^ (prefixWord ++ tailWord_210008).sum := by decide
  have hdescent : baseEnd_210008 < baseStart_210008 := by decide
  rcases family_descends (prefixWord ++ tailWord_210008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210040 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 4, 3]
def baseStart_210040 : Nat := 118140960795 + 210040 * 2 ^ 59
def prefixEnd_210040 : Nat := 4983230072969 + 3 ^ 40 * 210040 * 2
def baseEnd_210040 : Nat := 71900984446975634156033

theorem tailTrace_210040 : CollatzResearch.WordTrace tailWord_210040 prefixEnd_210040 71900984446975634156033 := by
  unfold tailWord_210040
  simp only [CollatzResearch.WordTrace]
  refine ⟨3830394079534213410597787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5107192106045617880797049 3830394079534213410597787)
  ·
    refine ⟨5745591119301320115896681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3830394079534213410597787 5745591119301320115896681)
    ·
      refine ⟨4309193339475990086922511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5745591119301320115896681 4309193339475990086922511)
      ·
        refine ⟨6463790009213985130383767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4309193339475990086922511 6463790009213985130383767)
        ·
          refine ⟨9695685013820977695575651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6463790009213985130383767 9695685013820977695575651)
          ·
            refine ⟨14543527520731466543363477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9695685013820977695575651 14543527520731466543363477)
            ·
              refine ⟨681727852534287494220163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14543527520731466543363477 681727852534287494220163)
              ·
                refine ⟨1022591778801431241330245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681727852534287494220163 1022591778801431241330245)
                ·
                  refine ⟨191735958525268357749421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022591778801431241330245 191735958525268357749421)
                  ·
                    refine ⟨71900984446975634156033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 191735958525268357749421 71900984446975634156033)
                    ·
                      rfl

theorem cell22_210040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_210040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210040 prefixEnd_210040 := by exact prefixLift 210040
  have htrace : WordTrace (prefixWord ++ tailWord_210040) baseStart_210040 baseEnd_210040 := by
    simpa [prefixWord, tailWord_210040, baseEnd_210040] using wordTrace_append hprefix tailTrace_210040
  have hstable : (prefixWord ++ tailWord_210040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210040).length < 2 ^ (prefixWord ++ tailWord_210040).sum := by decide
  have hdescent : baseEnd_210040 < baseStart_210040 := by decide
  rcases family_descends (prefixWord ++ tailWord_210040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210057 : List Nat := [1, 2, 1, 1, 4, 4, 1, 3, 2, 3]
def baseStart_210057 : Nat := 118140960795 + 210057 * 2 ^ 59
def prefixEnd_210057 : Nat := 4983230072969 + 3 ^ 40 * 210057 * 2
def baseEnd_210057 : Nat := 71906803894393256480981

theorem tailTrace_210057 : CollatzResearch.WordTrace tailWord_210057 prefixEnd_210057 71906803894393256480981 := by
  unfold tailWord_210057
  simp only [CollatzResearch.WordTrace]
  refine ⟨7661408200006838724564425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5107605466671225816376283 7661408200006838724564425)
  ·
    refine ⟨5746056150005129043423319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7661408200006838724564425 5746056150005129043423319)
    ·
      refine ⟨8619084225007693565134979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5746056150005129043423319 8619084225007693565134979)
      ·
        refine ⟨12928626337511540347702469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8619084225007693565134979 12928626337511540347702469)
        ·
          refine ⟨2424117438283413815194213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12928626337511540347702469 2424117438283413815194213)
          ·
            refine ⟨454522019678140090348915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2424117438283413815194213 454522019678140090348915)
            ·
              refine ⟨681783029517210135523373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454522019678140090348915 681783029517210135523373)
              ·
                refine ⟨255668636068953800821265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 681783029517210135523373 255668636068953800821265)
                ·
                  refine ⟨191751477051715350615949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255668636068953800821265 191751477051715350615949)
                  ·
                    refine ⟨71906803894393256480981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 191751477051715350615949 71906803894393256480981)
                    ·
                      rfl

theorem cell22_210057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 3].length) (baseStart_210057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210057 prefixEnd_210057 := by exact prefixLift 210057
  have htrace : WordTrace (prefixWord ++ tailWord_210057) baseStart_210057 baseEnd_210057 := by
    simpa [prefixWord, tailWord_210057, baseEnd_210057] using wordTrace_append hprefix tailTrace_210057
  have hstable : (prefixWord ++ tailWord_210057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210057).length < 2 ^ (prefixWord ++ tailWord_210057).sum := by decide
  have hdescent : baseEnd_210057 < baseStart_210057 := by decide
  rcases family_descends (prefixWord ++ tailWord_210057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210072 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 2, 4]
def baseStart_210072 : Nat := 118140960795 + 210072 * 2 ^ 59
def prefixEnd_210072 : Nat := 4983230072969 + 3 ^ 40 * 210072 * 2
def baseEnd_210072 : Nat := 71911938700938217355935

theorem tailTrace_210072 : CollatzResearch.WordTrace tailWord_210072 prefixEnd_210072 71911938700938217355935 := by
  unfold tailWord_210072
  simp only [CollatzResearch.WordTrace]
  refine ⟨3830977647476248143180235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5107970196634997524240313 3830977647476248143180235)
  ·
    refine ⟨5746466471214372214770353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3830977647476248143180235 5746466471214372214770353)
    ·
      refine ⟨4309849853410779161077765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5746466471214372214770353 4309849853410779161077765)
      ·
        refine ⟨808096847514521092702081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4309849853410779161077765 808096847514521092702081)
        ·
          refine ⟨606072635635890819526561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808096847514521092702081 606072635635890819526561)
          ·
            refine ⟨454554476726918114644921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 606072635635890819526561 454554476726918114644921)
            ·
              refine ⟨340915857545188585983691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454554476726918114644921 340915857545188585983691)
              ·
                refine ⟨511373786317782878975537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340915857545188585983691 511373786317782878975537)
                ·
                  refine ⟨383530339738337159231653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511373786317782878975537 383530339738337159231653)
                  ·
                    refine ⟨71911938700938217355935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 383530339738337159231653 71911938700938217355935)
                    ·
                      rfl

theorem cell22_210072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_210072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210072 prefixEnd_210072 := by exact prefixLift 210072
  have htrace : WordTrace (prefixWord ++ tailWord_210072) baseStart_210072 baseEnd_210072 := by
    simpa [prefixWord, tailWord_210072, baseEnd_210072] using wordTrace_append hprefix tailTrace_210072
  have hstable : (prefixWord ++ tailWord_210072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210072).length < 2 ^ (prefixWord ++ tailWord_210072).sum := by decide
  have hdescent : baseEnd_210072 < baseStart_210072 := by decide
  rcases family_descends (prefixWord ++ tailWord_210072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210083 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 4, 6]
def baseStart_210083 : Nat := 118140960795 + 210083 * 2 ^ 59
def prefixEnd_210083 : Nat := 4983230072969 + 3 ^ 40 * 210083 * 2
def baseEnd_210083 : Nat := 71915704225737855330901

theorem tailTrace_210083 : CollatzResearch.WordTrace tailWord_210083 prefixEnd_210083 71915704225737855330901 := by
  unfold tailWord_210083
  simp only [CollatzResearch.WordTrace]
  refine ⟨7662356497912645165010903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5108237665275096776673935 7662356497912645165010903)
  ·
    refine ⟨11493534746868967747516355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7662356497912645165010903 11493534746868967747516355)
    ·
      refine ⟨17240302120303451621274533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11493534746868967747516355 17240302120303451621274533)
      ·
        refine ⟨3232556647556897178988975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17240302120303451621274533 3232556647556897178988975)
        ·
          refine ⟨4848834971335345768483463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3232556647556897178988975 4848834971335345768483463)
          ·
            refine ⟨7273252457003018652725195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848834971335345768483463 7273252457003018652725195)
            ·
              refine ⟨10909878685504527979087793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7273252457003018652725195 10909878685504527979087793)
              ·
                refine ⟨8182409014128395984315845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10909878685504527979087793 8182409014128395984315845)
                ·
                  refine ⟨1534201690149074247059221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8182409014128395984315845 1534201690149074247059221)
                  ·
                    refine ⟨71915704225737855330901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1534201690149074247059221 71915704225737855330901)
                    ·
                      rfl

theorem cell22_210083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_210083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210083 prefixEnd_210083 := by exact prefixLift 210083
  have htrace : WordTrace (prefixWord ++ tailWord_210083) baseStart_210083 baseEnd_210083 := by
    simpa [prefixWord, tailWord_210083, baseEnd_210083] using wordTrace_append hprefix tailTrace_210083
  have hstable : (prefixWord ++ tailWord_210083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210083).length < 2 ^ (prefixWord ++ tailWord_210083).sum := by decide
  have hdescent : baseEnd_210083 < baseStart_210083 := by decide
  rcases family_descends (prefixWord ++ tailWord_210083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210093 : List Nat := [1, 5, 2, 1, 4, 1, 2, 2, 4]
def baseStart_210093 : Nat := 118140960795 + 210093 * 2 ^ 59
def prefixEnd_210093 : Nat := 4983230072969 + 3 ^ 40 * 210093 * 2
def baseEnd_210093 : Nat := 23973042476700387526957

theorem tailTrace_210093 : CollatzResearch.WordTrace tailWord_210093 prefixEnd_210093 23973042476700387526957 := by
  unfold tailWord_210093
  simp only [CollatzResearch.WordTrace]
  refine ⟨7662721227876416872874933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5108480818584277915249955 7662721227876416872874933)
  ·
    refine ⟨718380115113414081832025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7662721227876416872874933 718380115113414081832025)
    ·
      refine ⟨538785086335060561374019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 718380115113414081832025 538785086335060561374019)
      ·
        refine ⟨808177629502590842061029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538785086335060561374019 808177629502590842061029)
        ·
          refine ⟨151533305531735782886443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 808177629502590842061029 151533305531735782886443)
          ·
            refine ⟨227299958297603674329665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151533305531735782886443 227299958297603674329665)
            ·
              refine ⟨170474968723202755747249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227299958297603674329665 170474968723202755747249)
              ·
                refine ⟨127856226542402066810437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170474968723202755747249 127856226542402066810437)
                ·
                  refine ⟨23973042476700387526957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127856226542402066810437 23973042476700387526957)
                  ·
                    rfl

theorem cell22_210093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_210093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210093 prefixEnd_210093 := by exact prefixLift 210093
  have htrace : WordTrace (prefixWord ++ tailWord_210093) baseStart_210093 baseEnd_210093 := by
    simpa [prefixWord, tailWord_210093, baseEnd_210093] using wordTrace_append hprefix tailTrace_210093
  have hstable : (prefixWord ++ tailWord_210093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210093).length < 2 ^ (prefixWord ++ tailWord_210093).sum := by decide
  have hdescent : baseEnd_210093 < baseStart_210093 := by decide
  rcases family_descends (prefixWord ++ tailWord_210093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210130 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_210130 : Nat := 118140960795 + 210130 * 2 ^ 59
def prefixEnd_210130 : Nat := 4983230072969 + 3 ^ 40 * 210130 * 2
def baseEnd_210130 : Nat := 71931793286245399405757

theorem tailTrace_210130 : CollatzResearch.WordTrace tailWord_210130 prefixEnd_210130 71931793286245399405757 := by
  unfold tailWord_210130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1916017682185593047992961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5109380485828248127981229 1916017682185593047992961)
  ·
    refine ⟨1437013261639194785994721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1916017682185593047992961 1437013261639194785994721)
    ·
      refine ⟨1077759946229396089496041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1437013261639194785994721 1077759946229396089496041)
      ·
        refine ⟨808319959672047067122031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1077759946229396089496041 808319959672047067122031)
        ·
          refine ⟨1212479939508070600683047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808319959672047067122031 1212479939508070600683047)
          ·
            refine ⟨1818719909262105901024571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212479939508070600683047 1818719909262105901024571)
            ·
              refine ⟨2728079863893158851536857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1818719909262105901024571 2728079863893158851536857)
              ·
                refine ⟨2046059897919869138652643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2728079863893158851536857 2046059897919869138652643)
                ·
                  refine ⟨3069089846879803707978965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046059897919869138652643 3069089846879803707978965)
                  ·
                    refine ⟨71931793286245399405757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3069089846879803707978965 71931793286245399405757)
                    ·
                      rfl

theorem cell22_210130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_210130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210130 prefixEnd_210130 := by exact prefixLift 210130
  have htrace : WordTrace (prefixWord ++ tailWord_210130) baseStart_210130 baseEnd_210130 := by
    simpa [prefixWord, tailWord_210130, baseEnd_210130] using wordTrace_append hprefix tailTrace_210130
  have hstable : (prefixWord ++ tailWord_210130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210130).length < 2 ^ (prefixWord ++ tailWord_210130).sum := by decide
  have hdescent : baseEnd_210130 < baseStart_210130 := by decide
  rcases family_descends (prefixWord ++ tailWord_210130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210136 : List Nat := [2, 1, 2, 2, 5, 1, 2, 3, 1, 3]
def baseStart_210136 : Nat := 118140960795 + 210136 * 2 ^ 59
def prefixEnd_210136 : Nat := 4983230072969 + 3 ^ 40 * 210136 * 2
def baseEnd_210136 : Nat := 71933847208863383755739

theorem tailTrace_210136 : CollatzResearch.WordTrace tailWord_210136 prefixEnd_210136 71933847208863383755739 := by
  unfold tailWord_210136
  simp only [CollatzResearch.WordTrace]
  refine ⟨3832144783360317608345131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5109526377813756811126841 3832144783360317608345131)
  ·
    refine ⟨5748217175040476412517697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3832144783360317608345131 5748217175040476412517697)
    ·
      refine ⟨4311162881280357309388273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5748217175040476412517697 4311162881280357309388273)
      ·
        refine ⟨3233372160960267982041205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4311162881280357309388273 3233372160960267982041205)
        ·
          refine ⟨303128640090025123316363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3233372160960267982041205 303128640090025123316363)
          ·
            refine ⟨454692960135037684974545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303128640090025123316363 454692960135037684974545)
            ·
              refine ⟨341019720101278263730909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454692960135037684974545 341019720101278263730909)
              ·
                refine ⟨127882395037979348899091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341019720101278263730909 127882395037979348899091)
                ·
                  refine ⟨191823592556969023348637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127882395037979348899091 191823592556969023348637)
                  ·
                    refine ⟨71933847208863383755739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 191823592556969023348637 71933847208863383755739)
                    ·
                      rfl

theorem cell22_210136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_210136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210136 prefixEnd_210136 := by exact prefixLift 210136
  have htrace : WordTrace (prefixWord ++ tailWord_210136) baseStart_210136 baseEnd_210136 := by
    simpa [prefixWord, tailWord_210136, baseEnd_210136] using wordTrace_append hprefix tailTrace_210136
  have hstable : (prefixWord ++ tailWord_210136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210136).length < 2 ^ (prefixWord ++ tailWord_210136).sum := by decide
  have hdescent : baseEnd_210136 < baseStart_210136 := by decide
  rcases family_descends (prefixWord ++ tailWord_210136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210149 : List Nat := [1, 3, 1, 4, 3, 2, 1, 2, 5]
def baseStart_210149 : Nat := 118140960795 + 210149 * 2 ^ 59
def prefixEnd_210149 : Nat := 4983230072969 + 3 ^ 40 * 210149 * 2
def baseEnd_210149 : Nat := 23979432458178561060233

theorem tailTrace_210149 : CollatzResearch.WordTrace tailWord_210149 prefixEnd_210149 23979432458178561060233 := by
  unfold tailWord_210149
  simp only [CollatzResearch.WordTrace]
  refine ⟨7664763715673538436913501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5109842477115692291275667 7664763715673538436913501)
  ·
    refine ⟨2874286393377576913842563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7664763715673538436913501 2874286393377576913842563)
    ·
      refine ⟨4311429590066365370763845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2874286393377576913842563 4311429590066365370763845)
      ·
        refine ⟨808393048137443507018221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4311429590066365370763845 808393048137443507018221)
        ·
          refine ⟨303147393051541315131833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 808393048137443507018221 303147393051541315131833)
          ·
            refine ⟨227360544788655986348875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303147393051541315131833 227360544788655986348875)
            ·
              refine ⟨341040817182983979523313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227360544788655986348875 341040817182983979523313)
              ·
                refine ⟨255780612887237984642485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341040817182983979523313 255780612887237984642485)
                ·
                  refine ⟨23979432458178561060233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255780612887237984642485 23979432458178561060233)
                  ·
                    rfl

theorem cell22_210149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_210149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210149 prefixEnd_210149 := by exact prefixLift 210149
  have htrace : WordTrace (prefixWord ++ tailWord_210149) baseStart_210149 baseEnd_210149 := by
    simpa [prefixWord, tailWord_210149, baseEnd_210149] using wordTrace_append hprefix tailTrace_210149
  have hstable : (prefixWord ++ tailWord_210149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210149).length < 2 ^ (prefixWord ++ tailWord_210149).sum := by decide
  have hdescent : baseEnd_210149 < baseStart_210149 := by decide
  rcases family_descends (prefixWord ++ tailWord_210149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210226 : List Nat := [3, 2, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_210226 : Nat := 118140960795 + 210226 * 2 ^ 59
def prefixEnd_210226 : Nat := 4983230072969 + 3 ^ 40 * 210226 * 2
def baseEnd_210226 : Nat := 71964656048133149005463

theorem tailTrace_210226 : CollatzResearch.WordTrace tailWord_210226 prefixEnd_210226 71964656048133149005463 := by
  unfold tailWord_210226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1916893034098645146866633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5111714757596387058311021 1916893034098645146866633)
  ·
    refine ⟨1437669775573983860149975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1916893034098645146866633 1437669775573983860149975)
    ·
      refine ⟨2156504663360975790224963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1437669775573983860149975 2156504663360975790224963)
      ·
        refine ⟨3234756995041463685337445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156504663360975790224963 3234756995041463685337445)
        ·
          refine ⟨606516936570274441000771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3234756995041463685337445 606516936570274441000771)
          ·
            refine ⟨909775404855411661501157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606516936570274441000771 909775404855411661501157)
            ·
              refine ⟨170582888410389686531467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 909775404855411661501157 170582888410389686531467)
              ·
                refine ⟨255874332615584529797201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170582888410389686531467 255874332615584529797201)
                ·
                  refine ⟨191905749461688397347901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255874332615584529797201 191905749461688397347901)
                  ·
                    refine ⟨71964656048133149005463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 191905749461688397347901 71964656048133149005463)
                    ·
                      rfl

theorem cell22_210226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_210226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210226 prefixEnd_210226 := by exact prefixLift 210226
  have htrace : WordTrace (prefixWord ++ tailWord_210226) baseStart_210226 baseEnd_210226 := by
    simpa [prefixWord, tailWord_210226, baseEnd_210226] using wordTrace_append hprefix tailTrace_210226
  have hstable : (prefixWord ++ tailWord_210226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210226).length < 2 ^ (prefixWord ++ tailWord_210226).sum := by decide
  have hdescent : baseEnd_210226 < baseStart_210226 := by decide
  rcases family_descends (prefixWord ++ tailWord_210226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210230 : List Nat := [5, 1, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_210230 : Nat := 118140960795 + 210230 * 2 ^ 59
def prefixEnd_210230 : Nat := 4983230072969 + 3 ^ 40 * 210230 * 2
def baseEnd_210230 : Nat := 71966025329878471905451

theorem tailTrace_210230 : CollatzResearch.WordTrace tailWord_210230 prefixEnd_210230 71966025329878471905451 := by
  unfold tailWord_210230
  simp only [CollatzResearch.WordTrace]
  refine ⟨479232376773755579413259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5111812018920059513741429 479232376773755579413259)
  ·
    refine ⟨718848565160633369119889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 479232376773755579413259 718848565160633369119889)
    ·
      refine ⟨539136423870475026839917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 718848565160633369119889 539136423870475026839917)
      ·
        refine ⟨202176158951428135064969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 539136423870475026839917 202176158951428135064969)
        ·
          refine ⟨151632119213571101298727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202176158951428135064969 151632119213571101298727)
          ·
            refine ⟨227448178820356651948091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151632119213571101298727 227448178820356651948091)
            ·
              refine ⟨341172268230534977922137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227448178820356651948091 341172268230534977922137)
              ·
                refine ⟨255879201172901233441603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341172268230534977922137 255879201172901233441603)
                ·
                  refine ⟨383818801759351850162405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255879201172901233441603 383818801759351850162405)
                  ·
                    refine ⟨71966025329878471905451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 383818801759351850162405 71966025329878471905451)
                    ·
                      rfl

theorem cell22_210230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_210230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210230 prefixEnd_210230 := by exact prefixLift 210230
  have htrace : WordTrace (prefixWord ++ tailWord_210230) baseStart_210230 baseEnd_210230 := by
    simpa [prefixWord, tailWord_210230, baseEnd_210230] using wordTrace_append hprefix tailTrace_210230
  have hstable : (prefixWord ++ tailWord_210230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210230).length < 2 ^ (prefixWord ++ tailWord_210230).sum := by decide
  have hdescent : baseEnd_210230 < baseStart_210230 := by decide
  rcases family_descends (prefixWord ++ tailWord_210230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210250 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 9]
def baseStart_210250 : Nat := 118140960795 + 210250 * 2 ^ 59
def prefixEnd_210250 : Nat := 4983230072969 + 3 ^ 40 * 210250 * 2
def baseEnd_210250 : Nat := 23990957246201695468463

theorem tailTrace_210250 : CollatzResearch.WordTrace tailWord_210250 prefixEnd_210250 23990957246201695468463 := by
  unfold tailWord_210250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1917111872076908171585051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5112298325538421790893469 1917111872076908171585051)
  ·
    refine ⟨2875667808115362257377577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1917111872076908171585051 2875667808115362257377577)
    ·
      refine ⟨2156750856086521693033183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2875667808115362257377577 2156750856086521693033183)
      ·
        refine ⟨3235126284129782539549775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156750856086521693033183 3235126284129782539549775)
        ·
          refine ⟨4852689426194673809324663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235126284129782539549775 4852689426194673809324663)
          ·
            refine ⟨7279034139292010713986995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4852689426194673809324663 7279034139292010713986995)
            ·
              refine ⟨10918551208938016070980493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7279034139292010713986995 10918551208938016070980493)
              ·
                refine ⟨4094456703351756026617685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10918551208938016070980493 4094456703351756026617685)
                ·
                  refine ⟨23990957246201695468463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4094456703351756026617685 23990957246201695468463)
                  ·
                    rfl

theorem cell22_210250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_210250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210250 prefixEnd_210250 := by exact prefixLift 210250
  have htrace : WordTrace (prefixWord ++ tailWord_210250) baseStart_210250 baseEnd_210250 := by
    simpa [prefixWord, tailWord_210250, baseEnd_210250] using wordTrace_append hprefix tailTrace_210250
  have hstable : (prefixWord ++ tailWord_210250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210250).length < 2 ^ (prefixWord ++ tailWord_210250).sum := by decide
  have hdescent : baseEnd_210250 < baseStart_210250 := by decide
  rcases family_descends (prefixWord ++ tailWord_210250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210297 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 3, 4]
def baseStart_210297 : Nat := 118140960795 + 210297 * 2 ^ 59
def prefixEnd_210297 : Nat := 4983230072969 + 3 ^ 40 * 210297 * 2
def baseEnd_210297 : Nat := 71988960799112630480245

theorem tailTrace_210297 : CollatzResearch.WordTrace tailWord_210297 prefixEnd_210297 71988960799112630480245 := by
  unfold tailWord_210297
  simp only [CollatzResearch.WordTrace]
  refine ⟨7670161719137359713301145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5113441146091573142200763 7670161719137359713301145)
  ·
    refine ⟨5752621289353019784975859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7670161719137359713301145 5752621289353019784975859)
    ·
      refine ⟨8628931934029529677463789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5752621289353019784975859 8628931934029529677463789)
      ·
        refine ⟨3235849475261073629048921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8628931934029529677463789 3235849475261073629048921)
        ·
          refine ⟨2426887106445805221786691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3235849475261073629048921 2426887106445805221786691)
          ·
            refine ⟨3640330659668707832680037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426887106445805221786691 3640330659668707832680037)
            ·
              refine ⟨682561998687882718627507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3640330659668707832680037 682561998687882718627507)
              ·
                refine ⟨1023842998031824077941261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682561998687882718627507 1023842998031824077941261)
                ·
                  refine ⟨383941124261934029227973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023842998031824077941261 383941124261934029227973)
                  ·
                    refine ⟨71988960799112630480245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 383941124261934029227973 71988960799112630480245)
                    ·
                      rfl

theorem cell22_210297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_210297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210297 prefixEnd_210297 := by exact prefixLift 210297
  have htrace : WordTrace (prefixWord ++ tailWord_210297) baseStart_210297 baseEnd_210297 := by
    simpa [prefixWord, tailWord_210297, baseEnd_210297] using wordTrace_append hprefix tailTrace_210297
  have hstable : (prefixWord ++ tailWord_210297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210297).length < 2 ^ (prefixWord ++ tailWord_210297).sum := by decide
  have hdescent : baseEnd_210297 < baseStart_210297 := by decide
  rcases family_descends (prefixWord ++ tailWord_210297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210318 : List Nat := [4, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_210318 : Nat := 118140960795 + 210318 * 2 ^ 59
def prefixEnd_210318 : Nat := 4983230072969 + 3 ^ 40 * 210318 * 2
def baseEnd_210318 : Nat := 23998716509425191901727

theorem tailTrace_210318 : CollatzResearch.WordTrace tailWord_210318 prefixEnd_210318 23998716509425191901727 := by
  unfold tailWord_210318
  simp only [CollatzResearch.WordTrace]
  refine ⟨958865956507660037476951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5113951768040853533210405 958865956507660037476951)
  ·
    refine ⟨1438298934761490056215427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 958865956507660037476951 1438298934761490056215427)
    ·
      refine ⟨2157448402142235084323141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1438298934761490056215427 2157448402142235084323141)
      ·
        refine ⟨404521575401669078310589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2157448402142235084323141 404521575401669078310589)
        ·
          refine ⟨151695590775625904366471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404521575401669078310589 151695590775625904366471)
          ·
            refine ⟨227543386163438856549707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151695590775625904366471 227543386163438856549707)
            ·
              refine ⟨341315079245158284824561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227543386163438856549707 341315079245158284824561)
              ·
                refine ⟨255986309433868713618421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341315079245158284824561 255986309433868713618421)
                ·
                  refine ⟨23998716509425191901727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255986309433868713618421 23998716509425191901727)
                  ·
                    rfl

theorem cell22_210318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_210318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210318 prefixEnd_210318 := by exact prefixLift 210318
  have htrace : WordTrace (prefixWord ++ tailWord_210318) baseStart_210318 baseEnd_210318 := by
    simpa [prefixWord, tailWord_210318, baseEnd_210318] using wordTrace_append hprefix tailTrace_210318
  have hstable : (prefixWord ++ tailWord_210318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210318).length < 2 ^ (prefixWord ++ tailWord_210318).sum := by decide
  have hdescent : baseEnd_210318 < baseStart_210318 := by decide
  rcases family_descends (prefixWord ++ tailWord_210318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210329 : List Nat := [1, 2, 1, 2, 1, 5, 2, 4, 4]
def baseStart_210329 : Nat := 118140960795 + 210329 * 2 ^ 59
def prefixEnd_210329 : Nat := 4983230072969 + 3 ^ 40 * 210329 * 2
def baseEnd_210329 : Nat := 23999971684358404560049

theorem tailTrace_210329 : CollatzResearch.WordTrace tailWord_210329 prefixEnd_210329 23999971684358404560049 := by
  unfold tailWord_210329
  simp only [CollatzResearch.WordTrace]
  refine ⟨7671328855021429178466041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5114219236680952785644027 7671328855021429178466041)
  ·
    refine ⟨5753496641266071883849531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7671328855021429178466041 5753496641266071883849531)
    ·
      refine ⟨8630244961899107825774297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5753496641266071883849531 8630244961899107825774297)
      ·
        refine ⟨6472683721424330869330723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8630244961899107825774297 6472683721424330869330723)
        ·
          refine ⟨9709025582136496303996085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472683721424330869330723 9709025582136496303996085)
          ·
            refine ⟨910221148325296528499633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9709025582136496303996085 910221148325296528499633)
            ·
              refine ⟨682665861243972396374725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910221148325296528499633 682665861243972396374725)
              ·
                refine ⟨127999848983244824320261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 682665861243972396374725 127999848983244824320261)
                ·
                  refine ⟨23999971684358404560049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127999848983244824320261 23999971684358404560049)
                  ·
                    rfl

theorem cell22_210329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 4].length) (baseStart_210329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210329 prefixEnd_210329 := by exact prefixLift 210329
  have htrace : WordTrace (prefixWord ++ tailWord_210329) baseStart_210329 baseEnd_210329 := by
    simpa [prefixWord, tailWord_210329, baseEnd_210329] using wordTrace_append hprefix tailTrace_210329
  have hstable : (prefixWord ++ tailWord_210329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210329).length < 2 ^ (prefixWord ++ tailWord_210329).sum := by decide
  have hdescent : baseEnd_210329 < baseStart_210329 := by decide
  rcases family_descends (prefixWord ++ tailWord_210329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210464 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 8]
def baseStart_210464 : Nat := 118140960795 + 210464 * 2 ^ 59
def prefixEnd_210464 : Nat := 4983230072969 + 3 ^ 40 * 210464 * 2
def baseEnd_210464 : Nat := 24015376103993287184911

theorem tailTrace_210464 : CollatzResearch.WordTrace tailWord_210464 prefixEnd_210464 24015376103993287184911 := by
  unfold tailWord_210464
  simp only [CollatzResearch.WordTrace]
  refine ⟨3838126354766173617315223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5117501806354898156420297 3838126354766173617315223)
  ·
    refine ⟨5757189532149260425972835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3838126354766173617315223 5757189532149260425972835)
    ·
      refine ⟨8635784298223890638959253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5757189532149260425972835 8635784298223890638959253)
      ·
        refine ⟨404802388979244873701215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8635784298223890638959253 404802388979244873701215)
        ·
          refine ⟨607203583468867310551823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404802388979244873701215 607203583468867310551823)
          ·
            refine ⟨910805375203300965827735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607203583468867310551823 910805375203300965827735)
            ·
              refine ⟨1366208062804951448741603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910805375203300965827735 1366208062804951448741603)
              ·
                refine ⟨2049312094207427173112405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366208062804951448741603 2049312094207427173112405)
                ·
                  refine ⟨24015376103993287184911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2049312094207427173112405 24015376103993287184911)
                  ·
                    rfl

theorem cell22_210464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_210464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210464 prefixEnd_210464 := by exact prefixLift 210464
  have htrace : WordTrace (prefixWord ++ tailWord_210464) baseStart_210464 baseEnd_210464 := by
    simpa [prefixWord, tailWord_210464, baseEnd_210464] using wordTrace_append hprefix tailTrace_210464
  have hstable : (prefixWord ++ tailWord_210464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210464).length < 2 ^ (prefixWord ++ tailWord_210464).sum := by decide
  have hdescent : baseEnd_210464 < baseStart_210464 := by decide
  rcases family_descends (prefixWord ++ tailWord_210464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210483 : List Nat := [1, 1, 1, 2, 4, 5, 2, 1, 1, 4]
def baseStart_210483 : Nat := 118140960795 + 210483 * 2 ^ 59
def prefixEnd_210483 : Nat := 4983230072969 + 3 ^ 40 * 210483 * 2
def baseEnd_210483 : Nat := 72052632400270145329675

theorem tailTrace_210483 : CollatzResearch.WordTrace tailWord_210483 prefixEnd_210483 72052632400270145329675 := by
  unfold tailWord_210483
  simp only [CollatzResearch.WordTrace]
  refine ⟨7676945696463513479572103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5117963797642342319714735 7676945696463513479572103)
  ·
    refine ⟨11515418544695270219358155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7676945696463513479572103 11515418544695270219358155)
    ·
      refine ⟨17273127817042905329037233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11515418544695270219358155 17273127817042905329037233)
      ·
        refine ⟨12954845862782178996777925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17273127817042905329037233 12954845862782178996777925)
        ·
          refine ⟨2429033599271658561895861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12954845862782178996777925 2429033599271658561895861)
          ·
            refine ⟨227721899931717990177737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2429033599271658561895861 227721899931717990177737)
            ·
              refine ⟨170791424948788492633303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227721899931717990177737 170791424948788492633303)
              ·
                refine ⟨256187137423182738949955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170791424948788492633303 256187137423182738949955)
                ·
                  refine ⟨384280706134774108424933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256187137423182738949955 384280706134774108424933)
                  ·
                    refine ⟨72052632400270145329675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 384280706134774108424933 72052632400270145329675)
                    ·
                      rfl

theorem cell22_210483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 1, 4].length) (baseStart_210483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210483 prefixEnd_210483 := by exact prefixLift 210483
  have htrace : WordTrace (prefixWord ++ tailWord_210483) baseStart_210483 baseEnd_210483 := by
    simpa [prefixWord, tailWord_210483, baseEnd_210483] using wordTrace_append hprefix tailTrace_210483
  have hstable : (prefixWord ++ tailWord_210483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210483).length < 2 ^ (prefixWord ++ tailWord_210483).sum := by decide
  have hdescent : baseEnd_210483 < baseStart_210483 := by decide
  rcases family_descends (prefixWord ++ tailWord_210483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210513 : List Nat := [1, 2, 2, 1, 3, 2, 5, 1, 2, 3]
def baseStart_210513 : Nat := 118140960795 + 210513 * 2 ^ 59
def prefixEnd_210513 : Nat := 4983230072969 + 3 ^ 40 * 210513 * 2
def baseEnd_210513 : Nat := 72062902013360067079583

theorem tailTrace_210513 : CollatzResearch.WordTrace tailWord_210513 prefixEnd_210513 72062902013360067079583 := by
  unfold tailWord_210513
  simp only [CollatzResearch.WordTrace]
  refine ⟨7678039886354828603164193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5118693257569885735442795 7678039886354828603164193)
  ·
    refine ⟨5758529914766121452373145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7678039886354828603164193 5758529914766121452373145)
    ·
      refine ⟨4318897436074591089279859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5758529914766121452373145 4318897436074591089279859)
      ·
        refine ⟨6478346154111886633919789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4318897436074591089279859 6478346154111886633919789)
        ·
          refine ⟨2429379807791957487719921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6478346154111886633919789 2429379807791957487719921)
          ·
            refine ⟨1822034855843968115789941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2429379807791957487719921 1822034855843968115789941)
            ·
              refine ⟨170815767735372010855307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1822034855843968115789941 170815767735372010855307)
              ·
                refine ⟨256223651603058016282961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170815767735372010855307 256223651603058016282961)
                ·
                  refine ⟨192167738702293512212221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256223651603058016282961 192167738702293512212221)
                  ·
                    refine ⟨72062902013360067079583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192167738702293512212221 72062902013360067079583)
                    ·
                      rfl

theorem cell22_210513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_210513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210513 prefixEnd_210513 := by exact prefixLift 210513
  have htrace : WordTrace (prefixWord ++ tailWord_210513) baseStart_210513 baseEnd_210513 := by
    simpa [prefixWord, tailWord_210513, baseEnd_210513] using wordTrace_append hprefix tailTrace_210513
  have hstable : (prefixWord ++ tailWord_210513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210513).length < 2 ^ (prefixWord ++ tailWord_210513).sum := by decide
  have hdescent : baseEnd_210513 < baseStart_210513 := by decide
  rcases family_descends (prefixWord ++ tailWord_210513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210569 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 2, 5]
def baseStart_210569 : Nat := 118140960795 + 210569 * 2 ^ 59
def prefixEnd_210569 : Nat := 4983230072969 + 3 ^ 40 * 210569 * 2
def baseEnd_210569 : Nat := 72082071957794587679411

theorem tailTrace_210569 : CollatzResearch.WordTrace tailWord_210569 prefixEnd_210569 72082071957794587679411 := by
  unfold tailWord_210569
  simp only [CollatzResearch.WordTrace]
  refine ⟨7680082374151950167202761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5120054916101300111468507 7680082374151950167202761)
  ·
    refine ⟨5760061780613962625402071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7680082374151950167202761 5760061780613962625402071)
    ·
      refine ⟨8640092670920943938103107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5760061780613962625402071 8640092670920943938103107)
      ·
        refine ⟨12960139006381415907154661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8640092670920943938103107 12960139006381415907154661)
        ·
          refine ⟨2430026063696515482591499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12960139006381415907154661 2430026063696515482591499)
          ·
            refine ⟨3645039095544773223887249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2430026063696515482591499 3645039095544773223887249)
            ·
              refine ⟨2733779321658579917915437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3645039095544773223887249 2733779321658579917915437)
              ·
                refine ⟨1025167245621967469218289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2733779321658579917915437 1025167245621967469218289)
                ·
                  refine ⟨768875434216475601913717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1025167245621967469218289 768875434216475601913717)
                  ·
                    refine ⟨72082071957794587679411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 768875434216475601913717 72082071957794587679411)
                    ·
                      rfl

theorem cell22_210569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_210569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210569 prefixEnd_210569 := by exact prefixLift 210569
  have htrace : WordTrace (prefixWord ++ tailWord_210569) baseStart_210569 baseEnd_210569 := by
    simpa [prefixWord, tailWord_210569, baseEnd_210569] using wordTrace_append hprefix tailTrace_210569
  have hstable : (prefixWord ++ tailWord_210569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210569).length < 2 ^ (prefixWord ++ tailWord_210569).sum := by decide
  have hdescent : baseEnd_210569 < baseStart_210569 := by decide
  rcases family_descends (prefixWord ++ tailWord_210569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210629 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_210629 : Nat := 118140960795 + 210629 * 2 ^ 59
def prefixEnd_210629 : Nat := 4983230072969 + 3 ^ 40 * 210629 * 2
def baseEnd_210629 : Nat := 72102611183974431179227

theorem tailTrace_210629 : CollatzResearch.WordTrace tailWord_210629 prefixEnd_210629 72102611183974431179227 := by
  unfold tailWord_210629
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682270753934580414386941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5121513835956386942924627 7682270753934580414386941)
  ·
    refine ⟨2880851532725467655395103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7682270753934580414386941 2880851532725467655395103)
    ·
      refine ⟨4321277299088201483092655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2880851532725467655395103 4321277299088201483092655)
      ·
        refine ⟨6481915948632302224638983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4321277299088201483092655 6481915948632302224638983)
        ·
          refine ⟨9722873922948453336958475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6481915948632302224638983 9722873922948453336958475)
          ·
            refine ⟨14584310884422680005437713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9722873922948453336958475 14584310884422680005437713)
            ·
              refine ⟨10938233163317010004078285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14584310884422680005437713 10938233163317010004078285)
              ·
                refine ⟨4101837436243878751529357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10938233163317010004078285 4101837436243878751529357)
                ·
                  refine ⟨1538189038591454531823509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4101837436243878751529357 1538189038591454531823509)
                  ·
                    refine ⟨72102611183974431179227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1538189038591454531823509 72102611183974431179227)
                    ·
                      rfl

theorem cell22_210629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_210629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210629 prefixEnd_210629 := by exact prefixLift 210629
  have htrace : WordTrace (prefixWord ++ tailWord_210629) baseStart_210629 baseEnd_210629 := by
    simpa [prefixWord, tailWord_210629, baseEnd_210629] using wordTrace_append hprefix tailTrace_210629
  have hstable : (prefixWord ++ tailWord_210629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210629).length < 2 ^ (prefixWord ++ tailWord_210629).sum := by decide
  have hdescent : baseEnd_210629 < baseStart_210629 := by decide
  rcases family_descends (prefixWord ++ tailWord_210629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210631 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 1, 5]
def baseStart_210631 : Nat := 118140960795 + 210631 * 2 ^ 59
def prefixEnd_210631 : Nat := 4983230072969 + 3 ^ 40 * 210631 * 2
def baseEnd_210631 : Nat := 72103295824847092629221

theorem tailTrace_210631 : CollatzResearch.WordTrace tailWord_210631 prefixEnd_210631 72103295824847092629221 := by
  unfold tailWord_210631
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682343699927334755959747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5121562466618223170639831 7682343699927334755959747)
  ·
    refine ⟨11523515549891002133939621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7682343699927334755959747 11523515549891002133939621)
    ·
      refine ⟨2160659165604562900113679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11523515549891002133939621 2160659165604562900113679)
      ·
        refine ⟨3240988748406844350170519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2160659165604562900113679 3240988748406844350170519)
        ·
          refine ⟨4861483122610266525255779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240988748406844350170519 4861483122610266525255779)
          ·
            refine ⟨7292224683915399787883669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4861483122610266525255779 7292224683915399787883669)
            ·
              refine ⟨341823032058534365057047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7292224683915399787883669 341823032058534365057047)
              ·
                refine ⟨512734548087801547585571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341823032058534365057047 512734548087801547585571)
                ·
                  refine ⟨769101822131702321378357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512734548087801547585571 769101822131702321378357)
                  ·
                    refine ⟨72103295824847092629221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 769101822131702321378357 72103295824847092629221)
                    ·
                      rfl

theorem cell22_210631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_210631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210631 prefixEnd_210631 := by exact prefixLift 210631
  have htrace : WordTrace (prefixWord ++ tailWord_210631) baseStart_210631 baseEnd_210631 := by
    simpa [prefixWord, tailWord_210631, baseEnd_210631] using wordTrace_append hprefix tailTrace_210631
  have hstable : (prefixWord ++ tailWord_210631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210631).length < 2 ^ (prefixWord ++ tailWord_210631).sum := by decide
  have hdescent : baseEnd_210631 < baseStart_210631 := by decide
  rcases family_descends (prefixWord ++ tailWord_210631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210695 : List Nat := [1, 1, 4, 4, 2, 2, 2, 6]
def baseStart_210695 : Nat := 118140960795 + 210695 * 2 ^ 59
def prefixEnd_210695 : Nat := 4983230072969 + 3 ^ 40 * 210695 * 2
def baseEnd_210695 : Nat := 8013911592530251003225

theorem tailTrace_210695 : CollatzResearch.WordTrace tailWord_210695 prefixEnd_210695 8013911592530251003225 := by
  unfold tailWord_210695
  simp only [CollatzResearch.WordTrace]
  refine ⟨7684677971695473686289539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5123118647796982457526359 7684677971695473686289539)
  ·
    refine ⟨11527016957543210529434309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7684677971695473686289539 11527016957543210529434309)
    ·
      refine ⟨2161315679539351974268933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11527016957543210529434309 2161315679539351974268933)
      ·
        refine ⟨405246689913628495175425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2161315679539351974268933 405246689913628495175425)
        ·
          refine ⟨303935017435221371381569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405246689913628495175425 303935017435221371381569)
          ·
            refine ⟨227951263076416028536177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303935017435221371381569 227951263076416028536177)
            ·
              refine ⟨170963447307312021402133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227951263076416028536177 170963447307312021402133)
              ·
                refine ⟨8013911592530251003225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170963447307312021402133 8013911592530251003225)
                ·
                  rfl

theorem cell22_210695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 6].length) (baseStart_210695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210695 prefixEnd_210695 := by exact prefixLift 210695
  have htrace : WordTrace (prefixWord ++ tailWord_210695) baseStart_210695 baseEnd_210695 := by
    simpa [prefixWord, tailWord_210695, baseEnd_210695] using wordTrace_append hprefix tailTrace_210695
  have hstable : (prefixWord ++ tailWord_210695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210695).length < 2 ^ (prefixWord ++ tailWord_210695).sum := by decide
  have hdescent : baseEnd_210695 < baseStart_210695 := by decide
  rcases family_descends (prefixWord ++ tailWord_210695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210740 : List Nat := [2, 5, 1, 1, 2, 2, 1, 3, 5]
def baseStart_210740 : Nat := 118140960795 + 210740 * 2 ^ 59
def prefixEnd_210740 : Nat := 4983230072969 + 3 ^ 40 * 210740 * 2
def baseEnd_210740 : Nat := 24046869584135713884629

theorem tailTrace_210740 : CollatzResearch.WordTrace tailWord_210740 prefixEnd_210740 24046869584135713884629 := by
  unfold tailWord_210740
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843159628266223185838837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5124212837688297581118449 3843159628266223185838837)
  ·
    refine ⟨360296215149958423672391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3843159628266223185838837 360296215149958423672391)
    ·
      refine ⟨540444322724937635508587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360296215149958423672391 540444322724937635508587)
      ·
        refine ⟨810666484087406453262881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540444322724937635508587 810666484087406453262881)
        ·
          refine ⟨607999863065554839947161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 810666484087406453262881 607999863065554839947161)
          ·
            refine ⟨455999897299166129960371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607999863065554839947161 455999897299166129960371)
            ·
              refine ⟨683999845948749194940557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455999897299166129960371 683999845948749194940557)
              ·
                refine ⟨256499942230780948102709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 683999845948749194940557 256499942230780948102709)
                ·
                  refine ⟨24046869584135713884629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 256499942230780948102709 24046869584135713884629)
                  ·
                    rfl

theorem cell22_210740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_210740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210740 prefixEnd_210740 := by exact prefixLift 210740
  have htrace : WordTrace (prefixWord ++ tailWord_210740) baseStart_210740 baseEnd_210740 := by
    simpa [prefixWord, tailWord_210740, baseEnd_210740] using wordTrace_append hprefix tailTrace_210740
  have hstable : (prefixWord ++ tailWord_210740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210740).length < 2 ^ (prefixWord ++ tailWord_210740).sum := by decide
  have hdescent : baseEnd_210740 < baseStart_210740 := by decide
  rcases family_descends (prefixWord ++ tailWord_210740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210768 : List Nat := [2, 1, 1, 1, 1, 4, 1, 7, 4]
def baseStart_210768 : Nat := 118140960795 + 210768 * 2 ^ 59
def prefixEnd_210768 : Nat := 4983230072969 + 3 ^ 40 * 210768 * 2
def baseEnd_210768 : Nat := 24050064574874800651267

theorem tailTrace_210768 : CollatzResearch.WordTrace tailWord_210768 prefixEnd_210768 24050064574874800651267 := by
  unfold tailWord_210768
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843670250215503576848479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5124893666954004769131305 3843670250215503576848479)
  ·
    refine ⟨5765505375323255365272719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3843670250215503576848479 5765505375323255365272719)
    ·
      refine ⟨8648258062984883047909079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5765505375323255365272719 8648258062984883047909079)
      ·
        refine ⟨12972387094477324571863619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8648258062984883047909079 12972387094477324571863619)
        ·
          refine ⟨19458580641715986857795429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12972387094477324571863619 19458580641715986857795429)
          ·
            refine ⟨3648483870321747535836643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19458580641715986857795429 3648483870321747535836643)
            ·
              refine ⟨5472725805482621303754965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648483870321747535836643 5472725805482621303754965)
              ·
                refine ⟨128267011065998936806757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5472725805482621303754965 128267011065998936806757)
                ·
                  refine ⟨24050064574874800651267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128267011065998936806757 24050064574874800651267)
                  ·
                    rfl

theorem cell22_210768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 4].length) (baseStart_210768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210768 prefixEnd_210768 := by exact prefixLift 210768
  have htrace : WordTrace (prefixWord ++ tailWord_210768) baseStart_210768 baseEnd_210768 := by
    simpa [prefixWord, tailWord_210768, baseEnd_210768] using wordTrace_append hprefix tailTrace_210768
  have hstable : (prefixWord ++ tailWord_210768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210768).length < 2 ^ (prefixWord ++ tailWord_210768).sum := by decide
  have hdescent : baseEnd_210768 < baseStart_210768 := by decide
  rcases family_descends (prefixWord ++ tailWord_210768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210828 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 7, 3]
def baseStart_210828 : Nat := 118140960795 + 210828 * 2 ^ 59
def prefixEnd_210828 : Nat := 4983230072969 + 3 ^ 40 * 210828 * 2
def baseEnd_210828 : Nat := 72170732950804245453617

theorem tailTrace_210828 : CollatzResearch.WordTrace tailWord_210828 prefixEnd_210828 72170732950804245453617 := by
  unfold tailWord_210828
  simp only [CollatzResearch.WordTrace]
  refine ⟨3844764440106818700440569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5126352586809091600587425 3844764440106818700440569)
  ·
    refine ⟨2883573330080114025330427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3844764440106818700440569 2883573330080114025330427)
    ·
      refine ⟨4325359995120171037995641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2883573330080114025330427 4325359995120171037995641)
      ·
        refine ⟨3244019996340128278496731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4325359995120171037995641 3244019996340128278496731)
        ·
          refine ⟨4866029994510192417745097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3244019996340128278496731 4866029994510192417745097)
          ·
            refine ⟨3649522495882644313308823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4866029994510192417745097 3649522495882644313308823)
            ·
              refine ⟨5474283743823966469963235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649522495882644313308823 5474283743823966469963235)
              ·
                refine ⟨8211425615735949704944853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474283743823966469963235 8211425615735949704944853)
                ·
                  refine ⟨192455287868811321209645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8211425615735949704944853 192455287868811321209645)
                  ·
                    refine ⟨72170732950804245453617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192455287868811321209645 72170732950804245453617)
                    ·
                      rfl

theorem cell22_210828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_210828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210828 prefixEnd_210828 := by exact prefixLift 210828
  have htrace : WordTrace (prefixWord ++ tailWord_210828) baseStart_210828 baseEnd_210828 := by
    simpa [prefixWord, tailWord_210828, baseEnd_210828] using wordTrace_append hprefix tailTrace_210828
  have hstable : (prefixWord ++ tailWord_210828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210828).length < 2 ^ (prefixWord ++ tailWord_210828).sum := by decide
  have hdescent : baseEnd_210828 < baseStart_210828 := by decide
  rcases family_descends (prefixWord ++ tailWord_210828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210830 : List Nat := [4, 1, 1, 5, 1, 1, 9]
def baseStart_210830 : Nat := 118140960795 + 210830 * 2 ^ 59
def prefixEnd_210830 : Nat := 4983230072969 + 3 ^ 40 * 210830 * 2
def baseEnd_210830 : Nat := 2673015466358403959393

theorem tailTrace_210830 : CollatzResearch.WordTrace tailWord_210830 prefixEnd_210830 2673015466358403959393 := by
  unfold tailWord_210830
  simp only [CollatzResearch.WordTrace]
  refine ⟨961200228275798967806743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5126401217470927828302629 961200228275798967806743)
  ·
    refine ⟨1441800342413698451710115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 961200228275798967806743 1441800342413698451710115)
    ·
      refine ⟨2162700513620547677565173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1441800342413698451710115 2162700513620547677565173)
      ·
        refine ⟨202753173151926344771735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2162700513620547677565173 202753173151926344771735)
        ·
          refine ⟨304129759727889517157603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202753173151926344771735 304129759727889517157603)
          ·
            refine ⟨456194639591834275736405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304129759727889517157603 456194639591834275736405)
            ·
              refine ⟨2673015466358403959393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 456194639591834275736405 2673015466358403959393)
              ·
                rfl

theorem cell22_210830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 9].length) (baseStart_210830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210830 prefixEnd_210830 := by exact prefixLift 210830
  have htrace : WordTrace (prefixWord ++ tailWord_210830) baseStart_210830 baseEnd_210830 := by
    simpa [prefixWord, tailWord_210830, baseEnd_210830] using wordTrace_append hprefix tailTrace_210830
  have hstable : (prefixWord ++ tailWord_210830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210830).length < 2 ^ (prefixWord ++ tailWord_210830).sum := by decide
  have hdescent : baseEnd_210830 < baseStart_210830 := by decide
  rcases family_descends (prefixWord ++ tailWord_210830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210834 : List Nat := [3, 2, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_210834 : Nat := 118140960795 + 210834 * 2 ^ 59
def prefixEnd_210834 : Nat := 4983230072969 + 3 ^ 40 * 210834 * 2
def baseEnd_210834 : Nat := 72172786873422229803599

theorem tailTrace_210834 : CollatzResearch.WordTrace tailWord_210834 prefixEnd_210834 72172786873422229803599 := by
  unfold tailWord_210834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922436929547975106399889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5126498478794600283733037 1922436929547975106399889)
  ·
    refine ⟨1441827697160981329799917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1922436929547975106399889 1441827697160981329799917)
    ·
      refine ⟨540685386435367998674969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1441827697160981329799917 540685386435367998674969)
      ·
        refine ⟨405514039826525999006227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540685386435367998674969 405514039826525999006227)
        ·
          refine ⟨608271059739788998509341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405514039826525999006227 608271059739788998509341)
          ·
            refine ⟨228101647402420874441003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 608271059739788998509341 228101647402420874441003)
            ·
              refine ⟨342152471103631311661505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228101647402420874441003 342152471103631311661505)
              ·
                refine ⟨256614353327723483746129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342152471103631311661505 256614353327723483746129)
                ·
                  refine ⟨192460764995792612809597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256614353327723483746129 192460764995792612809597)
                  ·
                    refine ⟨72172786873422229803599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192460764995792612809597 72172786873422229803599)
                    ·
                      rfl

theorem cell22_210834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_210834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210834 prefixEnd_210834 := by exact prefixLift 210834
  have htrace : WordTrace (prefixWord ++ tailWord_210834) baseStart_210834 baseEnd_210834 := by
    simpa [prefixWord, tailWord_210834, baseEnd_210834] using wordTrace_append hprefix tailTrace_210834
  have hstable : (prefixWord ++ tailWord_210834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210834).length < 2 ^ (prefixWord ++ tailWord_210834).sum := by decide
  have hdescent : baseEnd_210834 < baseStart_210834 := by decide
  rcases family_descends (prefixWord ++ tailWord_210834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210845 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_210845 : Nat := 118140960795 + 210845 * 2 ^ 59
def prefixEnd_210845 : Nat := 4983230072969 + 3 ^ 40 * 210845 * 2
def baseEnd_210845 : Nat := 72176552398221867778565

theorem tailTrace_210845 : CollatzResearch.WordTrace tailWord_210845 prefixEnd_210845 72176552398221867778565 := by
  unfold tailWord_210845
  simp only [CollatzResearch.WordTrace]
  refine ⟨7690148921152049304249989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5126765947434699536166659 7690148921152049304249989)
  ·
    refine ⟨1441902922716009244546873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7690148921152049304249989 1441902922716009244546873)
    ·
      refine ⟨1081427192037006933410155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1441902922716009244546873 1081427192037006933410155)
      ·
        refine ⟨1622140788055510400115233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081427192037006933410155 1622140788055510400115233)
        ·
          refine ⟨1216605591041632800086425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1622140788055510400115233 1216605591041632800086425)
          ·
            refine ⟨912454193281224600064819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1216605591041632800086425 912454193281224600064819)
            ·
              refine ⟨1368681289921836900097229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912454193281224600064819 1368681289921836900097229)
              ·
                refine ⟨513255483720688837536461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1368681289921836900097229 513255483720688837536461)
                ·
                  refine ⟨192470806395258314076173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513255483720688837536461 192470806395258314076173)
                  ·
                    refine ⟨72176552398221867778565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192470806395258314076173 72176552398221867778565)
                    ·
                      rfl

theorem cell22_210845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_210845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210845 prefixEnd_210845 := by exact prefixLift 210845
  have htrace : WordTrace (prefixWord ++ tailWord_210845) baseStart_210845 baseEnd_210845 := by
    simpa [prefixWord, tailWord_210845, baseEnd_210845] using wordTrace_append hprefix tailTrace_210845
  have hstable : (prefixWord ++ tailWord_210845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210845).length < 2 ^ (prefixWord ++ tailWord_210845).sum := by decide
  have hdescent : baseEnd_210845 < baseStart_210845 := by decide
  rcases family_descends (prefixWord ++ tailWord_210845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210909 : List Nat := [1, 4, 3, 1, 3, 2, 2, 1, 5]
def baseStart_210909 : Nat := 118140960795 + 210909 * 2 ^ 59
def prefixEnd_210909 : Nat := 4983230072969 + 3 ^ 40 * 210909 * 2
def baseEnd_210909 : Nat := 24066153635382344726123

theorem tailTrace_210909 : CollatzResearch.WordTrace tailWord_210909 prefixEnd_210909 24066153635382344726123 := by
  unfold tailWord_210909
  simp only [CollatzResearch.WordTrace]
  refine ⟨7692483192920188234579781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5128322128613458823053187 7692483192920188234579781)
  ·
    refine ⟨1442340598672535293983709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7692483192920188234579781 1442340598672535293983709)
    ·
      refine ⟨540877724502200735243891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1442340598672535293983709 540877724502200735243891)
      ·
        refine ⟨811316586753301102865837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540877724502200735243891 811316586753301102865837)
        ·
          refine ⟨304243720032487913574689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 811316586753301102865837 304243720032487913574689)
          ·
            refine ⟨228182790024365935181017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304243720032487913574689 228182790024365935181017)
            ·
              refine ⟨171137092518274451385763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228182790024365935181017 171137092518274451385763)
              ·
                refine ⟨256705638777411677078645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171137092518274451385763 256705638777411677078645)
                ·
                  refine ⟨24066153635382344726123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 256705638777411677078645 24066153635382344726123)
                  ·
                    rfl

theorem cell22_210909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_210909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210909 prefixEnd_210909 := by exact prefixLift 210909
  have htrace : WordTrace (prefixWord ++ tailWord_210909) baseStart_210909 baseEnd_210909 := by
    simpa [prefixWord, tailWord_210909, baseEnd_210909] using wordTrace_append hprefix tailTrace_210909
  have hstable : (prefixWord ++ tailWord_210909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210909).length < 2 ^ (prefixWord ++ tailWord_210909).sum := by decide
  have hdescent : baseEnd_210909 < baseStart_210909 := by decide
  rcases family_descends (prefixWord ++ tailWord_210909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210952 : List Nat := [2, 1, 3, 2, 1, 2, 4, 2, 2, 3]
def baseStart_210952 : Nat := 118140960795 + 210952 * 2 ^ 59
def prefixEnd_210952 : Nat := 4983230072969 + 3 ^ 40 * 210952 * 2
def baseEnd_210952 : Nat := 72213180684909255353237

theorem tailTrace_210952 : CollatzResearch.WordTrace tailWord_210952 prefixEnd_210952 72213180684909255353237 := by
  unfold tailWord_210952
  simp only [CollatzResearch.WordTrace]
  refine ⟨3847025765882203289197555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5129367687842937718930073 3847025765882203289197555)
  ·
    refine ⟨5770538648823304933796333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3847025765882203289197555 5770538648823304933796333)
    ·
      refine ⟨2163951993308739350173625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5770538648823304933796333 2163951993308739350173625)
      ·
        refine ⟨1622963994981554512630219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2163951993308739350173625 1622963994981554512630219)
        ·
          refine ⟨2434445992472331768945329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622963994981554512630219 2434445992472331768945329)
          ·
            refine ⟨1825834494354248826708997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2434445992472331768945329 1825834494354248826708997)
            ·
              refine ⟨342343967691421655007937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1825834494354248826708997 342343967691421655007937)
              ·
                refine ⟨256757975768566241255953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342343967691421655007937 256757975768566241255953)
                ·
                  refine ⟨192568481826424680941965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256757975768566241255953 192568481826424680941965)
                  ·
                    refine ⟨72213180684909255353237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192568481826424680941965 72213180684909255353237)
                    ·
                      rfl

theorem cell22_210952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_210952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_210952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_210952 prefixEnd_210952 := by exact prefixLift 210952
  have htrace : WordTrace (prefixWord ++ tailWord_210952) baseStart_210952 baseEnd_210952 := by
    simpa [prefixWord, tailWord_210952, baseEnd_210952] using wordTrace_append hprefix tailTrace_210952
  have hstable : (prefixWord ++ tailWord_210952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210952).length < 2 ^ (prefixWord ++ tailWord_210952).sum := by decide
  have hdescent : baseEnd_210952 < baseStart_210952 := by decide
  rcases family_descends (prefixWord ++ tailWord_210952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211100 : List Nat := [2, 2, 3, 2, 1, 1, 1, 10]
def baseStart_211100 : Nat := 118140960795 + 211100 * 2 ^ 59
def prefixEnd_211100 : Nat := 4983230072969 + 3 ^ 40 * 211100 * 2
def baseEnd_211100 : Nat := 8029316012165133628087

theorem tailTrace_211100 : CollatzResearch.WordTrace tailWord_211100 prefixEnd_211100 8029316012165133628087 := by
  unfold tailWord_211100
  simp only [CollatzResearch.WordTrace]
  refine ⟨3849724767614113927391377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5132966356818818569855169 3849724767614113927391377)
  ·
    refine ⟨2887293575710585445543533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3849724767614113927391377 2887293575710585445543533)
    ·
      refine ⟨1082735090891469542078825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2887293575710585445543533 1082735090891469542078825)
      ·
        refine ⟨812051318168602156559119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1082735090891469542078825 812051318168602156559119)
        ·
          refine ⟨1218076977252903234838679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812051318168602156559119 1218076977252903234838679)
          ·
            refine ⟨1827115465879354852258019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218076977252903234838679 1827115465879354852258019)
            ·
              refine ⟨2740673198819032278387029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827115465879354852258019 2740673198819032278387029)
              ·
                refine ⟨8029316012165133628087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2740673198819032278387029 8029316012165133628087)
                ·
                  rfl

theorem cell22_211100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 10].length) (baseStart_211100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211100 prefixEnd_211100 := by exact prefixLift 211100
  have htrace : WordTrace (prefixWord ++ tailWord_211100) baseStart_211100 baseEnd_211100 := by
    simpa [prefixWord, tailWord_211100, baseEnd_211100] using wordTrace_append hprefix tailTrace_211100
  have hstable : (prefixWord ++ tailWord_211100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211100).length < 2 ^ (prefixWord ++ tailWord_211100).sum := by decide
  have hdescent : baseEnd_211100 < baseStart_211100 := by decide
  rcases family_descends (prefixWord ++ tailWord_211100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211121 : List Nat := [1, 2, 2, 5, 2, 1, 2, 2, 2, 3]
def baseStart_211121 : Nat := 118140960795 + 211121 * 2 ^ 59
def prefixEnd_211121 : Nat := 4983230072969 + 3 ^ 40 * 211121 * 2
def baseEnd_211121 : Nat := 72271032838649147877719

theorem tailTrace_211121 : CollatzResearch.WordTrace tailWord_211121 prefixEnd_211121 72271032838649147877719 := by
  unfold tailWord_211121
  simp only [CollatzResearch.WordTrace]
  refine ⟨7700215468152148441297217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5133476978768098960864811 7700215468152148441297217)
  ·
    refine ⟨5775161601114111330972913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7700215468152148441297217 5775161601114111330972913)
    ·
      refine ⟨4331371200835583498229685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5775161601114111330972913 4331371200835583498229685)
      ·
        refine ⟨406066050078335952959033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4331371200835583498229685 406066050078335952959033)
        ·
          refine ⟨304549537558751964719275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406066050078335952959033 304549537558751964719275)
          ·
            refine ⟨456824306338127947078913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304549537558751964719275 456824306338127947078913)
            ·
              refine ⟨342618229753595960309185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456824306338127947078913 342618229753595960309185)
              ·
                refine ⟨256963672315196970231889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342618229753595960309185 256963672315196970231889)
                ·
                  refine ⟨192722754236397727673917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256963672315196970231889 192722754236397727673917)
                  ·
                    refine ⟨72271032838649147877719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192722754236397727673917 72271032838649147877719)
                    ·
                      rfl

theorem cell22_211121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_211121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211121 prefixEnd_211121 := by exact prefixLift 211121
  have htrace : WordTrace (prefixWord ++ tailWord_211121) baseStart_211121 baseEnd_211121 := by
    simpa [prefixWord, tailWord_211121, baseEnd_211121] using wordTrace_append hprefix tailTrace_211121
  have hstable : (prefixWord ++ tailWord_211121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211121).length < 2 ^ (prefixWord ++ tailWord_211121).sum := by decide
  have hdescent : baseEnd_211121 < baseStart_211121 := by decide
  rcases family_descends (prefixWord ++ tailWord_211121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211130 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_211130 : Nat := 118140960795 + 211130 * 2 ^ 59
def prefixEnd_211130 : Nat := 4983230072969 + 3 ^ 40 * 211130 * 2
def baseEnd_211130 : Nat := 72274113722576124402691

theorem tailTrace_211130 : CollatzResearch.WordTrace tailWord_211130 prefixEnd_211130 72274113722576124402691 := by
  unfold tailWord_211130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1925135931279885744593711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5133695816746361985583229 1925135931279885744593711)
  ·
    refine ⟨2887703896919828616890567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1925135931279885744593711 2887703896919828616890567)
    ·
      refine ⟨4331555845379742925335851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2887703896919828616890567 4331555845379742925335851)
      ·
        refine ⟨6497333768069614388003777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4331555845379742925335851 6497333768069614388003777)
        ·
          refine ⟨4873000326052210791002833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6497333768069614388003777 4873000326052210791002833)
          ·
            refine ⟨3654750244539158093252125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4873000326052210791002833 3654750244539158093252125)
            ·
              refine ⟨1370531341702184284969547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3654750244539158093252125 1370531341702184284969547)
              ·
                refine ⟨2055797012553276427454321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370531341702184284969547 2055797012553276427454321)
                ·
                  refine ⟨1541847759414957320590741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2055797012553276427454321 1541847759414957320590741)
                  ·
                    refine ⟨72274113722576124402691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1541847759414957320590741 72274113722576124402691)
                    ·
                      rfl

theorem cell22_211130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_211130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211130 prefixEnd_211130 := by exact prefixLift 211130
  have htrace : WordTrace (prefixWord ++ tailWord_211130) baseStart_211130 baseEnd_211130 := by
    simpa [prefixWord, tailWord_211130, baseEnd_211130] using wordTrace_append hprefix tailTrace_211130
  have hstable : (prefixWord ++ tailWord_211130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211130).length < 2 ^ (prefixWord ++ tailWord_211130).sum := by decide
  have hdescent : baseEnd_211130 < baseStart_211130 := by decide
  rcases family_descends (prefixWord ++ tailWord_211130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211134 : List Nat := [4, 2, 1, 1, 4, 2, 1, 7]
def baseStart_211134 : Nat := 118140960795 + 211134 * 2 ^ 59
def prefixEnd_211134 : Nat := 4983230072969 + 3 ^ 40 * 211134 * 2
def baseEnd_211134 : Nat := 8030609222702383033631

theorem tailTrace_211134 : CollatzResearch.WordTrace tailWord_211134 prefixEnd_211134 8030609222702383033631 := by
  unfold tailWord_211134
  simp only [CollatzResearch.WordTrace]
  refine ⟨962586202138131457690057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5133793078070034441013637 962586202138131457690057)
  ·
    refine ⟨721939651603598593267543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 962586202138131457690057 721939651603598593267543)
    ·
      refine ⟨1082909477405397889901315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 721939651603598593267543 1082909477405397889901315)
      ·
        refine ⟨1624364216108096834851973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082909477405397889901315 1624364216108096834851973)
        ·
          refine ⟨304568290520268156534745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1624364216108096834851973 304568290520268156534745)
          ·
            refine ⟨228426217890201117401059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304568290520268156534745 228426217890201117401059)
            ·
              refine ⟨342639326835301676101589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228426217890201117401059 342639326835301676101589)
              ·
                refine ⟨8030609222702383033631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 342639326835301676101589 8030609222702383033631)
                ·
                  rfl

theorem cell22_211134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_211134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211134 prefixEnd_211134 := by exact prefixLift 211134
  have htrace : WordTrace (prefixWord ++ tailWord_211134) baseStart_211134 baseEnd_211134 := by
    simpa [prefixWord, tailWord_211134, baseEnd_211134] using wordTrace_append hprefix tailTrace_211134
  have hstable : (prefixWord ++ tailWord_211134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211134).length < 2 ^ (prefixWord ++ tailWord_211134).sum := by decide
  have hdescent : baseEnd_211134 < baseStart_211134 := by decide
  rcases family_descends (prefixWord ++ tailWord_211134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211138 : List Nat := [3, 5, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_211138 : Nat := 118140960795 + 211138 * 2 ^ 59
def prefixEnd_211138 : Nat := 4983230072969 + 3 ^ 40 * 211138 * 2
def baseEnd_211138 : Nat := 72276852286066770202667

theorem tailTrace_211138 : CollatzResearch.WordTrace tailWord_211138 prefixEnd_211138 72276852286066770202667 := by
  unfold tailWord_211138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1925208877272640086166517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5133890339393706896444045 1925208877272640086166517)
  ·
    refine ⟨180488332244310008078111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1925208877272640086166517 180488332244310008078111)
    ·
      refine ⟨270732498366465012117167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180488332244310008078111 270732498366465012117167)
      ·
        refine ⟨406098747549697518175751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270732498366465012117167 406098747549697518175751)
        ·
          refine ⟨609148121324546277263627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406098747549697518175751 609148121324546277263627)
          ·
            refine ⟨913722181986819415895441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609148121324546277263627 913722181986819415895441)
            ·
              refine ⟨685291636490114561921581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913722181986819415895441 685291636490114561921581)
              ·
                refine ⟨256984363683792960720593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 685291636490114561921581 256984363683792960720593)
                ·
                  refine ⟨192738272762844720540445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256984363683792960720593 192738272762844720540445)
                  ·
                    refine ⟨72276852286066770202667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192738272762844720540445 72276852286066770202667)
                    ·
                      rfl

theorem cell22_211138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_211138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211138 prefixEnd_211138 := by exact prefixLift 211138
  have htrace : WordTrace (prefixWord ++ tailWord_211138) baseStart_211138 baseEnd_211138 := by
    simpa [prefixWord, tailWord_211138, baseEnd_211138] using wordTrace_append hprefix tailTrace_211138
  have hstable : (prefixWord ++ tailWord_211138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211138).length < 2 ^ (prefixWord ++ tailWord_211138).sum := by decide
  have hdescent : baseEnd_211138 < baseStart_211138 := by decide
  rcases family_descends (prefixWord ++ tailWord_211138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211209 : List Nat := [1, 2, 1, 1, 3, 5, 2, 2, 1, 4]
def baseStart_211209 : Nat := 118140960795 + 211209 * 2 ^ 59
def prefixEnd_211209 : Nat := 4983230072969 + 3 ^ 40 * 211209 * 2
def baseEnd_211209 : Nat := 72301157037046251677449

theorem tailTrace_211209 : CollatzResearch.WordTrace tailWord_211209 prefixEnd_211209 72301157037046251677449 := by
  unfold tailWord_211209
  simp only [CollatzResearch.WordTrace]
  refine ⟨7703425091833339470500681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5135616727888892980333787 7703425091833339470500681)
  ·
    refine ⟨5777568818875004602875511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7703425091833339470500681 5777568818875004602875511)
    ·
      refine ⟨8666353228312506904313267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5777568818875004602875511 8666353228312506904313267)
      ·
        refine ⟨12999529842468760356469901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8666353228312506904313267 12999529842468760356469901)
        ·
          refine ⟨4874823690925785133676213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12999529842468760356469901 4874823690925785133676213)
          ·
            refine ⟨457014721024292356282145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4874823690925785133676213 457014721024292356282145)
            ·
              refine ⟨342761040768219267211609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457014721024292356282145 342761040768219267211609)
              ·
                refine ⟨257070780576164450408707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342761040768219267211609 257070780576164450408707)
                ·
                  refine ⟨385606170864246675613061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257070780576164450408707 385606170864246675613061)
                  ·
                    refine ⟨72301157037046251677449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 385606170864246675613061 72301157037046251677449)
                    ·
                      rfl

theorem cell22_211209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_211209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211209 prefixEnd_211209 := by exact prefixLift 211209
  have htrace : WordTrace (prefixWord ++ tailWord_211209) baseStart_211209 baseEnd_211209 := by
    simpa [prefixWord, tailWord_211209, baseEnd_211209] using wordTrace_append hprefix tailTrace_211209
  have hstable : (prefixWord ++ tailWord_211209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211209).length < 2 ^ (prefixWord ++ tailWord_211209).sum := by decide
  have hdescent : baseEnd_211209 < baseStart_211209 := by decide
  rcases family_descends (prefixWord ++ tailWord_211209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211256 : List Nat := [2, 1, 2, 1, 3, 1, 6, 1, 2, 3]
def baseStart_211256 : Nat := 118140960795 + 211256 * 2 ^ 59
def prefixEnd_211256 : Nat := 4983230072969 + 3 ^ 40 * 211256 * 2
def baseEnd_211256 : Nat := 72317246097553795752305

theorem tailTrace_211256 : CollatzResearch.WordTrace tailWord_211256 prefixEnd_211256 72317246097553795752305 := by
  unfold tailWord_211256
  simp only [CollatzResearch.WordTrace]
  refine ⟨3852569661331533248730811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5136759548442044331641081 3852569661331533248730811)
  ·
    refine ⟨5778854491997299873096217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3852569661331533248730811 5778854491997299873096217)
    ·
      refine ⟨4334140868997974904822163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5778854491997299873096217 4334140868997974904822163)
      ·
        refine ⟨6501211303496962357233245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4334140868997974904822163 6501211303496962357233245)
        ·
          refine ⟨2437954238811360883962467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6501211303496962357233245 2437954238811360883962467)
          ·
            refine ⟨3656931358217041325943701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437954238811360883962467 3656931358217041325943701)
            ·
              refine ⟨171418657416423812153611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3656931358217041325943701 171418657416423812153611)
              ·
                refine ⟨257127986124635718230417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171418657416423812153611 257127986124635718230417)
                ·
                  refine ⟨192845989593476788672813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257127986124635718230417 192845989593476788672813)
                  ·
                    refine ⟨72317246097553795752305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192845989593476788672813 72317246097553795752305)
                    ·
                      rfl

theorem cell22_211256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_211256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211256 prefixEnd_211256 := by exact prefixLift 211256
  have htrace : WordTrace (prefixWord ++ tailWord_211256) baseStart_211256 baseEnd_211256 := by
    simpa [prefixWord, tailWord_211256, baseEnd_211256] using wordTrace_append hprefix tailTrace_211256
  have hstable : (prefixWord ++ tailWord_211256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211256).length < 2 ^ (prefixWord ++ tailWord_211256).sum := by decide
  have hdescent : baseEnd_211256 < baseStart_211256 := by decide
  rcases family_descends (prefixWord ++ tailWord_211256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211292 : List Nat := [2, 2, 4, 3, 2, 1, 2, 2, 4]
def baseStart_211292 : Nat := 118140960795 + 211292 * 2 ^ 59
def prefixEnd_211292 : Nat := 4983230072969 + 3 ^ 40 * 211292 * 2
def baseEnd_211292 : Nat := 24109856544420567284065

theorem tailTrace_211292 : CollatzResearch.WordTrace tailWord_211292 prefixEnd_211292 24109856544420567284065 := by
  unfold tailWord_211292
  simp only [CollatzResearch.WordTrace]
  refine ⟨3853226175266322322886065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5137634900355096430514753 3853226175266322322886065)
  ·
    refine ⟨2889919631449741742164549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3853226175266322322886065 2889919631449741742164549)
    ·
      refine ⟨541859930896826576655853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2889919631449741742164549 541859930896826576655853)
      ·
        refine ⟨203197474086309966245945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 541859930896826576655853 203197474086309966245945)
        ·
          refine ⟨152398105564732474684459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203197474086309966245945 152398105564732474684459)
          ·
            refine ⟨228597158347098712026689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152398105564732474684459 228597158347098712026689)
            ·
              refine ⟨171447868760324034020017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228597158347098712026689 171447868760324034020017)
              ·
                refine ⟨128585901570243025515013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171447868760324034020017 128585901570243025515013)
                ·
                  refine ⟨24109856544420567284065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128585901570243025515013 24109856544420567284065)
                  ·
                    rfl

theorem cell22_211292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_211292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211292 prefixEnd_211292 := by exact prefixLift 211292
  have htrace : WordTrace (prefixWord ++ tailWord_211292) baseStart_211292 baseEnd_211292 := by
    simpa [prefixWord, tailWord_211292, baseEnd_211292] using wordTrace_append hprefix tailTrace_211292
  have hstable : (prefixWord ++ tailWord_211292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211292).length < 2 ^ (prefixWord ++ tailWord_211292).sum := by decide
  have hdescent : baseEnd_211292 < baseStart_211292 := by decide
  rcases family_descends (prefixWord ++ tailWord_211292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211312 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 1, 7]
def baseStart_211312 : Nat := 118140960795 + 211312 * 2 ^ 59
def prefixEnd_211312 : Nat := 4983230072969 + 3 ^ 40 * 211312 * 2
def baseEnd_211312 : Nat := 72336416041988316352133

theorem tailTrace_211312 : CollatzResearch.WordTrace tailWord_211312 prefixEnd_211312 72336416041988316352133 := by
  unfold tailWord_211312
  simp only [CollatzResearch.WordTrace]
  refine ⟨3853590905230094030750095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5138121206973458707666793 3853590905230094030750095)
  ·
    refine ⟨5780386357845141046125143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3853590905230094030750095 5780386357845141046125143)
    ·
      refine ⟨8670579536767711569187715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5780386357845141046125143 8670579536767711569187715)
      ·
        refine ⟨13005869305151567353781573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8670579536767711569187715 13005869305151567353781573)
        ·
          refine ⟨2438600494715918878834045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13005869305151567353781573 2438600494715918878834045)
          ·
            refine ⟨914475185518469579562767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2438600494715918878834045 914475185518469579562767)
            ·
              refine ⟨1371712778277704369344151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914475185518469579562767 1371712778277704369344151)
              ·
                refine ⟨2057569167416556554016227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371712778277704369344151 2057569167416556554016227)
                ·
                  refine ⟨3086353751124834831024341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057569167416556554016227 3086353751124834831024341)
                  ·
                    refine ⟨72336416041988316352133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3086353751124834831024341 72336416041988316352133)
                    ·
                      rfl

theorem cell22_211312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_211312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211312 prefixEnd_211312 := by exact prefixLift 211312
  have htrace : WordTrace (prefixWord ++ tailWord_211312) baseStart_211312 baseEnd_211312 := by
    simpa [prefixWord, tailWord_211312, baseEnd_211312] using wordTrace_append hprefix tailTrace_211312
  have hstable : (prefixWord ++ tailWord_211312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211312).length < 2 ^ (prefixWord ++ tailWord_211312).sum := by decide
  have hdescent : baseEnd_211312 < baseStart_211312 := by decide
  rcases family_descends (prefixWord ++ tailWord_211312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211314 : List Nat := [3, 2, 1, 2, 1, 3, 2, 3, 5]
def baseStart_211314 : Nat := 118140960795 + 211314 * 2 ^ 59
def prefixEnd_211314 : Nat := 4983230072969 + 3 ^ 40 * 211314 * 2
def baseEnd_211314 : Nat := 24112366894286992600709

theorem tailTrace_211314 : CollatzResearch.WordTrace tailWord_211314 prefixEnd_211314 24112366894286992600709 := by
  unfold tailWord_211314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1926813689113235600768249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5138169837635294935381997 1926813689113235600768249)
  ·
    refine ⟨1445110266834926700576187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1926813689113235600768249 1445110266834926700576187)
    ·
      refine ⟨2167665400252390050864281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1445110266834926700576187 2167665400252390050864281)
      ·
        refine ⟨1625749050189292538148211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2167665400252390050864281 1625749050189292538148211)
        ·
          refine ⟨2438623575283938807222317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1625749050189292538148211 2438623575283938807222317)
          ·
            refine ⟨914483840731477052708369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2438623575283938807222317 914483840731477052708369)
            ·
              refine ⟨685862880548607789531277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914483840731477052708369 685862880548607789531277)
              ·
                refine ⟨257198580205727921074229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 685862880548607789531277 257198580205727921074229)
                ·
                  refine ⟨24112366894286992600709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 257198580205727921074229 24112366894286992600709)
                  ·
                    rfl

theorem cell22_211314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_211314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211314 prefixEnd_211314 := by exact prefixLift 211314
  have htrace : WordTrace (prefixWord ++ tailWord_211314) baseStart_211314 baseEnd_211314 := by
    simpa [prefixWord, tailWord_211314, baseEnd_211314] using wordTrace_append hprefix tailTrace_211314
  have hstable : (prefixWord ++ tailWord_211314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211314).length < 2 ^ (prefixWord ++ tailWord_211314).sum := by decide
  have hdescent : baseEnd_211314 < baseStart_211314 := by decide
  rcases family_descends (prefixWord ++ tailWord_211314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211348 : List Nat := [2, 4, 2, 1, 3, 2, 1, 2, 5]
def baseStart_211348 : Nat := 118140960795 + 211348 * 2 ^ 59
def prefixEnd_211348 : Nat := 4983230072969 + 3 ^ 40 * 211348 * 2
def baseEnd_211348 : Nat := 24116246525898740817341

theorem tailTrace_211348 : CollatzResearch.WordTrace tailWord_211348 prefixEnd_211348 24116246525898740817341 := by
  unfold tailWord_211348
  simp only [CollatzResearch.WordTrace]
  refine ⟨3854247419164883104905349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5138996558886510806540465 3854247419164883104905349)
  ·
    refine ⟨722671391093415582169753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3854247419164883104905349 722671391093415582169753)
    ·
      refine ⟨542003543320061686627315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 722671391093415582169753 542003543320061686627315)
      ·
        refine ⟨813005314980092529940973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542003543320061686627315 813005314980092529940973)
        ·
          refine ⟨304876993117534698727865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 813005314980092529940973 304876993117534698727865)
          ·
            refine ⟨228657744838151024045899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304876993117534698727865 228657744838151024045899)
            ·
              refine ⟨342986617257226536068849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228657744838151024045899 342986617257226536068849)
              ·
                refine ⟨257239962942919902051637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342986617257226536068849 257239962942919902051637)
                ·
                  refine ⟨24116246525898740817341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 257239962942919902051637 24116246525898740817341)
                  ·
                    rfl

theorem cell22_211348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_211348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211348 prefixEnd_211348 := by exact prefixLift 211348
  have htrace : WordTrace (prefixWord ++ tailWord_211348) baseStart_211348 baseEnd_211348 := by
    simpa [prefixWord, tailWord_211348, baseEnd_211348] using wordTrace_append hprefix tailTrace_211348
  have hstable : (prefixWord ++ tailWord_211348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211348).length < 2 ^ (prefixWord ++ tailWord_211348).sum := by decide
  have hdescent : baseEnd_211348 < baseStart_211348 := by decide
  rcases family_descends (prefixWord ++ tailWord_211348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211359 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 6]
def baseStart_211359 : Nat := 118140960795 + 211359 * 2 ^ 59
def prefixEnd_211359 : Nat := 4983230072969 + 3 ^ 40 * 211359 * 2
def baseEnd_211359 : Nat := 24117501700831953475663

theorem tailTrace_211359 : CollatzResearch.WordTrace tailWord_211359 prefixEnd_211359 24117501700831953475663 := by
  unfold tailWord_211359
  simp only [CollatzResearch.WordTrace]
  refine ⟨7708896041289915088461131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5139264027526610058974087 7708896041289915088461131)
  ·
    refine ⟨11563344061934872632691697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7708896041289915088461131 11563344061934872632691697)
    ·
      refine ⟨8672508046451154474518773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11563344061934872632691697 8672508046451154474518773)
      ·
        refine ⟨813047629354795731986135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8672508046451154474518773 813047629354795731986135)
        ·
          refine ⟨1219571444032193597979203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813047629354795731986135 1219571444032193597979203)
          ·
            refine ⟨1829357166048290396968805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219571444032193597979203 1829357166048290396968805)
            ·
              refine ⟨343004468634054449431651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1829357166048290396968805 343004468634054449431651)
              ·
                refine ⟨514506702951081674147477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343004468634054449431651 514506702951081674147477)
                ·
                  refine ⟨24117501700831953475663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 514506702951081674147477 24117501700831953475663)
                  ·
                    rfl

theorem cell22_211359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 6].length) (baseStart_211359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211359 prefixEnd_211359 := by exact prefixLift 211359
  have htrace : WordTrace (prefixWord ++ tailWord_211359) baseStart_211359 baseEnd_211359 := by
    simpa [prefixWord, tailWord_211359, baseEnd_211359] using wordTrace_append hprefix tailTrace_211359
  have hstable : (prefixWord ++ tailWord_211359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211359).length < 2 ^ (prefixWord ++ tailWord_211359).sum := by decide
  have hdescent : baseEnd_211359 < baseStart_211359 := by decide
  rcases family_descends (prefixWord ++ tailWord_211359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211389 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_211389 : Nat := 118140960795 + 211389 * 2 ^ 59
def prefixEnd_211389 : Nat := 4983230072969 + 3 ^ 40 * 211389 * 2
def baseEnd_211389 : Nat := 72362774715585782176897

theorem tailTrace_211389 : CollatzResearch.WordTrace tailWord_211389 prefixEnd_211389 72362774715585782176897 := by
  unfold tailWord_211389
  simp only [CollatzResearch.WordTrace]
  refine ⟨7709990231181230212053221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5139993487454153474702147 7709990231181230212053221)
  ·
    refine ⟨1445623168346480664759979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7709990231181230212053221 1445623168346480664759979)
    ·
      refine ⟨2168434752519720997139969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1445623168346480664759979 2168434752519720997139969)
      ·
        refine ⟨1626326064389790747854977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2168434752519720997139969 1626326064389790747854977)
        ·
          refine ⟨1219744548292343060891233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1626326064389790747854977 1219744548292343060891233)
          ·
            refine ⟨914808411219257295668425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219744548292343060891233 914808411219257295668425)
            ·
              refine ⟨686106308414442971751319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914808411219257295668425 686106308414442971751319)
              ·
                refine ⟨1029159462621664457626979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686106308414442971751319 1029159462621664457626979)
                ·
                  refine ⟨1543739193932496686440469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029159462621664457626979 1543739193932496686440469)
                  ·
                    refine ⟨72362774715585782176897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1543739193932496686440469 72362774715585782176897)
                    ·
                      rfl

theorem cell22_211389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_211389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211389 prefixEnd_211389 := by exact prefixLift 211389
  have htrace : WordTrace (prefixWord ++ tailWord_211389) baseStart_211389 baseEnd_211389 := by
    simpa [prefixWord, tailWord_211389, baseEnd_211389] using wordTrace_append hprefix tailTrace_211389
  have hstable : (prefixWord ++ tailWord_211389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211389).length < 2 ^ (prefixWord ++ tailWord_211389).sum := by decide
  have hdescent : baseEnd_211389 < baseStart_211389 := by decide
  rcases family_descends (prefixWord ++ tailWord_211389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211410 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 6]
def baseStart_211410 : Nat := 118140960795 + 211410 * 2 ^ 59
def prefixEnd_211410 : Nat := 4983230072969 + 3 ^ 40 * 211410 * 2
def baseEnd_211410 : Nat := 24123321148249575800611

theorem tailTrace_211410 : CollatzResearch.WordTrace tailWord_211410 prefixEnd_211410 24123321148249575800611 := by
  unfold tailWord_211410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1927689041026287699641921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5140504109403433865711789 1927689041026287699641921)
  ·
    refine ⟨1445766780769715774731441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1927689041026287699641921 1445766780769715774731441)
    ·
      refine ⟨1084325085577286831048581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1445766780769715774731441 1084325085577286831048581)
      ·
        refine ⟨203310953545741280821609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1084325085577286831048581 203310953545741280821609)
        ·
          refine ⟨152483215159305960616207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203310953545741280821609 152483215159305960616207)
          ·
            refine ⟨228724822738958940924311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152483215159305960616207 228724822738958940924311)
            ·
              refine ⟨343087234108438411386467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228724822738958940924311 343087234108438411386467)
              ·
                refine ⟨514630851162657617079701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343087234108438411386467 514630851162657617079701)
                ·
                  refine ⟨24123321148249575800611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 514630851162657617079701 24123321148249575800611)
                  ·
                    rfl

theorem cell22_211410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_211410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211410 prefixEnd_211410 := by exact prefixLift 211410
  have htrace : WordTrace (prefixWord ++ tailWord_211410) baseStart_211410 baseEnd_211410 := by
    simpa [prefixWord, tailWord_211410, baseEnd_211410] using wordTrace_append hprefix tailTrace_211410
  have hstable : (prefixWord ++ tailWord_211410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211410).length < 2 ^ (prefixWord ++ tailWord_211410).sum := by decide
  have hdescent : baseEnd_211410 < baseStart_211410 := by decide
  rcases family_descends (prefixWord ++ tailWord_211410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211453 : List Nat := [1, 4, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_211453 : Nat := 118140960795 + 211453 * 2 ^ 59
def prefixEnd_211453 : Nat := 4983230072969 + 3 ^ 40 * 211453 * 2
def baseEnd_211453 : Nat := 72384683223510948576701

theorem tailTrace_211453 : CollatzResearch.WordTrace tailWord_211453 prefixEnd_211453 72384683223510948576701 := by
  unfold tailWord_211453
  simp only [CollatzResearch.WordTrace]
  refine ⟨7712324502949369142383013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5141549668632912761588675 7712324502949369142383013)
  ·
    refine ⟨1446060844303006714196815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7712324502949369142383013 1446060844303006714196815)
    ·
      refine ⟨2169091266454510071295223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1446060844303006714196815 2169091266454510071295223)
      ·
        refine ⟨3253636899681765106942835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2169091266454510071295223 3253636899681765106942835)
        ·
          refine ⟨4880455349522647660414253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253636899681765106942835 4880455349522647660414253)
          ·
            refine ⟨1830170756070992872655345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4880455349522647660414253 1830170756070992872655345)
            ·
              refine ⟨1372628067053244654491509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830170756070992872655345 1372628067053244654491509)
              ·
                refine ⟨128683881286241686358579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1372628067053244654491509 128683881286241686358579)
                ·
                  refine ⟨193025821929362529537869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128683881286241686358579 193025821929362529537869)
                  ·
                    refine ⟨72384683223510948576701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193025821929362529537869 72384683223510948576701)
                    ·
                      rfl

theorem cell22_211453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_211453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211453 prefixEnd_211453 := by exact prefixLift 211453
  have htrace : WordTrace (prefixWord ++ tailWord_211453) baseStart_211453 baseEnd_211453 := by
    simpa [prefixWord, tailWord_211453, baseEnd_211453] using wordTrace_append hprefix tailTrace_211453
  have hstable : (prefixWord ++ tailWord_211453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211453).length < 2 ^ (prefixWord ++ tailWord_211453).sum := by decide
  have hdescent : baseEnd_211453 < baseStart_211453 := by decide
  rcases family_descends (prefixWord ++ tailWord_211453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211464 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 2, 5]
def baseStart_211464 : Nat := 118140960795 + 211464 * 2 ^ 59
def prefixEnd_211464 : Nat := 4983230072969 + 3 ^ 40 * 211464 * 2
def baseEnd_211464 : Nat := 72388448748310586551667

theorem tailTrace_211464 : CollatzResearch.WordTrace tailWord_211464 prefixEnd_211464 72388448748310586551667 := by
  unfold tailWord_211464
  simp only [CollatzResearch.WordTrace]
  refine ⟨3856362852954759010516723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5141817137273012014022297 3856362852954759010516723)
  ·
    refine ⟨5784544279432138515775085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3856362852954759010516723 5784544279432138515775085)
    ·
      refine ⟨2169204104787051943415657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5784544279432138515775085 2169204104787051943415657)
      ·
        refine ⟨1626903078590288957561743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2169204104787051943415657 1626903078590288957561743)
        ·
          refine ⟨2440354617885433436342615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626903078590288957561743 2440354617885433436342615)
          ·
            refine ⟨3660531926828150154513923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440354617885433436342615 3660531926828150154513923)
            ·
              refine ⟨5490797890242225231770885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3660531926828150154513923 5490797890242225231770885)
              ·
                refine ⟨1029524604420417230957041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5490797890242225231770885 1029524604420417230957041)
                ·
                  refine ⟨772143453315312923217781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1029524604420417230957041 772143453315312923217781)
                  ·
                    refine ⟨72388448748310586551667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 772143453315312923217781 72388448748310586551667)
                    ·
                      rfl

theorem cell22_211464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_211464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211464 prefixEnd_211464 := by exact prefixLift 211464
  have htrace : WordTrace (prefixWord ++ tailWord_211464) baseStart_211464 baseEnd_211464 := by
    simpa [prefixWord, tailWord_211464, baseEnd_211464] using wordTrace_append hprefix tailTrace_211464
  have hstable : (prefixWord ++ tailWord_211464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211464).length < 2 ^ (prefixWord ++ tailWord_211464).sum := by decide
  have hdescent : baseEnd_211464 < baseStart_211464 := by decide
  rcases family_descends (prefixWord ++ tailWord_211464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211466 : List Nat := [3, 1, 2, 2, 2, 1, 4, 2, 5]
def baseStart_211466 : Nat := 118140960795 + 211466 * 2 ^ 59
def prefixEnd_211466 : Nat := 4983230072969 + 3 ^ 40 * 211466 * 2
def baseEnd_211466 : Nat := 24129711129727749333887

theorem tailTrace_211466 : CollatzResearch.WordTrace tailWord_211466 prefixEnd_211466 24129711129727749333887 := by
  unfold tailWord_211466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928199662975568090651563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5141865767934848241737501 1928199662975568090651563)
  ·
    refine ⟨2892299494463352135977345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1928199662975568090651563 2892299494463352135977345)
    ·
      refine ⟨2169224620847514101983009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2892299494463352135977345 2169224620847514101983009)
      ·
        refine ⟨1626918465635635576487257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2169224620847514101983009 1626918465635635576487257)
        ·
          refine ⟨1220188849226726682365443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1626918465635635576487257 1220188849226726682365443)
          ·
            refine ⟨1830283273840090023548165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220188849226726682365443 1830283273840090023548165)
            ·
              refine ⟨343178113845016879415281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1830283273840090023548165 343178113845016879415281)
              ·
                refine ⟨257383585383762659561461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343178113845016879415281 257383585383762659561461)
                ·
                  refine ⟨24129711129727749333887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 257383585383762659561461 24129711129727749333887)
                  ·
                    rfl

theorem cell22_211466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_211466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211466 prefixEnd_211466 := by exact prefixLift 211466
  have htrace : WordTrace (prefixWord ++ tailWord_211466) baseStart_211466 baseEnd_211466 := by
    simpa [prefixWord, tailWord_211466, baseEnd_211466] using wordTrace_append hprefix tailTrace_211466
  have hstable : (prefixWord ++ tailWord_211466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211466).length < 2 ^ (prefixWord ++ tailWord_211466).sum := by decide
  have hdescent : baseEnd_211466 < baseStart_211466 := by decide
  rcases family_descends (prefixWord ++ tailWord_211466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211470 : List Nat := [4, 1, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_211470 : Nat := 118140960795 + 211470 * 2 ^ 59
def prefixEnd_211470 : Nat := 4983230072969 + 3 ^ 40 * 211470 * 2
def baseEnd_211470 : Nat := 72390502670928570901649

theorem tailTrace_211470 : CollatzResearch.WordTrace tailWord_211470 prefixEnd_211470 72390502670928570901649 := by
  unfold tailWord_211470
  simp only [CollatzResearch.WordTrace]
  refine ⟨964118067985972630718983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5141963029258520697167909 964118067985972630718983)
  ·
    refine ⟨1446177101978958946078475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 964118067985972630718983 1446177101978958946078475)
    ·
      refine ⟨2169265652968438419117713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1446177101978958946078475 2169265652968438419117713)
      ·
        refine ⟨1626949239726328814338285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2169265652968438419117713 1626949239726328814338285)
        ·
          refine ⟨610105964897373305376857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1626949239726328814338285 610105964897373305376857)
          ·
            refine ⟨457579473673029979032643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610105964897373305376857 457579473673029979032643)
            ·
              refine ⟨686369210509544968548965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457579473673029979032643 686369210509544968548965)
              ·
                refine ⟨128694226970539681602931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 686369210509544968548965 128694226970539681602931)
                ·
                  refine ⟨193041340455809522404397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128694226970539681602931 193041340455809522404397)
                  ·
                    refine ⟨72390502670928570901649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193041340455809522404397 72390502670928570901649)
                    ·
                      rfl

theorem cell22_211470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_211470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211470 prefixEnd_211470 := by exact prefixLift 211470
  have htrace : WordTrace (prefixWord ++ tailWord_211470) baseStart_211470 baseEnd_211470 := by
    simpa [prefixWord, tailWord_211470, baseEnd_211470] using wordTrace_append hprefix tailTrace_211470
  have hstable : (prefixWord ++ tailWord_211470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211470).length < 2 ^ (prefixWord ++ tailWord_211470).sum := by decide
  have hdescent : baseEnd_211470 < baseStart_211470 := by decide
  rcases family_descends (prefixWord ++ tailWord_211470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211569 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 3, 8]
def baseStart_211569 : Nat := 118140960795 + 211569 * 2 ^ 59
def prefixEnd_211569 : Nat := 4983230072969 + 3 ^ 40 * 211569 * 2
def baseEnd_211569 : Nat := 72424392394125312676345

theorem tailTrace_211569 : CollatzResearch.WordTrace tailWord_211569 prefixEnd_211569 72424392394125312676345 := by
  unfold tailWord_211569
  simp only [CollatzResearch.WordTrace]
  refine ⟨7716555370529120953605761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5144370247019413969070507 7716555370529120953605761)
  ·
    refine ⟨5787416527896840715204321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7716555370529120953605761 5787416527896840715204321)
    ·
      refine ⟨4340562395922630536403241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5787416527896840715204321 4340562395922630536403241)
      ·
        refine ⟨3255421796941972902302431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4340562395922630536403241 3255421796941972902302431)
        ·
          refine ⟨4883132695412959353453647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3255421796941972902302431 4883132695412959353453647)
          ·
            refine ⟨7324699043119439030180471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883132695412959353453647 7324699043119439030180471)
            ·
              refine ⟨10987048564679158545270707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7324699043119439030180471 10987048564679158545270707)
              ·
                refine ⟨16480572847018737817906061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10987048564679158545270707 16480572847018737817906061)
                ·
                  refine ⟨6180214817632026681714773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16480572847018737817906061 6180214817632026681714773)
                  ·
                    refine ⟨72424392394125312676345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6180214817632026681714773 72424392394125312676345)
                    ·
                      rfl

theorem cell22_211569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_211569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211569 prefixEnd_211569 := by exact prefixLift 211569
  have htrace : WordTrace (prefixWord ++ tailWord_211569) baseStart_211569 baseEnd_211569 := by
    simpa [prefixWord, tailWord_211569, baseEnd_211569] using wordTrace_append hprefix tailTrace_211569
  have hstable : (prefixWord ++ tailWord_211569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211569).length < 2 ^ (prefixWord ++ tailWord_211569).sum := by decide
  have hdescent : baseEnd_211569 < baseStart_211569 := by decide
  rcases family_descends (prefixWord ++ tailWord_211569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211573 : List Nat := [1, 3, 4, 2, 2, 2, 8]
def baseStart_211573 : Nat := 118140960795 + 211573 * 2 ^ 59
def prefixEnd_211573 : Nat := 4983230072969 + 3 ^ 40 * 211573 * 2
def baseEnd_211573 : Nat := 2682435617624838354679

theorem tailTrace_211573 : CollatzResearch.WordTrace tailWord_211573 prefixEnd_211573 2682435617624838354679 := by
  unfold tailWord_211573
  simp only [CollatzResearch.WordTrace]
  refine ⟨7716701262514629636751373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5144467508343086424500915 7716701262514629636751373)
  ·
    refine ⟨2893762973442986113781765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7716701262514629636751373 2893762973442986113781765)
    ·
      refine ⟨542580557520559896334081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2893762973442986113781765 542580557520559896334081)
      ·
        refine ⟨406935418140419922250561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542580557520559896334081 406935418140419922250561)
        ·
          refine ⟨305201563605314941687921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406935418140419922250561 305201563605314941687921)
          ·
            refine ⟨228901172703986206265941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305201563605314941687921 228901172703986206265941)
            ·
              refine ⟨2682435617624838354679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 228901172703986206265941 2682435617624838354679)
              ·
                rfl

theorem cell22_211573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 8].length) (baseStart_211573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211573 prefixEnd_211573 := by exact prefixLift 211573
  have htrace : WordTrace (prefixWord ++ tailWord_211573) baseStart_211573 baseEnd_211573 := by
    simpa [prefixWord, tailWord_211573, baseEnd_211573] using wordTrace_append hprefix tailTrace_211573
  have hstable : (prefixWord ++ tailWord_211573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211573).length < 2 ^ (prefixWord ++ tailWord_211573).sum := by decide
  have hdescent : baseEnd_211573 < baseStart_211573 := by decide
  rcases family_descends (prefixWord ++ tailWord_211573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211594 : List Nat := [3, 1, 2, 3, 4, 1, 2, 1, 2, 3]
def baseStart_211594 : Nat := 118140960795 + 211594 * 2 ^ 59
def prefixEnd_211594 : Nat := 4983230072969 + 3 ^ 40 * 211594 * 2
def baseEnd_211594 : Nat := 72432950405033580801269

theorem tailTrace_211594 : CollatzResearch.WordTrace tailWord_211594 prefixEnd_211594 72432950405033580801269 := by
  unfold tailWord_211594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1929366798859637555816459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5144978130292366815510557 1929366798859637555816459)
  ·
    refine ⟨2894050198289456333724689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1929366798859637555816459 2894050198289456333724689)
    ·
      refine ⟨2170537648717092250293517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2894050198289456333724689 2170537648717092250293517)
      ·
        refine ⟨813951618268909593860069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2170537648717092250293517 813951618268909593860069)
        ·
          refine ⟨152615928425420548848763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 813951618268909593860069 152615928425420548848763)
          ·
            refine ⟨228923892638130823273145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152615928425420548848763 228923892638130823273145)
            ·
              refine ⟨171692919478598117454859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228923892638130823273145 171692919478598117454859)
              ·
                refine ⟨257539379217897176182289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171692919478598117454859 257539379217897176182289)
                ·
                  refine ⟨193154534413422882136717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257539379217897176182289 193154534413422882136717)
                  ·
                    refine ⟨72432950405033580801269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193154534413422882136717 72432950405033580801269)
                    ·
                      rfl

theorem cell22_211594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_211594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211594 prefixEnd_211594 := by exact prefixLift 211594
  have htrace : WordTrace (prefixWord ++ tailWord_211594) baseStart_211594 baseEnd_211594 := by
    simpa [prefixWord, tailWord_211594, baseEnd_211594] using wordTrace_append hprefix tailTrace_211594
  have hstable : (prefixWord ++ tailWord_211594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211594).length < 2 ^ (prefixWord ++ tailWord_211594).sum := by decide
  have hdescent : baseEnd_211594 < baseStart_211594 := by decide
  rcases family_descends (prefixWord ++ tailWord_211594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211639 : List Nat := [1, 1, 3, 1, 6, 2, 2, 2, 1, 3]
def baseStart_211639 : Nat := 118140960795 + 211639 * 2 ^ 59
def prefixEnd_211639 : Nat := 4983230072969 + 3 ^ 40 * 211639 * 2
def baseEnd_211639 : Nat := 72448354824668463426131

theorem tailTrace_211639 : CollatzResearch.WordTrace tailWord_211639 prefixEnd_211639 72448354824668463426131 := by
  unfold tailWord_211639
  simp only [CollatzResearch.WordTrace]
  refine ⟨7719108480275522908653971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5146072320183681939102647 7719108480275522908653971)
  ·
    refine ⟨11578662720413284362980957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7719108480275522908653971 11578662720413284362980957)
    ·
      refine ⟨4341998520154981636117859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11578662720413284362980957 4341998520154981636117859)
      ·
        refine ⟨6512997780232472454176789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4341998520154981636117859 6512997780232472454176789)
        ·
          refine ⟨305296770948397146289537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6512997780232472454176789 305296770948397146289537)
          ·
            refine ⟨228972578211297859717153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305296770948397146289537 228972578211297859717153)
            ·
              refine ⟨171729433658473394787865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228972578211297859717153 171729433658473394787865)
              ·
                refine ⟨128797075243855046090899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171729433658473394787865 128797075243855046090899)
                ·
                  refine ⟨193195612865782569136349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128797075243855046090899 193195612865782569136349)
                  ·
                    refine ⟨72448354824668463426131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193195612865782569136349 72448354824668463426131)
                    ·
                      rfl

theorem cell22_211639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_211639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211639 prefixEnd_211639 := by exact prefixLift 211639
  have htrace : WordTrace (prefixWord ++ tailWord_211639) baseStart_211639 baseEnd_211639 := by
    simpa [prefixWord, tailWord_211639, baseEnd_211639] using wordTrace_append hprefix tailTrace_211639
  have hstable : (prefixWord ++ tailWord_211639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211639).length < 2 ^ (prefixWord ++ tailWord_211639).sum := by decide
  have hdescent : baseEnd_211639 < baseStart_211639 := by decide
  rcases family_descends (prefixWord ++ tailWord_211639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211693 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_211693 : Nat := 118140960795 + 211693 * 2 ^ 59
def prefixEnd_211693 : Nat := 4983230072969 + 3 ^ 40 * 211693 * 2
def baseEnd_211693 : Nat := 72466840128230322575965

theorem tailTrace_211693 : CollatzResearch.WordTrace tailWord_211693 prefixEnd_211693 72466840128230322575965 := by
  unfold tailWord_211693
  simp only [CollatzResearch.WordTrace]
  refine ⟨7721078022079890131119733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5147385348053260087413155 7721078022079890131119733)
  ·
    refine ⟨723851064569989699792475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7721078022079890131119733 723851064569989699792475)
    ·
      refine ⟨1085776596854984549688713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 723851064569989699792475 1085776596854984549688713)
      ·
        refine ⟨814332447641238412266535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1085776596854984549688713 814332447641238412266535)
        ·
          refine ⟨1221498671461857618399803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814332447641238412266535 1221498671461857618399803)
          ·
            refine ⟨1832248007192786427599705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221498671461857618399803 1832248007192786427599705)
            ·
              refine ⟨1374186005394589820699779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832248007192786427599705 1374186005394589820699779)
              ·
                refine ⟨2061279008091884731049669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374186005394589820699779 2061279008091884731049669)
                ·
                  refine ⟨386489814017228387071813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2061279008091884731049669 386489814017228387071813)
                  ·
                    refine ⟨72466840128230322575965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 386489814017228387071813 72466840128230322575965)
                    ·
                      rfl

theorem cell22_211693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_211693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211693 prefixEnd_211693 := by exact prefixLift 211693
  have htrace : WordTrace (prefixWord ++ tailWord_211693) baseStart_211693 baseEnd_211693 := by
    simpa [prefixWord, tailWord_211693, baseEnd_211693] using wordTrace_append hprefix tailTrace_211693
  have hstable : (prefixWord ++ tailWord_211693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211693).length < 2 ^ (prefixWord ++ tailWord_211693).sum := by decide
  have hdescent : baseEnd_211693 < baseStart_211693 := by decide
  rcases family_descends (prefixWord ++ tailWord_211693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211695 : List Nat := [1, 1, 2, 1, 5, 2, 3, 2, 2, 3]
def baseStart_211695 : Nat := 118140960795 + 211695 * 2 ^ 59
def prefixEnd_211695 : Nat := 4983230072969 + 3 ^ 40 * 211695 * 2
def baseEnd_211695 : Nat := 72467524769102984025959

theorem tailTrace_211695 : CollatzResearch.WordTrace tailWord_211695 prefixEnd_211695 72467524769102984025959 := by
  unfold tailWord_211695
  simp only [CollatzResearch.WordTrace]
  refine ⟨7721150968072644472692539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5147433978715096315128359 7721150968072644472692539)
  ·
    refine ⟨11581726452108966709038809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7721150968072644472692539 11581726452108966709038809)
    ·
      refine ⟨8686294839081725031779107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11581726452108966709038809 8686294839081725031779107)
      ·
        refine ⟨13029442258622587547668661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8686294839081725031779107 13029442258622587547668661)
        ·
          refine ⟨1221510211745867582593937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13029442258622587547668661 1221510211745867582593937)
          ·
            refine ⟨916132658809400686945453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1221510211745867582593937 916132658809400686945453)
            ·
              refine ⟨343549747053525257604545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 916132658809400686945453 343549747053525257604545)
              ·
                refine ⟨257662310290143943203409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343549747053525257604545 257662310290143943203409)
                ·
                  refine ⟨193246732717607957402557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257662310290143943203409 193246732717607957402557)
                  ·
                    refine ⟨72467524769102984025959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193246732717607957402557 72467524769102984025959)
                    ·
                      rfl

theorem cell22_211695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 3].length) (baseStart_211695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211695 prefixEnd_211695 := by exact prefixLift 211695
  have htrace : WordTrace (prefixWord ++ tailWord_211695) baseStart_211695 baseEnd_211695 := by
    simpa [prefixWord, tailWord_211695, baseEnd_211695] using wordTrace_append hprefix tailTrace_211695
  have hstable : (prefixWord ++ tailWord_211695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211695).length < 2 ^ (prefixWord ++ tailWord_211695).sum := by decide
  have hdescent : baseEnd_211695 < baseStart_211695 := by decide
  rcases family_descends (prefixWord ++ tailWord_211695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211721 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 2, 6]
def baseStart_211721 : Nat := 118140960795 + 211721 * 2 ^ 59
def prefixEnd_211721 : Nat := 4983230072969 + 3 ^ 40 * 211721 * 2
def baseEnd_211721 : Nat := 72476425100447582875879

theorem tailTrace_211721 : CollatzResearch.WordTrace tailWord_211721 prefixEnd_211721 72476425100447582875879 := by
  unfold tailWord_211721
  simp only [CollatzResearch.WordTrace]
  refine ⟨7722099265978450913139017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5148066177318967275426011 7722099265978450913139017)
  ·
    refine ⟨5791574449483838184854263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7722099265978450913139017 5791574449483838184854263)
    ·
      refine ⟨8687361674225757277281395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5791574449483838184854263 8687361674225757277281395)
      ·
        refine ⟨13031042511338635915922093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8687361674225757277281395 13031042511338635915922093)
        ·
          refine ⟨4886640941751988468470785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13031042511338635915922093 4886640941751988468470785)
          ·
            refine ⟨3664980706313991351353089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4886640941751988468470785 3664980706313991351353089)
            ·
              refine ⟨2748735529735493513514817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3664980706313991351353089 2748735529735493513514817)
              ·
                refine ⟨2061551647301620135136113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2748735529735493513514817 2061551647301620135136113)
                ·
                  refine ⟨1546163735476215101352085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2061551647301620135136113 1546163735476215101352085)
                  ·
                    refine ⟨72476425100447582875879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1546163735476215101352085 72476425100447582875879)
                    ·
                      rfl

theorem cell22_211721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_211721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211721 prefixEnd_211721 := by exact prefixLift 211721
  have htrace : WordTrace (prefixWord ++ tailWord_211721) baseStart_211721 baseEnd_211721 := by
    simpa [prefixWord, tailWord_211721, baseEnd_211721] using wordTrace_append hprefix tailTrace_211721
  have hstable : (prefixWord ++ tailWord_211721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211721).length < 2 ^ (prefixWord ++ tailWord_211721).sum := by decide
  have hdescent : baseEnd_211721 < baseStart_211721 := by decide
  rcases family_descends (prefixWord ++ tailWord_211721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211770 : List Nat := [3, 1, 1, 1, 6, 1, 1, 3, 5]
def baseStart_211770 : Nat := 118140960795 + 211770 * 2 ^ 59
def prefixEnd_211770 : Nat := 4983230072969 + 3 ^ 40 * 211770 * 2
def baseEnd_211770 : Nat := 24164399600609262800243

theorem tailTrace_211770 : CollatzResearch.WordTrace tailWord_211770 prefixEnd_211770 24164399600609262800243 := by
  unfold tailWord_211770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1930971610700233070418191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5149257628533954854448509 1930971610700233070418191)
  ·
    refine ⟨2896457416050349605627287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1930971610700233070418191 2896457416050349605627287)
    ·
      refine ⟨4344686124075524408440931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2896457416050349605627287 4344686124075524408440931)
      ·
        refine ⟨6517029186113286612661397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4344686124075524408440931 6517029186113286612661397)
        ·
          refine ⟨305485743099060309968503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6517029186113286612661397 305485743099060309968503)
          ·
            refine ⟨458228614648590464952755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305485743099060309968503 458228614648590464952755)
            ·
              refine ⟨687342921972885697429133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458228614648590464952755 687342921972885697429133)
              ·
                refine ⟨257753595739832136535925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 687342921972885697429133 257753595739832136535925)
                ·
                  refine ⟨24164399600609262800243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 257753595739832136535925 24164399600609262800243)
                  ·
                    rfl

theorem cell22_211770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_211770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211770 prefixEnd_211770 := by exact prefixLift 211770
  have htrace : WordTrace (prefixWord ++ tailWord_211770) baseStart_211770 baseEnd_211770 := by
    simpa [prefixWord, tailWord_211770, baseEnd_211770] using wordTrace_append hprefix tailTrace_211770
  have hstable : (prefixWord ++ tailWord_211770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211770).length < 2 ^ (prefixWord ++ tailWord_211770).sum := by decide
  have hdescent : baseEnd_211770 < baseStart_211770 := by decide
  rcases family_descends (prefixWord ++ tailWord_211770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211845 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_211845 : Nat := 118140960795 + 211845 * 2 ^ 59
def prefixEnd_211845 : Nat := 4983230072969 + 3 ^ 40 * 211845 * 2
def baseEnd_211845 : Nat := 72518872834552592775499

theorem tailTrace_211845 : CollatzResearch.WordTrace tailWord_211845 prefixEnd_211845 72518872834552592775499 := by
  unfold tailWord_211845
  simp only [CollatzResearch.WordTrace]
  refine ⟨7726621917529220090652989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5151081278352813393768659 7726621917529220090652989)
  ·
    refine ⟨2897483219073457533994871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7726621917529220090652989 2897483219073457533994871)
    ·
      refine ⟨4346224828610186300992307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2897483219073457533994871 4346224828610186300992307)
      ·
        refine ⟨6519337242915279451488461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4346224828610186300992307 6519337242915279451488461)
        ·
          refine ⟨2444751466093229794308173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6519337242915279451488461 2444751466093229794308173)
          ·
            refine ⟨916781799784961172865565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2444751466093229794308173 916781799784961172865565)
            ·
              refine ⟨343793174919360439824587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 916781799784961172865565 343793174919360439824587)
              ·
                refine ⟨515689762379040659736881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343793174919360439824587 515689762379040659736881)
                ·
                  refine ⟨386767321784280494802661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515689762379040659736881 386767321784280494802661)
                  ·
                    refine ⟨72518872834552592775499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 386767321784280494802661 72518872834552592775499)
                    ·
                      rfl

theorem cell22_211845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_211845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211845 prefixEnd_211845 := by exact prefixLift 211845
  have htrace : WordTrace (prefixWord ++ tailWord_211845) baseStart_211845 baseEnd_211845 := by
    simpa [prefixWord, tailWord_211845, baseEnd_211845] using wordTrace_append hprefix tailTrace_211845
  have hstable : (prefixWord ++ tailWord_211845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211845).length < 2 ^ (prefixWord ++ tailWord_211845).sum := by decide
  have hdescent : baseEnd_211845 < baseStart_211845 := by decide
  rcases family_descends (prefixWord ++ tailWord_211845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211875 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 3, 3]
def baseStart_211875 : Nat := 118140960795 + 211875 * 2 ^ 59
def prefixEnd_211875 : Nat := 4983230072969 + 3 ^ 40 * 211875 * 2
def baseEnd_211875 : Nat := 72529142447642514525407

theorem tailTrace_211875 : CollatzResearch.WordTrace tailWord_211875 prefixEnd_211875 72529142447642514525407 := by
  unfold tailWord_211875
  simp only [CollatzResearch.WordTrace]
  refine ⟨7727716107420535214245079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5151810738280356809496719 7727716107420535214245079)
  ·
    refine ⟨11591574161130802821367619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7727716107420535214245079 11591574161130802821367619)
    ·
      refine ⟨17387361241696204232051429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11591574161130802821367619 17387361241696204232051429)
      ·
        refine ⟨3260130232818038293509643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17387361241696204232051429 3260130232818038293509643)
        ·
          refine ⟨4890195349227057440264465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3260130232818038293509643 4890195349227057440264465)
          ·
            refine ⟨3667646511920293080198349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4890195349227057440264465 3667646511920293080198349)
            ·
              refine ⟨1375367441970109905074381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3667646511920293080198349 1375367441970109905074381)
              ·
                refine ⟨515762790738791214402893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1375367441970109905074381 515762790738791214402893)
                ·
                  refine ⟨193411046527046705401085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515762790738791214402893 193411046527046705401085)
                  ·
                    refine ⟨72529142447642514525407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193411046527046705401085 72529142447642514525407)
                    ·
                      rfl

theorem cell22_211875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 3].length) (baseStart_211875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211875 prefixEnd_211875 := by exact prefixLift 211875
  have htrace : WordTrace (prefixWord ++ tailWord_211875) baseStart_211875 baseEnd_211875 := by
    simpa [prefixWord, tailWord_211875, baseEnd_211875] using wordTrace_append hprefix tailTrace_211875
  have hstable : (prefixWord ++ tailWord_211875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211875).length < 2 ^ (prefixWord ++ tailWord_211875).sum := by decide
  have hdescent : baseEnd_211875 < baseStart_211875 := by decide
  rcases family_descends (prefixWord ++ tailWord_211875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211903 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 4, 5]
def baseStart_211903 : Nat := 118140960795 + 211903 * 2 ^ 59
def prefixEnd_211903 : Nat := 4983230072969 + 3 ^ 40 * 211903 * 2
def baseEnd_211903 : Nat := 72538727419859774825321

theorem tailTrace_211903 : CollatzResearch.WordTrace tailWord_211903 prefixEnd_211903 72538727419859774825321 := by
  unfold tailWord_211903
  simp only [CollatzResearch.WordTrace]
  refine ⟨7728737351319095996264363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5152491567546063997509575 7728737351319095996264363)
  ·
    refine ⟨11593106026978643994396545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7728737351319095996264363 11593106026978643994396545)
    ·
      refine ⟨8694829520233982995797409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11593106026978643994396545 8694829520233982995797409)
      ·
        refine ⟨6521122140175487246848057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8694829520233982995797409 6521122140175487246848057)
        ·
          refine ⟨4890841605131615435136043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6521122140175487246848057 4890841605131615435136043)
          ·
            refine ⟨7336262407697423152704065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4890841605131615435136043 7336262407697423152704065)
            ·
              refine ⟨5502196805773067364528049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7336262407697423152704065 5502196805773067364528049)
              ·
                refine ⟨4126647604329800523396037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5502196805773067364528049 4126647604329800523396037)
                ·
                  refine ⟨773746425811837598136757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4126647604329800523396037 773746425811837598136757)
                  ·
                    refine ⟨72538727419859774825321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 773746425811837598136757 72538727419859774825321)
                    ·
                      rfl

theorem cell22_211903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_211903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211903 prefixEnd_211903 := by exact prefixLift 211903
  have htrace : WordTrace (prefixWord ++ tailWord_211903) baseStart_211903 baseEnd_211903 := by
    simpa [prefixWord, tailWord_211903, baseEnd_211903] using wordTrace_append hprefix tailTrace_211903
  have hstable : (prefixWord ++ tailWord_211903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211903).length < 2 ^ (prefixWord ++ tailWord_211903).sum := by decide
  have hdescent : baseEnd_211903 < baseStart_211903 := by decide
  rcases family_descends (prefixWord ++ tailWord_211903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211926 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_211926 : Nat := 118140960795 + 211926 * 2 ^ 59
def prefixEnd_211926 : Nat := 4983230072969 + 3 ^ 40 * 211926 * 2
def baseEnd_211926 : Nat := 72546600789895381500251

theorem tailTrace_211926 : CollatzResearch.WordTrace tailWord_211926 prefixEnd_211926 72546600789895381500251 := by
  unfold tailWord_211926
  simp only [CollatzResearch.WordTrace]
  refine ⟨483098514389735682771977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5153050820157180616234421 483098514389735682771977)
  ·
    refine ⟨362323885792301762078983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 483098514389735682771977 362323885792301762078983)
    ·
      refine ⟨543485828688452643118475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362323885792301762078983 543485828688452643118475)
      ·
        refine ⟨815228743032678964677713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543485828688452643118475 815228743032678964677713)
        ·
          refine ⟨611421557274509223508285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 815228743032678964677713 611421557274509223508285)
          ·
            refine ⟨229283083977940958815607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 611421557274509223508285 229283083977940958815607)
            ·
              refine ⟨343924625966911438223411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229283083977940958815607 343924625966911438223411)
              ·
                refine ⟨515886938950367157335117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343924625966911438223411 515886938950367157335117)
                ·
                  refine ⟨193457602106387684000669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515886938950367157335117 193457602106387684000669)
                  ·
                    refine ⟨72546600789895381500251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193457602106387684000669 72546600789895381500251)
                    ·
                      rfl

theorem cell22_211926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_211926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211926 prefixEnd_211926 := by exact prefixLift 211926
  have htrace : WordTrace (prefixWord ++ tailWord_211926) baseStart_211926 baseEnd_211926 := by
    simpa [prefixWord, tailWord_211926, baseEnd_211926] using wordTrace_append hprefix tailTrace_211926
  have hstable : (prefixWord ++ tailWord_211926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211926).length < 2 ^ (prefixWord ++ tailWord_211926).sum := by decide
  have hdescent : baseEnd_211926 < baseStart_211926 := by decide
  rcases family_descends (prefixWord ++ tailWord_211926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211969 : List Nat := [1, 2, 4, 1, 2, 3, 3, 1, 1, 4]
def baseStart_211969 : Nat := 118140960795 + 211969 * 2 ^ 59
def prefixEnd_211969 : Nat := 4983230072969 + 3 ^ 40 * 211969 * 2
def baseEnd_211969 : Nat := 72561320568657602675119

theorem tailTrace_211969 : CollatzResearch.WordTrace tailWord_211969 prefixEnd_211969 72561320568657602675119 := by
  unfold tailWord_211969
  simp only [CollatzResearch.WordTrace]
  refine ⟨7731144569079989268166961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5154096379386659512111307 7731144569079989268166961)
  ·
    refine ⟨5798358426809991951125221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7731144569079989268166961 5798358426809991951125221)
    ·
      refine ⟨1087192205026873490835979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5798358426809991951125221 1087192205026873490835979)
      ·
        refine ⟨1630788307540310236253969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087192205026873490835979 1630788307540310236253969)
        ·
          refine ⟨1223091230655232677190477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1630788307540310236253969 1223091230655232677190477)
          ·
            refine ⟨458659211495712253946429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1223091230655232677190477 458659211495712253946429)
            ·
              refine ⟨171997204310892095229911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 458659211495712253946429 171997204310892095229911)
              ·
                refine ⟨257995806466338142844867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171997204310892095229911 257995806466338142844867)
                ·
                  refine ⟨386993709699507214267301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257995806466338142844867 386993709699507214267301)
                  ·
                    refine ⟨72561320568657602675119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 386993709699507214267301 72561320568657602675119)
                    ·
                      rfl

theorem cell22_211969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_211969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_211969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_211969 prefixEnd_211969 := by exact prefixLift 211969
  have htrace : WordTrace (prefixWord ++ tailWord_211969) baseStart_211969 baseEnd_211969 := by
    simpa [prefixWord, tailWord_211969, baseEnd_211969] using wordTrace_append hprefix tailTrace_211969
  have hstable : (prefixWord ++ tailWord_211969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211969).length < 2 ^ (prefixWord ++ tailWord_211969).sum := by decide
  have hdescent : baseEnd_211969 < baseStart_211969 := by decide
  rcases family_descends (prefixWord ++ tailWord_211969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212033 : List Nat := [1, 2, 5, 1, 4, 1, 1, 2, 2, 3]
def baseStart_212033 : Nat := 118140960795 + 212033 * 2 ^ 59
def prefixEnd_212033 : Nat := 4983230072969 + 3 ^ 40 * 212033 * 2
def baseEnd_212033 : Nat := 72583229076582769074923

theorem tailTrace_212033 : CollatzResearch.WordTrace tailWord_212033 prefixEnd_212033 72583229076582769074923 := by
  unfold tailWord_212033
  simp only [CollatzResearch.WordTrace]
  refine ⟨7733478840848128198496753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5155652560565418798997835 7733478840848128198496753)
  ·
    refine ⟨5800109130636096148872565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7733478840848128198496753 5800109130636096148872565)
    ·
      refine ⟨543760230997134013956803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5800109130636096148872565 543760230997134013956803)
      ·
        refine ⟨815640346495701020935205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543760230997134013956803 815640346495701020935205)
        ·
          refine ⟨152932564967943941425351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 815640346495701020935205 152932564967943941425351)
          ·
            refine ⟨229398847451915912138027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152932564967943941425351 229398847451915912138027)
            ·
              refine ⟨344098271177873868207041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229398847451915912138027 344098271177873868207041)
              ·
                refine ⟨258073703383405401155281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344098271177873868207041 258073703383405401155281)
                ·
                  refine ⟨193555277537554050866461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258073703383405401155281 193555277537554050866461)
                  ·
                    refine ⟨72583229076582769074923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193555277537554050866461 72583229076582769074923)
                    ·
                      rfl

theorem cell22_212033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_212033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212033 prefixEnd_212033 := by exact prefixLift 212033
  have htrace : WordTrace (prefixWord ++ tailWord_212033) baseStart_212033 baseEnd_212033 := by
    simpa [prefixWord, tailWord_212033, baseEnd_212033] using wordTrace_append hprefix tailTrace_212033
  have hstable : (prefixWord ++ tailWord_212033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212033).length < 2 ^ (prefixWord ++ tailWord_212033).sum := by decide
  have hdescent : baseEnd_212033 < baseStart_212033 := by decide
  rcases family_descends (prefixWord ++ tailWord_212033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212040 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 7]
def baseStart_212040 : Nat := 118140960795 + 212040 * 2 ^ 59
def prefixEnd_212040 : Nat := 4983230072969 + 3 ^ 40 * 212040 * 2
def baseEnd_212040 : Nat := 24195208439879028049967

theorem tailTrace_212040 : CollatzResearch.WordTrace tailWord_212040 prefixEnd_212040 24195208439879028049967 := by
  unfold tailWord_212040
  simp only [CollatzResearch.WordTrace]
  refine ⟨3866867075911384197000787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5155822767881845596001049 3866867075911384197000787)
  ·
    refine ⟨5800300613867076295501181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3866867075911384197000787 5800300613867076295501181)
    ·
      refine ⟨2175112730200153610812943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5800300613867076295501181 2175112730200153610812943)
      ·
        refine ⟨3262669095300230416219415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175112730200153610812943 3262669095300230416219415)
        ·
          refine ⟨4894003642950345624329123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262669095300230416219415 4894003642950345624329123)
          ·
            refine ⟨7341005464425518436493685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4894003642950345624329123 7341005464425518436493685)
            ·
              refine ⟨688219262289892353421283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7341005464425518436493685 688219262289892353421283)
              ·
                refine ⟨1032328893434838530131925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688219262289892353421283 1032328893434838530131925)
                ·
                  refine ⟨24195208439879028049967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1032328893434838530131925 24195208439879028049967)
                  ·
                    rfl

theorem cell22_212040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_212040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212040 prefixEnd_212040 := by exact prefixLift 212040
  have htrace : WordTrace (prefixWord ++ tailWord_212040) baseStart_212040 baseEnd_212040 := by
    simpa [prefixWord, tailWord_212040, baseEnd_212040] using wordTrace_append hprefix tailTrace_212040
  have hstable : (prefixWord ++ tailWord_212040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212040).length < 2 ^ (prefixWord ++ tailWord_212040).sum := by decide
  have hdescent : baseEnd_212040 < baseStart_212040 := by decide
  rcases family_descends (prefixWord ++ tailWord_212040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212078 : List Nat := [4, 1, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_212078 : Nat := 118140960795 + 212078 * 2 ^ 59
def prefixEnd_212078 : Nat := 4983230072969 + 3 ^ 40 * 212078 * 2
def baseEnd_212078 : Nat := 72598633496217651699785

theorem tailTrace_212078 : CollatzResearch.WordTrace tailWord_212078 prefixEnd_212078 72598633496217651699785 := by
  unfold tailWord_212078
  simp only [CollatzResearch.WordTrace]
  refine ⟨966890015710637610485611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5156746750456733922589925 966890015710637610485611)
  ·
    refine ⟨1450335023565956415728417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 966890015710637610485611 1450335023565956415728417)
    ·
      refine ⟨1087751267674467311796313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1450335023565956415728417 1087751267674467311796313)
      ·
        refine ⟨815813450755850483847235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1087751267674467311796313 815813450755850483847235)
        ·
          refine ⟨1223720176133775725770853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815813450755850483847235 1223720176133775725770853)
          ·
            refine ⟨229447533025082948582035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1223720176133775725770853 229447533025082948582035)
            ·
              refine ⟨344171299537624422873053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229447533025082948582035 344171299537624422873053)
              ·
                refine ⟨129064237326609158577395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344171299537624422873053 129064237326609158577395)
                ·
                  refine ⟨193596355989913737866093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129064237326609158577395 193596355989913737866093)
                  ·
                    refine ⟨72598633496217651699785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193596355989913737866093 72598633496217651699785)
                    ·
                      rfl

theorem cell22_212078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_212078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212078 prefixEnd_212078 := by exact prefixLift 212078
  have htrace : WordTrace (prefixWord ++ tailWord_212078) baseStart_212078 baseEnd_212078 := by
    simpa [prefixWord, tailWord_212078, baseEnd_212078] using wordTrace_append hprefix tailTrace_212078
  have hstable : (prefixWord ++ tailWord_212078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212078).length < 2 ^ (prefixWord ++ tailWord_212078).sum := by decide
  have hdescent : baseEnd_212078 < baseStart_212078 := by decide
  rcases family_descends (prefixWord ++ tailWord_212078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212087 : List Nat := [1, 1, 3, 1, 1, 4, 1, 5, 1, 4]
def baseStart_212087 : Nat := 118140960795 + 212087 * 2 ^ 59
def prefixEnd_212087 : Nat := 4983230072969 + 3 ^ 40 * 212087 * 2
def baseEnd_212087 : Nat := 72601714380144628224757

theorem tailTrace_212087 : CollatzResearch.WordTrace tailWord_212087 prefixEnd_212087 72601714380144628224757 := by
  unfold tailWord_212087
  simp only [CollatzResearch.WordTrace]
  refine ⟨7735448382652495420962515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5156965588434996947308343 7735448382652495420962515)
  ·
    refine ⟨11603172573978743131443773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7735448382652495420962515 11603172573978743131443773)
    ·
      refine ⟨4351189715242028674291415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11603172573978743131443773 4351189715242028674291415)
      ·
        refine ⟨6526784572863043011437123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4351189715242028674291415 6526784572863043011437123)
        ·
          refine ⟨9790176859294564517155685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6526784572863043011437123 9790176859294564517155685)
          ·
            refine ⟨1835658161117730846966691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9790176859294564517155685 1835658161117730846966691)
            ·
              refine ⟨2753487241676596270450037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835658161117730846966691 2753487241676596270450037)
              ·
                refine ⟨258139428907180900354691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2753487241676596270450037 258139428907180900354691)
                ·
                  refine ⟨387209143360771350532037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258139428907180900354691 387209143360771350532037)
                  ·
                    refine ⟨72601714380144628224757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 387209143360771350532037 72601714380144628224757)
                    ·
                      rfl

theorem cell22_212087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_212087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212087 prefixEnd_212087 := by exact prefixLift 212087
  have htrace : WordTrace (prefixWord ++ tailWord_212087) baseStart_212087 baseEnd_212087 := by
    simpa [prefixWord, tailWord_212087, baseEnd_212087] using wordTrace_append hprefix tailTrace_212087
  have hstable : (prefixWord ++ tailWord_212087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212087).length < 2 ^ (prefixWord ++ tailWord_212087).sum := by decide
  have hdescent : baseEnd_212087 < baseStart_212087 := by decide
  rcases family_descends (prefixWord ++ tailWord_212087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212115 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 3, 6]
def baseStart_212115 : Nat := 118140960795 + 212115 * 2 ^ 59
def prefixEnd_212115 : Nat := 4983230072969 + 3 ^ 40 * 212115 * 2
def baseEnd_212115 : Nat := 72611299352361888524671

theorem tailTrace_212115 : CollatzResearch.WordTrace tailWord_212115 prefixEnd_212115 72611299352361888524671 := by
  unfold tailWord_212115
  simp only [CollatzResearch.WordTrace]
  refine ⟨7736469626551056202981799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5157646417700704135321199 7736469626551056202981799)
  ·
    refine ⟨11604704439826584304472699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7736469626551056202981799 11604704439826584304472699)
    ·
      refine ⟨17407056659739876456709049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11604704439826584304472699 17407056659739876456709049)
      ·
        refine ⟨13055292494804907342531787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17407056659739876456709049 13055292494804907342531787)
        ·
          refine ⟨19582938742207361013797681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13055292494804907342531787 19582938742207361013797681)
          ·
            refine ⟨14687204056655520760348261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19582938742207361013797681 14687204056655520760348261)
            ·
              refine ⟨2753850760622910142565299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14687204056655520760348261 2753850760622910142565299)
              ·
                refine ⟨4130776140934365213847949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753850760622910142565299 4130776140934365213847949)
                ·
                  refine ⟨1549041052850386955192981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4130776140934365213847949 1549041052850386955192981)
                  ·
                    refine ⟨72611299352361888524671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1549041052850386955192981 72611299352361888524671)
                    ·
                      rfl

theorem cell22_212115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_212115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212115 prefixEnd_212115 := by exact prefixLift 212115
  have htrace : WordTrace (prefixWord ++ tailWord_212115) baseStart_212115 baseEnd_212115 := by
    simpa [prefixWord, tailWord_212115, baseEnd_212115] using wordTrace_append hprefix tailTrace_212115
  have hstable : (prefixWord ++ tailWord_212115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212115).length < 2 ^ (prefixWord ++ tailWord_212115).sum := by decide
  have hdescent : baseEnd_212115 < baseStart_212115 := by decide
  rcases family_descends (prefixWord ++ tailWord_212115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212117 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 6, 3]
def baseStart_212117 : Nat := 118140960795 + 212117 * 2 ^ 59
def prefixEnd_212117 : Nat := 4983230072969 + 3 ^ 40 * 212117 * 2
def baseEnd_212117 : Nat := 72611983993234549974665

theorem tailTrace_212117 : CollatzResearch.WordTrace tailWord_212117 prefixEnd_212117 72611983993234549974665 := by
  unfold tailWord_212117
  simp only [CollatzResearch.WordTrace]
  refine ⟨7736542572543810544554605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5157695048362540363036403 7736542572543810544554605)
  ·
    refine ⟨2901203464703928954207977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7736542572543810544554605 2901203464703928954207977)
    ·
      refine ⟨2175902598527946715655983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2901203464703928954207977 2175902598527946715655983)
      ·
        refine ⟨3263853897791920073483975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175902598527946715655983 3263853897791920073483975)
        ·
          refine ⟨4895780846687880110225963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3263853897791920073483975 4895780846687880110225963)
          ·
            refine ⟨7343671270031820165338945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895780846687880110225963 7343671270031820165338945)
            ·
              refine ⟨5507753452523865124004209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7343671270031820165338945 5507753452523865124004209)
              ·
                refine ⟨4130815089392898843003157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5507753452523865124004209 4130815089392898843003157)
                ·
                  refine ⟨193631957315292133265773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4130815089392898843003157 193631957315292133265773)
                  ·
                    refine ⟨72611983993234549974665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193631957315292133265773 72611983993234549974665)
                    ·
                      rfl

theorem cell22_212117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_212117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212117 prefixEnd_212117 := by exact prefixLift 212117
  have htrace : WordTrace (prefixWord ++ tailWord_212117) baseStart_212117 baseEnd_212117 := by
    simpa [prefixWord, tailWord_212117, baseEnd_212117] using wordTrace_append hprefix tailTrace_212117
  have hstable : (prefixWord ++ tailWord_212117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212117).length < 2 ^ (prefixWord ++ tailWord_212117).sum := by decide
  have hdescent : baseEnd_212117 < baseStart_212117 := by decide
  rcases family_descends (prefixWord ++ tailWord_212117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212138 : List Nat := [3, 1, 5, 1, 1, 2, 3, 1, 1, 4]
def baseStart_212138 : Nat := 118140960795 + 212138 * 2 ^ 59
def prefixEnd_212138 : Nat := 4983230072969 + 3 ^ 40 * 212138 * 2
def baseEnd_212138 : Nat := 72619172722397495199601

theorem tailTrace_212138 : CollatzResearch.WordTrace tailWord_212138 prefixEnd_212138 72619172722397495199601 := by
  unfold tailWord_212138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1934327126366932782767267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5158205670311820754046045 1934327126366932782767267)
  ·
    refine ⟨2901490689550399174150901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1934327126366932782767267 2901490689550399174150901)
    ·
      refine ⟨272014752145349922576647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2901490689550399174150901 272014752145349922576647)
      ·
        refine ⟨408022128218024883864971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272014752145349922576647 408022128218024883864971)
        ·
          refine ⟨612033192327037325797457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408022128218024883864971 612033192327037325797457)
          ·
            refine ⟨459024894245277994348093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612033192327037325797457 459024894245277994348093)
            ·
              refine ⟨172134335341979247880535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 459024894245277994348093 172134335341979247880535)
              ·
                refine ⟨258201503012968871820803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172134335341979247880535 258201503012968871820803)
                ·
                  refine ⟨387302254519453307731205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258201503012968871820803 387302254519453307731205)
                  ·
                    refine ⟨72619172722397495199601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 387302254519453307731205 72619172722397495199601)
                    ·
                      rfl

theorem cell22_212138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_212138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212138 prefixEnd_212138 := by exact prefixLift 212138
  have htrace : WordTrace (prefixWord ++ tailWord_212138) baseStart_212138 baseEnd_212138 := by
    simpa [prefixWord, tailWord_212138, baseEnd_212138] using wordTrace_append hprefix tailTrace_212138
  have hstable : (prefixWord ++ tailWord_212138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212138).length < 2 ^ (prefixWord ++ tailWord_212138).sum := by decide
  have hdescent : baseEnd_212138 < baseStart_212138 := by decide
  rcases family_descends (prefixWord ++ tailWord_212138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212196 : List Nat := [2, 3, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_212196 : Nat := 118140960795 + 212196 * 2 ^ 59
def prefixEnd_212196 : Nat := 4983230072969 + 3 ^ 40 * 212196 * 2
def baseEnd_212196 : Nat := 72639027307704677249423

theorem tailTrace_212196 : CollatzResearch.WordTrace tailWord_212196 prefixEnd_212196 72639027307704677249423 := by
  unfold tailWord_212196
  simp only [CollatzResearch.WordTrace]
  refine ⟨3869711969628803518340221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5159615959505071357786961 3869711969628803518340221)
  ·
    refine ⟨1451141988610801319377583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3869711969628803518340221 1451141988610801319377583)
    ·
      refine ⟨2176712982916201979066375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1451141988610801319377583 2176712982916201979066375)
      ·
        refine ⟨3265069474374302968599563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176712982916201979066375 3265069474374302968599563)
        ·
          refine ⟨4897604211561454452899345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3265069474374302968599563 4897604211561454452899345)
          ·
            refine ⟨3673203158671090839674509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4897604211561454452899345 3673203158671090839674509)
            ·
              refine ⟨1377451184501659064877941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3673203158671090839674509 1377451184501659064877941)
              ·
                refine ⟨129136048547030537332307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1377451184501659064877941 129136048547030537332307)
                ·
                  refine ⟨193704072820545805998461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129136048547030537332307 193704072820545805998461)
                  ·
                    refine ⟨72639027307704677249423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193704072820545805998461 72639027307704677249423)
                    ·
                      rfl

theorem cell22_212196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_212196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212196 prefixEnd_212196 := by exact prefixLift 212196
  have htrace : WordTrace (prefixWord ++ tailWord_212196) baseStart_212196 baseEnd_212196 := by
    simpa [prefixWord, tailWord_212196, baseEnd_212196] using wordTrace_append hprefix tailTrace_212196
  have hstable : (prefixWord ++ tailWord_212196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212196).length < 2 ^ (prefixWord ++ tailWord_212196).sum := by decide
  have hdescent : baseEnd_212196 < baseStart_212196 := by decide
  rcases family_descends (prefixWord ++ tailWord_212196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212297 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 2, 7]
def baseStart_212297 : Nat := 118140960795 + 212297 * 2 ^ 59
def prefixEnd_212297 : Nat := 4983230072969 + 3 ^ 40 * 212297 * 2
def baseEnd_212297 : Nat := 72673601671774080474113

theorem tailTrace_212297 : CollatzResearch.WordTrace tailWord_212297 prefixEnd_212297 72673601671774080474113 := by
  unfold tailWord_212297
  simp only [CollatzResearch.WordTrace]
  refine ⟨7743107711891701286107145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5162071807927800857404763 7743107711891701286107145)
  ·
    refine ⟨5807330783918775964580359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7743107711891701286107145 5807330783918775964580359)
    ·
      refine ⟨8710996175878163946870539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5807330783918775964580359 8710996175878163946870539)
      ·
        refine ⟨13066494263817245920305809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8710996175878163946870539 13066494263817245920305809)
        ·
          refine ⟨9799870697862934440229357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13066494263817245920305809 9799870697862934440229357)
          ·
            refine ⟨3674951511698600415086009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9799870697862934440229357 3674951511698600415086009)
            ·
              refine ⟨2756213633773950311314507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3674951511698600415086009 2756213633773950311314507)
              ·
                refine ⟨4134320450660925466971761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756213633773950311314507 4134320450660925466971761)
                ·
                  refine ⟨3100740337995694100228821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4134320450660925466971761 3100740337995694100228821)
                  ·
                    refine ⟨72673601671774080474113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3100740337995694100228821 72673601671774080474113)
                    ·
                      rfl

theorem cell22_212297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_212297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212297 prefixEnd_212297 := by exact prefixLift 212297
  have htrace : WordTrace (prefixWord ++ tailWord_212297) baseStart_212297 baseEnd_212297 := by
    simpa [prefixWord, tailWord_212297, baseEnd_212297] using wordTrace_append hprefix tailTrace_212297
  have hstable : (prefixWord ++ tailWord_212297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212297).length < 2 ^ (prefixWord ++ tailWord_212297).sum := by decide
  have hdescent : baseEnd_212297 < baseStart_212297 := by decide
  rcases family_descends (prefixWord ++ tailWord_212297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212350 : List Nat := [4, 2, 3, 2, 1, 1, 3, 6]
def baseStart_212350 : Nat := 118140960795 + 212350 * 2 ^ 59
def prefixEnd_212350 : Nat := 4983230072969 + 3 ^ 40 * 212350 * 2
def baseEnd_212350 : Nat := 8076860517211067655439

theorem tailTrace_212350 : CollatzResearch.WordTrace tailWord_212350 prefixEnd_212350 8076860517211067655439 := by
  unfold tailWord_212350
  simp only [CollatzResearch.WordTrace]
  refine ⟨968130097587461417223313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5163360520466460891857669 968130097587461417223313)
  ·
    refine ⟨726097573190596062917485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 968130097587461417223313 726097573190596062917485)
    ·
      refine ⟨272286589946473523594057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 726097573190596062917485 272286589946473523594057)
      ·
        refine ⟨204214942459855142695543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272286589946473523594057 204214942459855142695543)
        ·
          refine ⟨306322413689782714043315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204214942459855142695543 306322413689782714043315)
          ·
            refine ⟨459483620534674071064973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306322413689782714043315 459483620534674071064973)
            ·
              refine ⟨172306357700502776649365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 459483620534674071064973 172306357700502776649365)
              ·
                refine ⟨8076860517211067655439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172306357700502776649365 8076860517211067655439)
                ·
                  rfl

theorem cell22_212350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_212350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212350 prefixEnd_212350 := by exact prefixLift 212350
  have htrace : WordTrace (prefixWord ++ tailWord_212350) baseStart_212350 baseEnd_212350 := by
    simpa [prefixWord, tailWord_212350, baseEnd_212350] using wordTrace_append hprefix tailTrace_212350
  have hstable : (prefixWord ++ tailWord_212350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212350).length < 2 ^ (prefixWord ++ tailWord_212350).sum := by decide
  have hdescent : baseEnd_212350 < baseStart_212350 := by decide
  rcases family_descends (prefixWord ++ tailWord_212350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212419 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 1, 6]
def baseStart_212419 : Nat := 118140960795 + 212419 * 2 ^ 59
def prefixEnd_212419 : Nat := 4983230072969 + 3 ^ 40 * 212419 * 2
def baseEnd_212419 : Nat := 72715364765006428923739

theorem tailTrace_212419 : CollatzResearch.WordTrace tailWord_212419 prefixEnd_212419 72715364765006428923739 := by
  unfold tailWord_212419
  simp only [CollatzResearch.WordTrace]
  refine ⟨7747557417449716122048311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5165038278299810748032207 7747557417449716122048311)
  ·
    refine ⟨11621336126174574183072467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7747557417449716122048311 11621336126174574183072467)
    ·
      refine ⟨17432004189261861274608701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11621336126174574183072467 17432004189261861274608701)
      ·
        refine ⟨6537001570973197977978263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17432004189261861274608701 6537001570973197977978263)
        ·
          refine ⟨9805502356459796966967395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6537001570973197977978263 9805502356459796966967395)
          ·
            refine ⟨14708253534689695450451093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9805502356459796966967395 14708253534689695450451093)
            ·
              refine ⟨689449384438579474239895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14708253534689695450451093 689449384438579474239895)
              ·
                refine ⟨1034174076657869211359843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689449384438579474239895 1034174076657869211359843)
                ·
                  refine ⟨1551261114986803817039765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034174076657869211359843 1551261114986803817039765)
                  ·
                    refine ⟨72715364765006428923739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1551261114986803817039765 72715364765006428923739)
                    ·
                      rfl

theorem cell22_212419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 6].length) (baseStart_212419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212419 prefixEnd_212419 := by exact prefixLift 212419
  have htrace : WordTrace (prefixWord ++ tailWord_212419) baseStart_212419 baseEnd_212419 := by
    simpa [prefixWord, tailWord_212419, baseEnd_212419] using wordTrace_append hprefix tailTrace_212419
  have hstable : (prefixWord ++ tailWord_212419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212419).length < 2 ^ (prefixWord ++ tailWord_212419).sum := by decide
  have hdescent : baseEnd_212419 < baseStart_212419 := by decide
  rcases family_descends (prefixWord ++ tailWord_212419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212451 : List Nat := [1, 1, 1, 6, 2, 2, 2, 7]
def baseStart_212451 : Nat := 118140960795 + 212451 * 2 ^ 59
def prefixEnd_212451 : Nat := 4983230072969 + 3 ^ 40 * 212451 * 2
def baseEnd_212451 : Nat := 8080702113218779124849

theorem tailTrace_212451 : CollatzResearch.WordTrace tailWord_212451 prefixEnd_212451 8080702113218779124849 := by
  unfold tailWord_212451
  simp only [CollatzResearch.WordTrace]
  refine ⟨7748724553333785587213207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5165816368889190391475471 7748724553333785587213207)
  ·
    refine ⟨11623086830000678380819811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7748724553333785587213207 11623086830000678380819811)
    ·
      refine ⟨17434630245001017571229717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11623086830000678380819811 17434630245001017571229717)
      ·
        refine ⟨817248292734422698651393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17434630245001017571229717 817248292734422698651393)
        ·
          refine ⟨612936219550817023988545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 817248292734422698651393 612936219550817023988545)
          ·
            refine ⟨459702164663112767991409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612936219550817023988545 459702164663112767991409)
            ·
              refine ⟨344776623497334575993557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459702164663112767991409 344776623497334575993557)
              ·
                refine ⟨8080702113218779124849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 344776623497334575993557 8080702113218779124849)
                ·
                  rfl

theorem cell22_212451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 7].length) (baseStart_212451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212451 prefixEnd_212451 := by exact prefixLift 212451
  have htrace : WordTrace (prefixWord ++ tailWord_212451) baseStart_212451 baseEnd_212451 := by
    simpa [prefixWord, tailWord_212451, baseEnd_212451] using wordTrace_append hprefix tailTrace_212451
  have hstable : (prefixWord ++ tailWord_212451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212451).length < 2 ^ (prefixWord ++ tailWord_212451).sum := by decide
  have hdescent : baseEnd_212451 < baseStart_212451 := by decide
  rcases family_descends (prefixWord ++ tailWord_212451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212455 : List Nat := [1, 1, 5, 2, 1, 2, 4, 1, 2, 3]
def baseStart_212455 : Nat := 118140960795 + 212455 * 2 ^ 59
def prefixEnd_212455 : Nat := 4983230072969 + 3 ^ 40 * 212455 * 2
def baseEnd_212455 : Nat := 72727688300714335023629

theorem tailTrace_212455 : CollatzResearch.WordTrace tailWord_212455 prefixEnd_212455 72727688300714335023629 := by
  unfold tailWord_212455
  simp only [CollatzResearch.WordTrace]
  refine ⟨7748870445319294270358819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5165913630212862846905879 7748870445319294270358819)
  ·
    refine ⟨11623305667978941405538229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7748870445319294270358819 11623305667978941405538229)
    ·
      refine ⟨1089684906373025756769209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11623305667978941405538229 1089684906373025756769209)
      ·
        refine ⟨817263679779769317576907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1089684906373025756769209 817263679779769317576907)
        ·
          refine ⟨1225895519669653976365361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817263679779769317576907 1225895519669653976365361)
          ·
            refine ⟨919421639752240482274021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225895519669653976365361 919421639752240482274021)
            ·
              refine ⟨172391557453545090426379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 919421639752240482274021 172391557453545090426379)
              ·
                refine ⟨258587336180317635639569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172391557453545090426379 258587336180317635639569)
                ·
                  refine ⟨193940502135238226729677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258587336180317635639569 193940502135238226729677)
                  ·
                    refine ⟨72727688300714335023629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193940502135238226729677 72727688300714335023629)
                    ·
                      rfl

theorem cell22_212455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_212455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212455 prefixEnd_212455 := by exact prefixLift 212455
  have htrace : WordTrace (prefixWord ++ tailWord_212455) baseStart_212455 baseEnd_212455 := by
    simpa [prefixWord, tailWord_212455, baseEnd_212455] using wordTrace_append hprefix tailTrace_212455
  have hstable : (prefixWord ++ tailWord_212455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212455).length < 2 ^ (prefixWord ++ tailWord_212455).sum := by decide
  have hdescent : baseEnd_212455 < baseStart_212455 := by decide
  rcases family_descends (prefixWord ++ tailWord_212455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212479 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 7]
def baseStart_212479 : Nat := 118140960795 + 212479 * 2 ^ 59
def prefixEnd_212479 : Nat := 4983230072969 + 3 ^ 40 * 212479 * 2
def baseEnd_212479 : Nat := 24245301330395424141185

theorem tailTrace_212479 : CollatzResearch.WordTrace tailWord_212479 prefixEnd_212479 24245301330395424141185 := by
  unfold tailWord_212479
  simp only [CollatzResearch.WordTrace]
  refine ⟨7749745797232346369232491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5166497198154897579488327 7749745797232346369232491)
  ·
    refine ⟨11624618695848519553848737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7749745797232346369232491 11624618695848519553848737)
    ·
      refine ⟨8718464021886389665386553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11624618695848519553848737 8718464021886389665386553)
      ·
        refine ⟨6538848016414792249039915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8718464021886389665386553 6538848016414792249039915)
        ·
          refine ⟨9808272024622188373559873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6538848016414792249039915 9808272024622188373559873)
          ·
            refine ⟨7356204018466641280169905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9808272024622188373559873 7356204018466641280169905)
            ·
              refine ⟨5517153013849980960127429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7356204018466641280169905 5517153013849980960127429)
              ·
                refine ⟨1034466190096871430023893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5517153013849980960127429 1034466190096871430023893)
                ·
                  refine ⟨24245301330395424141185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1034466190096871430023893 24245301330395424141185)
                  ·
                    rfl

theorem cell22_212479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 7].length) (baseStart_212479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212479 prefixEnd_212479 := by exact prefixLift 212479
  have htrace : WordTrace (prefixWord ++ tailWord_212479) baseStart_212479 baseEnd_212479 := by
    simpa [prefixWord, tailWord_212479, baseEnd_212479] using wordTrace_append hprefix tailTrace_212479
  have hstable : (prefixWord ++ tailWord_212479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212479).length < 2 ^ (prefixWord ++ tailWord_212479).sum := by decide
  have hdescent : baseEnd_212479 < baseStart_212479 := by decide
  rcases family_descends (prefixWord ++ tailWord_212479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212534 : List Nat := [5, 1, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_212534 : Nat := 118140960795 + 212534 * 2 ^ 59
def prefixEnd_212534 : Nat := 4983230072969 + 3 ^ 40 * 212534 * 2
def baseEnd_212534 : Nat := 72754731615184462298387

theorem tailTrace_212534 : CollatzResearch.WordTrace tailWord_212534 prefixEnd_212534 72754731615184462298387 := by
  unfold tailWord_212534
  simp only [CollatzResearch.WordTrace]
  refine ⟨484484488252068172655291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5167834541355393841656437 484484488252068172655291)
  ·
    refine ⟨726726732378102258982937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 484484488252068172655291 726726732378102258982937)
    ·
      refine ⟨545045049283576694237203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 726726732378102258982937 545045049283576694237203)
      ·
        refine ⟨817567573925365041355805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545045049283576694237203 817567573925365041355805)
        ·
          refine ⟨306587840222011890508427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 817567573925365041355805 306587840222011890508427)
          ·
            refine ⟨459881760333017835762641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306587840222011890508427 459881760333017835762641)
            ·
              refine ⟨344911320249763376821981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459881760333017835762641 344911320249763376821981)
              ·
                refine ⟨129341745093661266308243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344911320249763376821981 129341745093661266308243)
                ·
                  refine ⟨194012617640491899462365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129341745093661266308243 194012617640491899462365)
                  ·
                    refine ⟨72754731615184462298387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194012617640491899462365 72754731615184462298387)
                    ·
                      rfl

theorem cell22_212534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_212534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212534 prefixEnd_212534 := by exact prefixLift 212534
  have htrace : WordTrace (prefixWord ++ tailWord_212534) baseStart_212534 baseEnd_212534 := by
    simpa [prefixWord, tailWord_212534, baseEnd_212534] using wordTrace_append hprefix tailTrace_212534
  have hstable : (prefixWord ++ tailWord_212534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212534).length < 2 ^ (prefixWord ++ tailWord_212534).sum := by decide
  have hdescent : baseEnd_212534 < baseStart_212534 := by decide
  rcases family_descends (prefixWord ++ tailWord_212534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212543 : List Nat := [1, 1, 2, 2, 3, 4, 1, 3, 1, 4]
def baseStart_212543 : Nat := 118140960795 + 212543 * 2 ^ 59
def prefixEnd_212543 : Nat := 4983230072969 + 3 ^ 40 * 212543 * 2
def baseEnd_212543 : Nat := 72757812499111438823359

theorem tailTrace_212543 : CollatzResearch.WordTrace tailWord_212543 prefixEnd_212543 72757812499111438823359 := by
  unfold tailWord_212543
  simp only [CollatzResearch.WordTrace]
  refine ⟨7752080069000485299562283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5168053379333656866374855 7752080069000485299562283)
  ·
    refine ⟨11628120103500727949343425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7752080069000485299562283 11628120103500727949343425)
    ·
      refine ⟨8721090077625545962007569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11628120103500727949343425 8721090077625545962007569)
      ·
        refine ⟨6540817558219159471505677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8721090077625545962007569 6540817558219159471505677)
        ·
          refine ⟨2452806584332184801814629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6540817558219159471505677 2452806584332184801814629)
          ·
            refine ⟨459901234562284650340243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2452806584332184801814629 459901234562284650340243)
            ·
              refine ⟨689851851843426975510365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459901234562284650340243 689851851843426975510365)
              ·
                refine ⟨258694444441285115816387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 689851851843426975510365 258694444441285115816387)
                ·
                  refine ⟨388041666661927673724581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258694444441285115816387 388041666661927673724581)
                  ·
                    refine ⟨72757812499111438823359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 388041666661927673724581 72757812499111438823359)
                    ·
                      rfl

theorem cell22_212543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_212543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212543 prefixEnd_212543 := by exact prefixLift 212543
  have htrace : WordTrace (prefixWord ++ tailWord_212543) baseStart_212543 baseEnd_212543 := by
    simpa [prefixWord, tailWord_212543, baseEnd_212543] using wordTrace_append hprefix tailTrace_212543
  have hstable : (prefixWord ++ tailWord_212543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212543).length < 2 ^ (prefixWord ++ tailWord_212543).sum := by decide
  have hdescent : baseEnd_212543 < baseStart_212543 := by decide
  rcases family_descends (prefixWord ++ tailWord_212543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212708 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_212708 : Nat := 118140960795 + 212708 * 2 ^ 59
def prefixEnd_212708 : Nat := 4983230072969 + 3 ^ 40 * 212708 * 2
def baseEnd_212708 : Nat := 72814295371106008447853

theorem tailTrace_212708 : CollatzResearch.WordTrace tailWord_212708 prefixEnd_212708 72814295371106008447853 := by
  unfold tailWord_212708
  simp only [CollatzResearch.WordTrace]
  refine ⟨3879049056701359239659389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5172065408935145652879185 3879049056701359239659389)
  ·
    refine ⟨1454643396263009714872271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3879049056701359239659389 1454643396263009714872271)
    ·
      refine ⟨2181965094394514572308407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454643396263009714872271 2181965094394514572308407)
      ·
        refine ⟨3272947641591771858462611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2181965094394514572308407 3272947641591771858462611)
        ·
          refine ⟨4909421462387657787693917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3272947641591771858462611 4909421462387657787693917)
          ·
            refine ⟨1841033048395371670385219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4909421462387657787693917 1841033048395371670385219)
            ·
              refine ⟨2761549572593057505577829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841033048395371670385219 2761549572593057505577829)
              ·
                refine ⟨517790544861198282295843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2761549572593057505577829 517790544861198282295843)
                ·
                  refine ⟨776685817291797423443765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517790544861198282295843 776685817291797423443765)
                  ·
                    refine ⟨72814295371106008447853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 776685817291797423443765 72814295371106008447853)
                    ·
                      rfl

theorem cell22_212708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_212708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212708 prefixEnd_212708 := by exact prefixLift 212708
  have htrace : WordTrace (prefixWord ++ tailWord_212708) baseStart_212708 baseEnd_212708 := by
    simpa [prefixWord, tailWord_212708, baseEnd_212708] using wordTrace_append hprefix tailTrace_212708
  have hstable : (prefixWord ++ tailWord_212708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212708).length < 2 ^ (prefixWord ++ tailWord_212708).sum := by decide
  have hdescent : baseEnd_212708 < baseStart_212708 := by decide
  rcases family_descends (prefixWord ++ tailWord_212708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212712 : List Nat := [2, 1, 4, 1, 3, 1, 4, 1, 1, 4]
def baseStart_212712 : Nat := 118140960795 + 212712 * 2 ^ 59
def prefixEnd_212712 : Nat := 4983230072969 + 3 ^ 40 * 212712 * 2
def baseEnd_212712 : Nat := 72815664652851331347841

theorem tailTrace_212712 : CollatzResearch.WordTrace tailWord_212712 prefixEnd_212712 72815664652851331347841 := by
  unfold tailWord_212712
  simp only [CollatzResearch.WordTrace]
  refine ⟨3879122002694113581232195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5172162670258818108309593 3879122002694113581232195)
  ·
    refine ⟨5818683004041170371848293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3879122002694113581232195 5818683004041170371848293)
    ·
      refine ⟨1091003063257719444721555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5818683004041170371848293 1091003063257719444721555)
      ·
        refine ⟨1636504594886579167082333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1091003063257719444721555 1636504594886579167082333)
        ·
          refine ⟨613689223082467187655875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1636504594886579167082333 613689223082467187655875)
          ·
            refine ⟨920533834623700781483813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613689223082467187655875 920533834623700781483813)
            ·
              refine ⟨172600093991943896528215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 920533834623700781483813 172600093991943896528215)
              ·
                refine ⟨258900140987915844792323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172600093991943896528215 258900140987915844792323)
                ·
                  refine ⟨388350211481873767188485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258900140987915844792323 388350211481873767188485)
                  ·
                    refine ⟨72815664652851331347841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 388350211481873767188485 72815664652851331347841)
                    ·
                      rfl

theorem cell22_212712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_212712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212712 prefixEnd_212712 := by exact prefixLift 212712
  have htrace : WordTrace (prefixWord ++ tailWord_212712) baseStart_212712 baseEnd_212712 := by
    simpa [prefixWord, tailWord_212712, baseEnd_212712] using wordTrace_append hprefix tailTrace_212712
  have hstable : (prefixWord ++ tailWord_212712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212712).length < 2 ^ (prefixWord ++ tailWord_212712).sum := by decide
  have hdescent : baseEnd_212712 < baseStart_212712 := by decide
  rcases family_descends (prefixWord ++ tailWord_212712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212723 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 2, 4]
def baseStart_212723 : Nat := 118140960795 + 212723 * 2 ^ 59
def prefixEnd_212723 : Nat := 4983230072969 + 3 ^ 40 * 212723 * 2
def baseEnd_212723 : Nat := 72819430177650969322807

theorem tailTrace_212723 : CollatzResearch.WordTrace tailWord_212723 prefixEnd_212723 72819430177650969322807 := by
  unfold tailWord_212723
  simp only [CollatzResearch.WordTrace]
  refine ⟨7758645208348376041114823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5172430138898917360743215 7758645208348376041114823)
  ·
    refine ⟨11637967812522564061672235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7758645208348376041114823 11637967812522564061672235)
    ·
      refine ⟨17456951718783846092508353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11637967812522564061672235 17456951718783846092508353)
      ·
        refine ⟨13092713789087884569381265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17456951718783846092508353 13092713789087884569381265)
        ·
          refine ⟨9819535341815913427035949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13092713789087884569381265 9819535341815913427035949)
          ·
            refine ⟨3682325753180967535138481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9819535341815913427035949 3682325753180967535138481)
            ·
              refine ⟨2761744314885725651353861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3682325753180967535138481 2761744314885725651353861)
              ·
                refine ⟨517827059041073559628849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2761744314885725651353861 517827059041073559628849)
                ·
                  refine ⟨388370294280805169721637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517827059041073559628849 388370294280805169721637)
                  ·
                    refine ⟨72819430177650969322807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 388370294280805169721637 72819430177650969322807)
                    ·
                      rfl

theorem cell22_212723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 4].length) (baseStart_212723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212723 prefixEnd_212723 := by exact prefixLift 212723
  have htrace : WordTrace (prefixWord ++ tailWord_212723) baseStart_212723 baseEnd_212723 := by
    simpa [prefixWord, tailWord_212723, baseEnd_212723] using wordTrace_append hprefix tailTrace_212723
  have hstable : (prefixWord ++ tailWord_212723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212723).length < 2 ^ (prefixWord ++ tailWord_212723).sum := by decide
  have hdescent : baseEnd_212723 < baseStart_212723 := by decide
  rcases family_descends (prefixWord ++ tailWord_212723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212793 : List Nat := [1, 2, 1, 7, 2, 1, 2, 1, 2, 3]
def baseStart_212793 : Nat := 118140960795 + 212793 * 2 ^ 59
def prefixEnd_212793 : Nat := 4983230072969 + 3 ^ 40 * 212793 * 2
def baseEnd_212793 : Nat := 72843392608194120072593

theorem tailTrace_212793 : CollatzResearch.WordTrace tailWord_212793 prefixEnd_212793 72843392608194120072593 := by
  unfold tailWord_212793
  simp only [CollatzResearch.WordTrace]
  refine ⟨7761198318094777996163033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5174132212063185330775355 7761198318094777996163033)
  ·
    refine ⟨5820898738571083497122275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7761198318094777996163033 5820898738571083497122275)
    ·
      refine ⟨8731348107856625245683413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5820898738571083497122275 8731348107856625245683413)
      ·
        refine ⟨204640971277889654195705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 8731348107856625245683413 204640971277889654195705)
        ·
          refine ⟨153480728458417240646779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204640971277889654195705 153480728458417240646779)
          ·
            refine ⟨230221092687625860970169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153480728458417240646779 230221092687625860970169)
            ·
              refine ⟨172665819515719395727627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230221092687625860970169 172665819515719395727627)
              ·
                refine ⟨258998729273579093591441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172665819515719395727627 258998729273579093591441)
                ·
                  refine ⟨194249046955184320193581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258998729273579093591441 194249046955184320193581)
                  ·
                    refine ⟨72843392608194120072593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194249046955184320193581 72843392608194120072593)
                    ·
                      rfl

theorem cell22_212793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 2, 3].length) (baseStart_212793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212793 prefixEnd_212793 := by exact prefixLift 212793
  have htrace : WordTrace (prefixWord ++ tailWord_212793) baseStart_212793 baseEnd_212793 := by
    simpa [prefixWord, tailWord_212793, baseEnd_212793] using wordTrace_append hprefix tailTrace_212793
  have hstable : (prefixWord ++ tailWord_212793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212793).length < 2 ^ (prefixWord ++ tailWord_212793).sum := by decide
  have hdescent : baseEnd_212793 < baseStart_212793 := by decide
  rcases family_descends (prefixWord ++ tailWord_212793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212843 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 5, 5]
def baseStart_212843 : Nat := 118140960795 + 212843 * 2 ^ 59
def prefixEnd_212843 : Nat := 4983230072969 + 3 ^ 40 * 212843 * 2
def baseEnd_212843 : Nat := 72860508630010656322439

theorem tailTrace_212843 : CollatzResearch.WordTrace tailWord_212843 prefixEnd_212843 72860508630010656322439 := by
  unfold tailWord_212843
  simp only [CollatzResearch.WordTrace]
  refine ⟨7763021967913636535483183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5175347978609091023655455 7763021967913636535483183)
  ·
    refine ⟨11644532951870454803224775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7763021967913636535483183 11644532951870454803224775)
    ·
      refine ⟨17466799427805682204837163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11644532951870454803224775 17466799427805682204837163)
      ·
        refine ⟨26200199141708523307255745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17466799427805682204837163 26200199141708523307255745)
        ·
          refine ⟨19650149356281392480441809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26200199141708523307255745 19650149356281392480441809)
          ·
            refine ⟨14737612017211044360331357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19650149356281392480441809 14737612017211044360331357)
            ·
              refine ⟨5526604506454141635124259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14737612017211044360331357 5526604506454141635124259)
              ·
                refine ⟨8289906759681212452686389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5526604506454141635124259 8289906759681212452686389)
                ·
                  refine ⟨777178758720113667439349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8289906759681212452686389 777178758720113667439349)
                  ·
                    refine ⟨72860508630010656322439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 777178758720113667439349 72860508630010656322439)
                    ·
                      rfl

theorem cell22_212843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 5].length) (baseStart_212843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212843 prefixEnd_212843 := by exact prefixLift 212843
  have htrace : WordTrace (prefixWord ++ tailWord_212843) baseStart_212843 baseEnd_212843 := by
    simpa [prefixWord, tailWord_212843, baseEnd_212843] using wordTrace_append hprefix tailTrace_212843
  have hstable : (prefixWord ++ tailWord_212843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212843).length < 2 ^ (prefixWord ++ tailWord_212843).sum := by decide
  have hdescent : baseEnd_212843 < baseStart_212843 := by decide
  rcases family_descends (prefixWord ++ tailWord_212843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212860 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 8, 3]
def baseStart_212860 : Nat := 118140960795 + 212860 * 2 ^ 59
def prefixEnd_212860 : Nat := 4983230072969 + 3 ^ 40 * 212860 * 2
def baseEnd_212860 : Nat := 72866328077428278647387

theorem tailTrace_212860 : CollatzResearch.WordTrace tailWord_212860 prefixEnd_212860 72866328077428278647387 := by
  unfold tailWord_212860
  simp only [CollatzResearch.WordTrace]
  refine ⟨3881821004426024219426017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5175761339234698959234689 3881821004426024219426017)
  ·
    refine ⟨2911365753319518164569513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3881821004426024219426017 2911365753319518164569513)
    ·
      refine ⟨2183524314989638623427135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2911365753319518164569513 2183524314989638623427135)
      ·
        refine ⟨3275286472484457935140703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2183524314989638623427135 3275286472484457935140703)
        ·
          refine ⟨4912929708726686902711055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3275286472484457935140703 4912929708726686902711055)
          ·
            refine ⟨7369394563090030354066583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4912929708726686902711055 7369394563090030354066583)
            ·
              refine ⟨11054091844635045531099875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7369394563090030354066583 11054091844635045531099875)
              ·
                refine ⟨16581137766952568296649813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11054091844635045531099875 16581137766952568296649813)
                ·
                  refine ⟨194310208206475409726365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16581137766952568296649813 194310208206475409726365)
                  ·
                    refine ⟨72866328077428278647387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194310208206475409726365 72866328077428278647387)
                    ·
                      rfl

theorem cell22_212860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_212860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212860 prefixEnd_212860 := by exact prefixLift 212860
  have htrace : WordTrace (prefixWord ++ tailWord_212860) baseStart_212860 baseEnd_212860 := by
    simpa [prefixWord, tailWord_212860, baseEnd_212860] using wordTrace_append hprefix tailTrace_212860
  have hstable : (prefixWord ++ tailWord_212860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212860).length < 2 ^ (prefixWord ++ tailWord_212860).sum := by decide
  have hdescent : baseEnd_212860 < baseStart_212860 := by decide
  rcases family_descends (prefixWord ++ tailWord_212860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212862 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_212862 : Nat := 118140960795 + 212862 * 2 ^ 59
def prefixEnd_212862 : Nat := 4983230072969 + 3 ^ 40 * 212862 * 2
def baseEnd_212862 : Nat := 24289004239433646699127

theorem tailTrace_212862 : CollatzResearch.WordTrace tailWord_212862 prefixEnd_212862 24289004239433646699127 := by
  unfold tailWord_212862
  simp only [CollatzResearch.WordTrace]
  refine ⟨970464369355600347553105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5175809969896535186949893 970464369355600347553105)
  ·
    refine ⟨727848277016700260664829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 970464369355600347553105 727848277016700260664829)
    ·
      refine ⟨272943103881262597749311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 727848277016700260664829 272943103881262597749311)
      ·
        refine ⟨409414655821893896623967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272943103881262597749311 409414655821893896623967)
        ·
          refine ⟨614121983732840844935951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409414655821893896623967 614121983732840844935951)
          ·
            refine ⟨921182975599261267403927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614121983732840844935951 921182975599261267403927)
            ·
              refine ⟨1381774463398891901105891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921182975599261267403927 1381774463398891901105891)
              ·
                refine ⟨2072661695098337851658837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381774463398891901105891 2072661695098337851658837)
                ·
                  refine ⟨24289004239433646699127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2072661695098337851658837 24289004239433646699127)
                  ·
                    rfl

theorem cell22_212862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_212862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212862 prefixEnd_212862 := by exact prefixLift 212862
  have htrace : WordTrace (prefixWord ++ tailWord_212862) baseStart_212862 baseEnd_212862 := by
    simpa [prefixWord, tailWord_212862, baseEnd_212862] using wordTrace_append hprefix tailTrace_212862
  have hstable : (prefixWord ++ tailWord_212862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212862).length < 2 ^ (prefixWord ++ tailWord_212862).sum := by decide
  have hdescent : baseEnd_212862 < baseStart_212862 := by decide
  rcases family_descends (prefixWord ++ tailWord_212862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212890 : List Nat := [3, 1, 1, 4, 2, 2, 9]
def baseStart_212890 : Nat := 118140960795 + 212890 * 2 ^ 59
def prefixEnd_212890 : Nat := 4983230072969 + 3 ^ 40 * 212890 * 2
def baseEnd_212890 : Nat := 2699133247796970385085

theorem tailTrace_212890 : CollatzResearch.WordTrace tailWord_212890 prefixEnd_212890 2699133247796970385085 := by
  unfold tailWord_212890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941184049685840890611031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5176490799162242374962749 1941184049685840890611031)
  ·
    refine ⟨2911776074528761335916547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1941184049685840890611031 2911776074528761335916547)
    ·
      refine ⟨4367664111793142003874821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2911776074528761335916547 4367664111793142003874821)
      ·
        refine ⟨818937020961214125726529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4367664111793142003874821 818937020961214125726529)
        ·
          refine ⟨614202765720910594294897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818937020961214125726529 614202765720910594294897)
          ·
            refine ⟨460652074290682945721173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614202765720910594294897 460652074290682945721173)
            ·
              refine ⟨2699133247796970385085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 460652074290682945721173 2699133247796970385085)
              ·
                rfl

theorem cell22_212890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 9].length) (baseStart_212890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_212890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_212890 prefixEnd_212890 := by exact prefixLift 212890
  have htrace : WordTrace (prefixWord ++ tailWord_212890) baseStart_212890 baseEnd_212890 := by
    simpa [prefixWord, tailWord_212890, baseEnd_212890] using wordTrace_append hprefix tailTrace_212890
  have hstable : (prefixWord ++ tailWord_212890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212890).length < 2 ^ (prefixWord ++ tailWord_212890).sum := by decide
  have hdescent : baseEnd_212890 < baseStart_212890 := by decide
  rcases family_descends (prefixWord ++ tailWord_212890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213029 : List Nat := [1, 3, 1, 2, 2, 3, 2, 3, 2, 3]
def baseStart_213029 : Nat := 118140960795 + 213029 * 2 ^ 59
def prefixEnd_213029 : Nat := 4983230072969 + 3 ^ 40 * 213029 * 2
def baseEnd_213029 : Nat := 72924180231168171171869

theorem tailTrace_213029 : CollatzResearch.WordTrace tailWord_213029 prefixEnd_213029 72924180231168171171869 := by
  unfold tailWord_213029
  simp only [CollatzResearch.WordTrace]
  refine ⟨7769805945239790301754141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5179870630159860201169427 7769805945239790301754141)
  ·
    refine ⟨2913677229464921363157803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7769805945239790301754141 2913677229464921363157803)
    ·
      refine ⟨4370515844197382044736705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2913677229464921363157803 4370515844197382044736705)
      ·
        refine ⟨3277886883148036533552529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4370515844197382044736705 3277886883148036533552529)
        ·
          refine ⟨2458415162361027400164397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3277886883148036533552529 2458415162361027400164397)
          ·
            refine ⟨921905685885385275061649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2458415162361027400164397 921905685885385275061649)
            ·
              refine ⟨691429264414038956296237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921905685885385275061649 691429264414038956296237)
              ·
                refine ⟨259285974155264608611089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 691429264414038956296237 259285974155264608611089)
                ·
                  refine ⟨194464480616448456458317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259285974155264608611089 194464480616448456458317)
                  ·
                    refine ⟨72924180231168171171869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194464480616448456458317 72924180231168171171869)
                    ·
                      rfl

theorem cell22_213029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_213029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213029 prefixEnd_213029 := by exact prefixLift 213029
  have htrace : WordTrace (prefixWord ++ tailWord_213029) baseStart_213029 baseEnd_213029 := by
    simpa [prefixWord, tailWord_213029, baseEnd_213029] using wordTrace_append hprefix tailTrace_213029
  have hstable : (prefixWord ++ tailWord_213029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213029).length < 2 ^ (prefixWord ++ tailWord_213029).sum := by decide
  have hdescent : baseEnd_213029 < baseStart_213029 := by decide
  rcases family_descends (prefixWord ++ tailWord_213029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213151 : List Nat := [1, 1, 2, 6, 1, 1, 3, 2, 1, 4]
def baseStart_213151 : Nat := 118140960795 + 213151 * 2 ^ 59
def prefixEnd_213151 : Nat := 4983230072969 + 3 ^ 40 * 213151 * 2
def baseEnd_213151 : Nat := 72965943324400519621495

theorem tailTrace_213151 : CollatzResearch.WordTrace tailWord_213151 prefixEnd_213151 72965943324400519621495 := by
  unfold tailWord_213151
  simp only [CollatzResearch.WordTrace]
  refine ⟨7774255650797805137695307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5182837100531870091796871 7774255650797805137695307)
  ·
    refine ⟨11661383476196707706542961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7774255650797805137695307 11661383476196707706542961)
    ·
      refine ⟨8746037607147530779907221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11661383476196707706542961 8746037607147530779907221)
      ·
        refine ⟨409970512835040505308151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8746037607147530779907221 409970512835040505308151)
        ·
          refine ⟨614955769252560757962227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409970512835040505308151 614955769252560757962227)
          ·
            refine ⟨922433653878841136943341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614955769252560757962227 922433653878841136943341)
            ·
              refine ⟨345912620204565426353753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 922433653878841136943341 345912620204565426353753)
              ·
                refine ⟨259434465153424069765315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345912620204565426353753 259434465153424069765315)
                ·
                  refine ⟨389151697730136104647973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259434465153424069765315 389151697730136104647973)
                  ·
                    refine ⟨72965943324400519621495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 389151697730136104647973 72965943324400519621495)
                    ·
                      rfl

theorem cell22_213151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_213151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213151 prefixEnd_213151 := by exact prefixLift 213151
  have htrace : WordTrace (prefixWord ++ tailWord_213151) baseStart_213151 baseEnd_213151 := by
    simpa [prefixWord, tailWord_213151, baseEnd_213151] using wordTrace_append hprefix tailTrace_213151
  have hstable : (prefixWord ++ tailWord_213151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213151).length < 2 ^ (prefixWord ++ tailWord_213151).sum := by decide
  have hdescent : baseEnd_213151 < baseStart_213151 := by decide
  rcases family_descends (prefixWord ++ tailWord_213151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213192 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 2, 7]
def baseStart_213192 : Nat := 118140960795 + 213192 * 2 ^ 59
def prefixEnd_213192 : Nat := 4983230072969 + 3 ^ 40 * 213192 * 2
def baseEnd_213192 : Nat := 72979978462290079346369

theorem tailTrace_213192 : CollatzResearch.WordTrace tailWord_213192 prefixEnd_213192 72979978462290079346369 := by
  unfold tailWord_213192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3887875521824634569968915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5183834029099512759958553 3887875521824634569968915)
  ·
    refine ⟨5831813282736951854953373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3887875521824634569968915 5831813282736951854953373)
    ·
      refine ⟨2186929981026356945607515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5831813282736951854953373 2186929981026356945607515)
      ·
        refine ⟨3280394971539535418411273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2186929981026356945607515 3280394971539535418411273)
        ·
          refine ⟨2460296228654651563808455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3280394971539535418411273 2460296228654651563808455)
          ·
            refine ⟨3690444342981977345712683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460296228654651563808455 3690444342981977345712683)
            ·
              refine ⟨5535666514472966018569025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690444342981977345712683 5535666514472966018569025)
              ·
                refine ⟨4151749885854724513926769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5535666514472966018569025 4151749885854724513926769)
                ·
                  refine ⟨3113812414391043385445077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4151749885854724513926769 3113812414391043385445077)
                  ·
                    refine ⟨72979978462290079346369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3113812414391043385445077 72979978462290079346369)
                    ·
                      rfl

theorem cell22_213192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_213192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213192 prefixEnd_213192 := by exact prefixLift 213192
  have htrace : WordTrace (prefixWord ++ tailWord_213192) baseStart_213192 baseEnd_213192 := by
    simpa [prefixWord, tailWord_213192, baseEnd_213192] using wordTrace_append hprefix tailTrace_213192
  have hstable : (prefixWord ++ tailWord_213192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213192).length < 2 ^ (prefixWord ++ tailWord_213192).sum := by decide
  have hdescent : baseEnd_213192 < baseStart_213192 := by decide
  rcases family_descends (prefixWord ++ tailWord_213192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213207 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 4, 6]
def baseStart_213207 : Nat := 118140960795 + 213207 * 2 ^ 59
def prefixEnd_213207 : Nat := 4983230072969 + 3 ^ 40 * 213207 * 2
def baseEnd_213207 : Nat := 72985113268835040221323

theorem tailTrace_213207 : CollatzResearch.WordTrace tailWord_213207 prefixEnd_213207 72985113268835040221323 := by
  unfold tailWord_213207
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776298138594926701733875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5184198759063284467822583 7776298138594926701733875)
  ·
    refine ⟨11664447207892390052600813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7776298138594926701733875 11664447207892390052600813)
    ·
      refine ⟨4374167702959646269725305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11664447207892390052600813 4374167702959646269725305)
      ·
        refine ⟨3280625777219734702293979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4374167702959646269725305 3280625777219734702293979)
        ·
          refine ⟨4920938665829602053440969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280625777219734702293979 4920938665829602053440969)
          ·
            refine ⟨3690703999372201540080727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4920938665829602053440969 3690703999372201540080727)
            ·
              refine ⟨5536055999058302310121091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690703999372201540080727 5536055999058302310121091)
              ·
                refine ⟨8304083998587453465181637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5536055999058302310121091 8304083998587453465181637)
                ·
                  refine ⟨1557015749735147524721557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8304083998587453465181637 1557015749735147524721557)
                  ·
                    refine ⟨72985113268835040221323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1557015749735147524721557 72985113268835040221323)
                    ·
                      rfl

theorem cell22_213207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_213207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213207 prefixEnd_213207 := by exact prefixLift 213207
  have htrace : WordTrace (prefixWord ++ tailWord_213207) baseStart_213207 baseEnd_213207 := by
    simpa [prefixWord, tailWord_213207, baseEnd_213207] using wordTrace_append hprefix tailTrace_213207
  have hstable : (prefixWord ++ tailWord_213207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213207).length < 2 ^ (prefixWord ++ tailWord_213207).sum := by decide
  have hdescent : baseEnd_213207 < baseStart_213207 := by decide
  rcases family_descends (prefixWord ++ tailWord_213207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213209 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 5, 3]
def baseStart_213209 : Nat := 118140960795 + 213209 * 2 ^ 59
def prefixEnd_213209 : Nat := 4983230072969 + 3 ^ 40 * 213209 * 2
def baseEnd_213209 : Nat := 72985797909707701671317

theorem tailTrace_213209 : CollatzResearch.WordTrace tailWord_213209 prefixEnd_213209 72985797909707701671317 := by
  unfold tailWord_213209
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776371084587681043306681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5184247389725120695537787 7776371084587681043306681)
  ·
    refine ⟨5832278313440760782480011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7776371084587681043306681 5832278313440760782480011)
    ·
      refine ⟨8748417470161141173720017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5832278313440760782480011 8748417470161141173720017)
      ·
        refine ⟨6561313102620855880290013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8748417470161141173720017 6561313102620855880290013)
        ·
          refine ⟨2460492413482820955108755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6561313102620855880290013 2460492413482820955108755)
          ·
            refine ⟨3690738620224231432663133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460492413482820955108755 3690738620224231432663133)
            ·
              refine ⟨1384026982584086787248675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3690738620224231432663133 1384026982584086787248675)
              ·
                refine ⟨2076040473876130180873013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384026982584086787248675 2076040473876130180873013)
                ·
                  refine ⟨194628794425887204456845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2076040473876130180873013 194628794425887204456845)
                  ·
                    refine ⟨72985797909707701671317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194628794425887204456845 72985797909707701671317)
                    ·
                      rfl

theorem cell22_213209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 3].length) (baseStart_213209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213209 prefixEnd_213209 := by exact prefixLift 213209
  have htrace : WordTrace (prefixWord ++ tailWord_213209) baseStart_213209 baseEnd_213209 := by
    simpa [prefixWord, tailWord_213209, baseEnd_213209] using wordTrace_append hprefix tailTrace_213209
  have hstable : (prefixWord ++ tailWord_213209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213209).length < 2 ^ (prefixWord ++ tailWord_213209).sum := by decide
  have hdescent : baseEnd_213209 < baseStart_213209 := by decide
  rcases family_descends (prefixWord ++ tailWord_213209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213213 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_213213 : Nat := 118140960795 + 213213 * 2 ^ 59
def prefixEnd_213213 : Nat := 4983230072969 + 3 ^ 40 * 213213 * 2
def baseEnd_213213 : Nat := 72987167191453024571305

theorem tailTrace_213213 : CollatzResearch.WordTrace tailWord_213213 prefixEnd_213213 72987167191453024571305 := by
  unfold tailWord_213213
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776516976573189726452293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5184344651048793150968195 7776516976573189726452293)
  ·
    refine ⟨1458096933107473073709805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7776516976573189726452293 1458096933107473073709805)
    ·
      refine ⟨546786349915302402641177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1458096933107473073709805 546786349915302402641177)
      ·
        refine ⟨410089762436476801980883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546786349915302402641177 410089762436476801980883)
        ·
          refine ⟨615134643654715202971325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410089762436476801980883 615134643654715202971325)
          ·
            refine ⟨230675491370518201114247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 615134643654715202971325 230675491370518201114247)
            ·
              refine ⟨346013237055777301671371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230675491370518201114247 346013237055777301671371)
              ·
                refine ⟨519019855583665952507057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346013237055777301671371 519019855583665952507057)
                ·
                  refine ⟨389264891687749464380293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519019855583665952507057 389264891687749464380293)
                  ·
                    refine ⟨72987167191453024571305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 389264891687749464380293 72987167191453024571305)
                    ·
                      rfl

theorem cell22_213213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_213213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213213 prefixEnd_213213 := by exact prefixLift 213213
  have htrace : WordTrace (prefixWord ++ tailWord_213213) baseStart_213213 baseEnd_213213 := by
    simpa [prefixWord, tailWord_213213, baseEnd_213213] using wordTrace_append hprefix tailTrace_213213
  have hstable : (prefixWord ++ tailWord_213213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213213).length < 2 ^ (prefixWord ++ tailWord_213213).sum := by decide
  have hdescent : baseEnd_213213 < baseStart_213213 := by decide
  rcases family_descends (prefixWord ++ tailWord_213213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213269 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_213269 : Nat := 118140960795 + 213269 * 2 ^ 59
def prefixEnd_213269 : Nat := 4983230072969 + 3 ^ 40 * 213269 * 2
def baseEnd_213269 : Nat := 73006337135887545171133

theorem tailTrace_213269 : CollatzResearch.WordTrace tailWord_213269 prefixEnd_213269 73006337135887545171133 := by
  unfold tailWord_213269
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778559464370311290490861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5185706309580207526993907 7778559464370311290490861)
  ·
    refine ⟨2916959799138866733934073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7778559464370311290490861 2916959799138866733934073)
    ·
      refine ⟨2187719849354150050450555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2916959799138866733934073 2187719849354150050450555)
      ·
        refine ⟨3281579774031225075675833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187719849354150050450555 3281579774031225075675833)
        ·
          refine ⟨2461184830523418806756875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3281579774031225075675833 2461184830523418806756875)
          ·
            refine ⟨3691777245785128210135313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461184830523418806756875 3691777245785128210135313)
            ·
              refine ⟨2768832934338846157601485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3691777245785128210135313 2768832934338846157601485)
              ·
                refine ⟨1038312350377067309100557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2768832934338846157601485 1038312350377067309100557)
                ·
                  refine ⟨389367131391400240912709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1038312350377067309100557 389367131391400240912709)
                  ·
                    refine ⟨73006337135887545171133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 389367131391400240912709 73006337135887545171133)
                    ·
                      rfl

theorem cell22_213269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_213269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213269 prefixEnd_213269 := by exact prefixLift 213269
  have htrace : WordTrace (prefixWord ++ tailWord_213269) baseStart_213269 baseEnd_213269 := by
    simpa [prefixWord, tailWord_213269, baseEnd_213269] using wordTrace_append hprefix tailTrace_213269
  have hstable : (prefixWord ++ tailWord_213269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213269).length < 2 ^ (prefixWord ++ tailWord_213269).sum := by decide
  have hdescent : baseEnd_213269 < baseStart_213269 := by decide
  rcases family_descends (prefixWord ++ tailWord_213269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213277 : List Nat := [1, 4, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_213277 : Nat := 118140960795 + 213277 * 2 ^ 59
def prefixEnd_213277 : Nat := 4983230072969 + 3 ^ 40 * 213277 * 2
def baseEnd_213277 : Nat := 73009075699378190971109

theorem tailTrace_213277 : CollatzResearch.WordTrace tailWord_213277 prefixEnd_213277 73009075699378190971109 := by
  unfold tailWord_213277
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778851248341328656782085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5185900832227552437854723 7778851248341328656782085)
  ·
    refine ⟨1458534609063999123146641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7778851248341328656782085 1458534609063999123146641)
    ·
      refine ⟨1093900956797999342359981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1458534609063999123146641 1093900956797999342359981)
      ·
        refine ⟨410212858799249753384993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1093900956797999342359981 410212858799249753384993)
        ·
          refine ⟨307659644099437315038745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410212858799249753384993 307659644099437315038745)
          ·
            refine ⟨230744733074577986279059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307659644099437315038745 230744733074577986279059)
            ·
              refine ⟨346117099611866979418589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230744733074577986279059 346117099611866979418589)
              ·
                refine ⟨129793912354450117281971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346117099611866979418589 129793912354450117281971)
                ·
                  refine ⟨194690868531675175922957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129793912354450117281971 194690868531675175922957)
                  ·
                    refine ⟨73009075699378190971109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194690868531675175922957 73009075699378190971109)
                    ·
                      rfl

theorem cell22_213277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_213277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213277 prefixEnd_213277 := by exact prefixLift 213277
  have htrace : WordTrace (prefixWord ++ tailWord_213277) baseStart_213277 baseEnd_213277 := by
    simpa [prefixWord, tailWord_213277, baseEnd_213277] using wordTrace_append hprefix tailTrace_213277
  have hstable : (prefixWord ++ tailWord_213277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213277).length < 2 ^ (prefixWord ++ tailWord_213277).sum := by decide
  have hdescent : baseEnd_213277 < baseStart_213277 := by decide
  rcases family_descends (prefixWord ++ tailWord_213277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213294 : List Nat := [4, 1, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_213294 : Nat := 118140960795 + 213294 * 2 ^ 59
def prefixEnd_213294 : Nat := 4983230072969 + 3 ^ 40 * 213294 * 2
def baseEnd_213294 : Nat := 73014895146795813296057

theorem tailTrace_213294 : CollatzResearch.WordTrace tailWord_213294 prefixEnd_213294 73014895146795813296057 := by
  unfold tailWord_213294
  simp only [CollatzResearch.WordTrace]
  refine ⟨972433911159967570018867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5186314192853160373433957 972433911159967570018867)
  ·
    refine ⟨1458650866739951355028301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 972433911159967570018867 1458650866739951355028301)
    ·
      refine ⟨546994075027481758135613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1458650866739951355028301 546994075027481758135613)
      ·
        refine ⟨205122778135305659300855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 546994075027481758135613 205122778135305659300855)
        ·
          refine ⟨307684167202958488951283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205122778135305659300855 307684167202958488951283)
          ·
            refine ⟨461526250804437733426925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307684167202958488951283 461526250804437733426925)
            ·
              refine ⟨173072344051664150035097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461526250804437733426925 173072344051664150035097)
              ·
                refine ⟨129804258038748112526323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173072344051664150035097 129804258038748112526323)
                ·
                  refine ⟨194706387058122168789485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129804258038748112526323 194706387058122168789485)
                  ·
                    refine ⟨73014895146795813296057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194706387058122168789485 73014895146795813296057)
                    ·
                      rfl

theorem cell22_213294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_213294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213294 prefixEnd_213294 := by exact prefixLift 213294
  have htrace : WordTrace (prefixWord ++ tailWord_213294) baseStart_213294 baseEnd_213294 := by
    simpa [prefixWord, tailWord_213294, baseEnd_213294] using wordTrace_append hprefix tailTrace_213294
  have hstable : (prefixWord ++ tailWord_213294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213294).length < 2 ^ (prefixWord ++ tailWord_213294).sum := by decide
  have hdescent : baseEnd_213294 < baseStart_213294 := by decide
  rcases family_descends (prefixWord ++ tailWord_213294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213329 : List Nat := [1, 2, 2, 1, 4, 2, 2, 8]
def baseStart_213329 : Nat := 118140960795 + 213329 * 2 ^ 59
def prefixEnd_213329 : Nat := 4983230072969 + 3 ^ 40 * 213329 * 2
def baseEnd_213329 : Nat := 8114097373563043185661

theorem tailTrace_213329 : CollatzResearch.WordTrace tailWord_213329 prefixEnd_213329 8114097373563043185661 := by
  unfold tailWord_213329
  simp only [CollatzResearch.WordTrace]
  refine ⟨7780747844152941537675041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5187165229435294358450027 7780747844152941537675041)
  ·
    refine ⟨5835560883114706153256281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7780747844152941537675041 5835560883114706153256281)
    ·
      refine ⟨4376670662336029614942211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5835560883114706153256281 4376670662336029614942211)
      ·
        refine ⟨6565005993504044422413317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4376670662336029614942211 6565005993504044422413317)
        ·
          refine ⟨1230938623782008329202497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6565005993504044422413317 1230938623782008329202497)
          ·
            refine ⟨923203967836506246901873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1230938623782008329202497 923203967836506246901873)
            ·
              refine ⟨692402975877379685176405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923203967836506246901873 692402975877379685176405)
              ·
                refine ⟨8114097373563043185661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 692402975877379685176405 8114097373563043185661)
                ·
                  rfl

theorem cell22_213329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 8].length) (baseStart_213329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213329 prefixEnd_213329 := by exact prefixLift 213329
  have htrace : WordTrace (prefixWord ++ tailWord_213329) baseStart_213329 baseEnd_213329 := by
    simpa [prefixWord, tailWord_213329, baseEnd_213329] using wordTrace_append hprefix tailTrace_213329
  have hstable : (prefixWord ++ tailWord_213329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213329).length < 2 ^ (prefixWord ++ tailWord_213329).sum := by decide
  have hdescent : baseEnd_213329 < baseStart_213329 := by decide
  rcases family_descends (prefixWord ++ tailWord_213329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213361 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 3, 3]
def baseStart_213361 : Nat := 118140960795 + 213361 * 2 ^ 59
def prefixEnd_213361 : Nat := 4983230072969 + 3 ^ 40 * 213361 * 2
def baseEnd_213361 : Nat := 73037830616029971870851

theorem tailTrace_213361 : CollatzResearch.WordTrace tailWord_213361 prefixEnd_213361 73037830616029971870851 := by
  unfold tailWord_213361
  simp only [CollatzResearch.WordTrace]
  refine ⟨7781914980037011002839937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5187943320024674001893291 7781914980037011002839937)
  ·
    refine ⟨5836436235027758252129953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7781914980037011002839937 5836436235027758252129953)
    ·
      refine ⟨4377327176270818689097465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5836436235027758252129953 4377327176270818689097465)
      ·
        refine ⟨3282995382203114016823099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4377327176270818689097465 3282995382203114016823099)
        ·
          refine ⟨4924493073304671025234649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3282995382203114016823099 4924493073304671025234649)
          ·
            refine ⟨3693369804978503268925987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4924493073304671025234649 3693369804978503268925987)
            ·
              refine ⟨5540054707467754903388981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3693369804978503268925987 5540054707467754903388981)
              ·
                refine ⟨519380128825102022192717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5540054707467754903388981 519380128825102022192717)
                ·
                  refine ⟨194767548309413258322269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519380128825102022192717 194767548309413258322269)
                  ·
                    refine ⟨73037830616029971870851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194767548309413258322269 73037830616029971870851)
                    ·
                      rfl

theorem cell22_213361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_213361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213361 prefixEnd_213361 := by exact prefixLift 213361
  have htrace : WordTrace (prefixWord ++ tailWord_213361) baseStart_213361 baseEnd_213361 := by
    simpa [prefixWord, tailWord_213361, baseEnd_213361] using wordTrace_append hprefix tailTrace_213361
  have hstable : (prefixWord ++ tailWord_213361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213361).length < 2 ^ (prefixWord ++ tailWord_213361).sum := by decide
  have hdescent : baseEnd_213361 < baseStart_213361 := by decide
  rcases family_descends (prefixWord ++ tailWord_213361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213408 : List Nat := [2, 1, 1, 4, 1, 5, 1, 2, 5]
def baseStart_213408 : Nat := 118140960795 + 213408 * 2 ^ 59
def prefixEnd_213408 : Nat := 4983230072969 + 3 ^ 40 * 213408 * 2
def baseEnd_213408 : Nat := 24351306558845838648569

theorem tailTrace_213408 : CollatzResearch.WordTrace tailWord_213408 prefixEnd_213408 24351306558845838648569 := by
  unfold tailWord_213408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3891814605433369014900439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5189086140577825353200585 3891814605433369014900439)
  ·
    refine ⟨5837721908150053522350659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3891814605433369014900439 5837721908150053522350659)
    ·
      refine ⟨8756582862225080283525989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5837721908150053522350659 8756582862225080283525989)
      ·
        refine ⟨1641859286667202553161123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8756582862225080283525989 1641859286667202553161123)
        ·
          refine ⟨2462788930000803829741685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641859286667202553161123 2462788930000803829741685)
          ·
            refine ⟨230886462187575359038283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2462788930000803829741685 230886462187575359038283)
            ·
              refine ⟨346329693281363038557425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230886462187575359038283 346329693281363038557425)
              ·
                refine ⟨259747269961022278918069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346329693281363038557425 259747269961022278918069)
                ·
                  refine ⟨24351306558845838648569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 259747269961022278918069 24351306558845838648569)
                  ·
                    rfl

theorem cell22_213408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 5].length) (baseStart_213408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213408 prefixEnd_213408 := by exact prefixLift 213408
  have htrace : WordTrace (prefixWord ++ tailWord_213408) baseStart_213408 baseEnd_213408 := by
    simpa [prefixWord, tailWord_213408, baseEnd_213408] using wordTrace_append hprefix tailTrace_213408
  have hstable : (prefixWord ++ tailWord_213408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213408).length < 2 ^ (prefixWord ++ tailWord_213408).sum := by decide
  have hdescent : baseEnd_213408 < baseStart_213408 := by decide
  rcases family_descends (prefixWord ++ tailWord_213408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
