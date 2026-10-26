import V185TrunkScan23Chunk0783

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4637037 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_4637037 : Nat := 118140960795 + 4637037 * 2 ^ 59
def prefixEnd_4637037 : Nat := 4983230072969 + 3 ^ 40 * 4637037 * 2
def baseEnd_4637037 : Nat := 2381028793682679305112161

theorem tailTrace_4637037 : CollatzResearch.WordTrace tailWord_4637037 prefixEnd_4637037 2381028793682679305112161 := by
  unfold tailWord_4637037
  simp only [CollatzResearch.WordTrace]
  refine ⟨169126633701814366714917365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112751089134542911143278243 169126633701814366714917365)
  ·
    refine ⟨15855621909545096879523503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 169126633701814366714917365 15855621909545096879523503)
    ·
      refine ⟨23783432864317645319285255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15855621909545096879523503 23783432864317645319285255)
      ·
        refine ⟨35675149296476467978927883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23783432864317645319285255 35675149296476467978927883)
        ·
          refine ⟨53512723944714701968391825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35675149296476467978927883 53512723944714701968391825)
          ·
            refine ⟨40134542958536026476293869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53512723944714701968391825 40134542958536026476293869)
            ·
              refine ⟨15050453609451009928610201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40134542958536026476293869 15050453609451009928610201)
              ·
                refine ⟨11287840207088257446457651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15050453609451009928610201 11287840207088257446457651)
                ·
                  refine ⟨16931760310632386169686477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11287840207088257446457651 16931760310632386169686477)
                  ·
                    refine ⟨6349410116487144813632429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16931760310632386169686477 6349410116487144813632429)
                    ·
                      refine ⟨2381028793682679305112161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6349410116487144813632429 2381028793682679305112161)
                      ·
                        rfl

theorem cell23_4637037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_4637037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637037 prefixEnd_4637037 := by exact prefixLift 4637037
  have htrace : WordTrace (prefixWord ++ tailWord_4637037) baseStart_4637037 baseEnd_4637037 := by
    simpa [prefixWord, tailWord_4637037, baseEnd_4637037] using wordTrace_append hprefix tailTrace_4637037
  have hstable : (prefixWord ++ tailWord_4637037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637037).length < 2 ^ (prefixWord ++ tailWord_4637037).sum := by decide
  have hdescent : baseEnd_4637037 < baseStart_4637037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637043 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 8]
def baseStart_4637043 : Nat := 118140960795 + 4637043 * 2 ^ 59
def prefixEnd_4637043 : Nat := 4983230072969 + 3 ^ 40 * 4637043 * 2
def baseEnd_4637043 : Nat := 2381031874566606281637133

theorem tailTrace_4637043 : CollatzResearch.WordTrace tailWord_4637043 prefixEnd_4637043 2381031874566606281637133 := by
  unfold tailWord_4637043
  simp only [CollatzResearch.WordTrace]
  refine ⟨169126852539792629739635783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112751235026528419826423855 169126852539792629739635783)
  ·
    refine ⟨253690278809688944609453675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169126852539792629739635783 253690278809688944609453675)
    ·
      refine ⟨380535418214533416914180513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253690278809688944609453675 380535418214533416914180513)
      ·
        refine ⟨285401563660900062685635385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380535418214533416914180513 285401563660900062685635385)
        ·
          refine ⟨214051172745675047014226539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285401563660900062685635385 214051172745675047014226539)
          ·
            refine ⟨321076759118512570521339809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214051172745675047014226539 321076759118512570521339809)
            ·
              refine ⟨240807569338884427891004857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321076759118512570521339809 240807569338884427891004857)
              ·
                refine ⟨180605677004163320918253643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240807569338884427891004857 180605677004163320918253643)
                ·
                  refine ⟨270908515506244981377380465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180605677004163320918253643 270908515506244981377380465)
                  ·
                    refine ⟨203181386629683736033035349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 270908515506244981377380465 203181386629683736033035349)
                    ·
                      refine ⟨2381031874566606281637133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 203181386629683736033035349 2381031874566606281637133)
                      ·
                        rfl

theorem cell23_4637043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_4637043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637043 prefixEnd_4637043 := by exact prefixLift 4637043
  have htrace : WordTrace (prefixWord ++ tailWord_4637043) baseStart_4637043 baseEnd_4637043 := by
    simpa [prefixWord, tailWord_4637043, baseEnd_4637043] using wordTrace_append hprefix tailTrace_4637043
  have hstable : (prefixWord ++ tailWord_4637043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637043).length < 2 ^ (prefixWord ++ tailWord_4637043).sum := by decide
  have hdescent : baseEnd_4637043 < baseStart_4637043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637060 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_4637060 : Nat := 118140960795 + 4637060 * 2 ^ 59
def prefixEnd_4637060 : Nat := 4983230072969 + 3 ^ 40 * 4637060 * 2
def baseEnd_4637060 : Nat := 2381040603737732715124555

theorem tailTrace_4637060 : CollatzResearch.WordTrace tailWord_4637060 prefixEnd_4637060 2381040603737732715124555 := by
  unfold tailWord_4637060
  simp only [CollatzResearch.WordTrace]
  refine ⟨84563736290365520821502317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112751648387154027762003089 84563736290365520821502317)
  ·
    refine ⟨31711401108887070308063369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84563736290365520821502317 31711401108887070308063369)
    ·
      refine ⟨23783550831665302731047527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31711401108887070308063369 23783550831665302731047527)
      ·
        refine ⟨35675326247497954096571291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23783550831665302731047527 35675326247497954096571291)
        ·
          refine ⟨53512989371246931144856937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35675326247497954096571291 53512989371246931144856937)
          ·
            refine ⟨40134742028435198358642703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53512989371246931144856937 40134742028435198358642703)
            ·
              refine ⟨60202113042652797537964055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40134742028435198358642703 60202113042652797537964055)
              ·
                refine ⟨90303169563979196306946083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60202113042652797537964055 90303169563979196306946083)
                ·
                  refine ⟨135454754345968794460419125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90303169563979196306946083 135454754345968794460419125)
                  ·
                    refine ⟨12698883219934574480664293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 135454754345968794460419125 12698883219934574480664293)
                    ·
                      refine ⟨2381040603737732715124555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12698883219934574480664293 2381040603737732715124555)
                      ·
                        rfl

theorem cell23_4637060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_4637060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637060 prefixEnd_4637060 := by exact prefixLift 4637060
  have htrace : WordTrace (prefixWord ++ tailWord_4637060) baseStart_4637060 baseEnd_4637060 := by
    simpa [prefixWord, tailWord_4637060, baseEnd_4637060] using wordTrace_append hprefix tailTrace_4637060
  have hstable : (prefixWord ++ tailWord_4637060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637060).length < 2 ^ (prefixWord ++ tailWord_4637060).sum := by decide
  have hdescent : baseEnd_4637060 < baseStart_4637060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637078 : List Nat := [5, 3, 1, 2, 1, 1, 3, 7]
def baseStart_4637078 : Nat := 118140960795 + 4637078 * 2 ^ 59
def prefixEnd_4637078 : Nat := 4983230072969 + 3 ^ 40 * 4637078 * 2
def baseEnd_4637078 : Nat := 88187031347759764618499

theorem tailTrace_4637078 : CollatzResearch.WordTrace tailWord_4637078 prefixEnd_4637078 88187031347759764618499 := by
  unfold tailWord_4637078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10570508068416614419822493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112752086063110553811439925 10570508068416614419822493)
  ·
    refine ⟨3963940525656230407433435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10570508068416614419822493 3963940525656230407433435)
    ·
      refine ⟨5945910788484345611150153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3963940525656230407433435 5945910788484345611150153)
      ·
        refine ⟨4459433091363259208362615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5945910788484345611150153 4459433091363259208362615)
        ·
          refine ⟨6689149637044888812543923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4459433091363259208362615 6689149637044888812543923)
          ·
            refine ⟨10033724455567333218815885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6689149637044888812543923 10033724455567333218815885)
            ·
              refine ⟨3762646670837749957055957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10033724455567333218815885 3762646670837749957055957)
              ·
                refine ⟨88187031347759764618499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3762646670837749957055957 88187031347759764618499)
                ·
                  rfl

theorem cell23_4637078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_4637078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637078 prefixEnd_4637078 := by exact prefixLift 4637078
  have htrace : WordTrace (prefixWord ++ tailWord_4637078) baseStart_4637078 baseEnd_4637078 := by
    simpa [prefixWord, tailWord_4637078, baseEnd_4637078] using wordTrace_append hprefix tailTrace_4637078
  have hstable : (prefixWord ++ tailWord_4637078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637078).length < 2 ^ (prefixWord ++ tailWord_4637078).sum := by decide
  have hdescent : baseEnd_4637078 < baseStart_4637078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637111 : List Nat := [1, 1, 3, 1, 3, 3, 3, 2, 2, 2, 2]
def baseStart_4637111 : Nat := 118140960795 + 4637111 * 2 ^ 59
def prefixEnd_4637111 : Nat := 4983230072969 + 3 ^ 40 * 4637111 * 2
def baseEnd_4637111 : Nat := 2381066791251112015586821

theorem tailTrace_4637111 : CollatzResearch.WordTrace tailWord_4637111 prefixEnd_4637111 2381066791251112015586821 := by
  unfold tailWord_4637111
  simp only [CollatzResearch.WordTrace]
  refine ⟨169129332703546277353111187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112752888469030851568740791 169129332703546277353111187)
  ·
    refine ⟨253693999055319416029666781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169129332703546277353111187 253693999055319416029666781)
    ·
      refine ⟨95135249645744781011125043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253693999055319416029666781 95135249645744781011125043)
      ·
        refine ⟨142702874468617171516687565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95135249645744781011125043 142702874468617171516687565)
        ·
          refine ⟨53513577925731439318757837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142702874468617171516687565 53513577925731439318757837)
          ·
            refine ⟨20067591722149289744534189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53513577925731439318757837 20067591722149289744534189)
            ·
              refine ⟨7525346895805983654200321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20067591722149289744534189 7525346895805983654200321)
              ·
                refine ⟨5644010171854487740650241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7525346895805983654200321 5644010171854487740650241)
                ·
                  refine ⟨4233007628890865805487681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5644010171854487740650241 4233007628890865805487681)
                  ·
                    refine ⟨3174755721668149354115761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4233007628890865805487681 3174755721668149354115761)
                    ·
                      refine ⟨2381066791251112015586821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3174755721668149354115761 2381066791251112015586821)
                      ·
                        rfl

theorem cell23_4637111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 2, 2].length) (baseStart_4637111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637111 prefixEnd_4637111 := by exact prefixLift 4637111
  have htrace : WordTrace (prefixWord ++ tailWord_4637111) baseStart_4637111 baseEnd_4637111 := by
    simpa [prefixWord, tailWord_4637111, baseEnd_4637111] using wordTrace_append hprefix tailTrace_4637111
  have hstable : (prefixWord ++ tailWord_4637111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637111).length < 2 ^ (prefixWord ++ tailWord_4637111).sum := by decide
  have hdescent : baseEnd_4637111 < baseStart_4637111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637117 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 7]
def baseStart_4637117 : Nat := 118140960795 + 4637117 * 2 ^ 59
def prefixEnd_4637117 : Nat := 4983230072969 + 3 ^ 40 * 4637117 * 2
def baseEnd_4637117 : Nat := 264563319126115443567977

theorem tailTrace_4637117 : CollatzResearch.WordTrace tailWord_4637117 prefixEnd_4637117 264563319126115443567977 := by
  unfold tailWord_4637117
  simp only [CollatzResearch.WordTrace]
  refine ⟨169129551541524540377829605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112753034361016360251886403 169129551541524540377829605)
  ·
    refine ⟨31711790914035851320843051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169129551541524540377829605 31711790914035851320843051)
    ·
      refine ⟨47567686371053776981264577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31711790914035851320843051 47567686371053776981264577)
      ·
        refine ⟨35675764778290332735948433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47567686371053776981264577 35675764778290332735948433)
        ·
          refine ⟨26756823583717749551961325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35675764778290332735948433 26756823583717749551961325)
          ·
            refine ⟨10033808843894156081985497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26756823583717749551961325 10033808843894156081985497)
            ·
              refine ⟨7525356632920617061489123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10033808843894156081985497 7525356632920617061489123)
              ·
                refine ⟨11288034949380925592233685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7525356632920617061489123 11288034949380925592233685)
                ·
                  refine ⟨264563319126115443567977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11288034949380925592233685 264563319126115443567977)
                  ·
                    rfl

theorem cell23_4637117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_4637117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637117 prefixEnd_4637117 := by exact prefixLift 4637117
  have htrace : WordTrace (prefixWord ++ tailWord_4637117) baseStart_4637117 baseEnd_4637117 := by
    simpa [prefixWord, tailWord_4637117, baseEnd_4637117] using wordTrace_append hprefix tailTrace_4637117
  have hstable : (prefixWord ++ tailWord_4637117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637117).length < 2 ^ (prefixWord ++ tailWord_4637117).sum := by decide
  have hdescent : baseEnd_4637117 < baseStart_4637117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637127 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_4637127 : Nat := 118140960795 + 4637127 * 2 ^ 59
def prefixEnd_4637127 : Nat := 4983230072969 + 3 ^ 40 * 4637127 * 2
def baseEnd_4637127 : Nat := 2381075006941583952986747

theorem tailTrace_4637127 : CollatzResearch.WordTrace tailWord_4637127 prefixEnd_4637127 2381075006941583952986747 := by
  unfold tailWord_4637127
  simp only [CollatzResearch.WordTrace]
  refine ⟨169129916271488312085693635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112753277514325541390462423 169129916271488312085693635)
  ·
    refine ⟨253694874407232468128540453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169129916271488312085693635 253694874407232468128540453)
    ·
      refine ⟨47567788951356087774101335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 253694874407232468128540453 47567788951356087774101335)
      ·
        refine ⟨71351683427034131661152003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47567788951356087774101335 71351683427034131661152003)
        ·
          refine ⟨107027525140551197491728005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71351683427034131661152003 107027525140551197491728005)
          ·
            refine ⟨20067660963853349529699001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107027525140551197491728005 20067660963853349529699001)
            ·
              refine ⟨15050745722890012147274251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20067660963853349529699001 15050745722890012147274251)
              ·
                refine ⟨22576118584335018220911377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15050745722890012147274251 22576118584335018220911377)
                ·
                  refine ⟨16932088938251263665683533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22576118584335018220911377 16932088938251263665683533)
                  ·
                    refine ⟨6349533351844223874631325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16932088938251263665683533 6349533351844223874631325)
                    ·
                      refine ⟨2381075006941583952986747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6349533351844223874631325 2381075006941583952986747)
                      ·
                        rfl

theorem cell23_4637127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_4637127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637127 prefixEnd_4637127 := by exact prefixLift 4637127
  have htrace : WordTrace (prefixWord ++ tailWord_4637127) baseStart_4637127 baseEnd_4637127 := by
    simpa [prefixWord, tailWord_4637127, baseEnd_4637127] using wordTrace_append hprefix tailTrace_4637127
  have hstable : (prefixWord ++ tailWord_4637127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637127).length < 2 ^ (prefixWord ++ tailWord_4637127).sum := by decide
  have hdescent : baseEnd_4637127 < baseStart_4637127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637128 : List Nat := [2, 1, 3, 1, 3, 3, 3, 1, 2, 2, 2]
def baseStart_4637128 : Nat := 118140960795 + 4637128 * 2 ^ 59
def prefixEnd_4637128 : Nat := 4983230072969 + 3 ^ 40 * 4637128 * 2
def baseEnd_4637128 : Nat := 2381075520422238449074243

theorem tailTrace_4637128 : CollatzResearch.WordTrace tailWord_4637128 prefixEnd_4637128 2381075520422238449074243 := by
  unfold tailWord_4637128
  simp only [CollatzResearch.WordTrace]
  refine ⟨84564976372242344628240019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112753301829656459504320025 84564976372242344628240019)
  ·
    refine ⟨126847464558363516942360029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84564976372242344628240019 126847464558363516942360029)
    ·
      refine ⟨47567799209386318853385011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126847464558363516942360029 47567799209386318853385011)
      ·
        refine ⟨71351698814079478280077517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47567799209386318853385011 71351698814079478280077517)
        ·
          refine ⟨26756887055279804355029069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71351698814079478280077517 26756887055279804355029069)
          ·
            refine ⟨10033832645729926633135901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26756887055279804355029069 10033832645729926633135901)
            ·
              refine ⟨3762687242148722487425963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10033832645729926633135901 3762687242148722487425963)
              ·
                refine ⟨5644030863223083731138945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3762687242148722487425963 5644030863223083731138945)
                ·
                  refine ⟨4233023147417312798354209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5644030863223083731138945 4233023147417312798354209)
                  ·
                    refine ⟨3174767360562984598765657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4233023147417312798354209 3174767360562984598765657)
                    ·
                      refine ⟨2381075520422238449074243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3174767360562984598765657 2381075520422238449074243)
                      ·
                        rfl

theorem cell23_4637128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_4637128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637128 prefixEnd_4637128 := by exact prefixLift 4637128
  have htrace : WordTrace (prefixWord ++ tailWord_4637128) baseStart_4637128 baseEnd_4637128 := by
    simpa [prefixWord, tailWord_4637128, baseEnd_4637128] using wordTrace_append hprefix tailTrace_4637128
  have hstable : (prefixWord ++ tailWord_4637128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637128).length < 2 ^ (prefixWord ++ tailWord_4637128).sum := by decide
  have hdescent : baseEnd_4637128 < baseStart_4637128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637130 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 3, 7]
def baseStart_4637130 : Nat := 118140960795 + 4637130 * 2 ^ 59
def prefixEnd_4637130 : Nat := 4983230072969 + 3 ^ 40 * 4637130 * 2
def baseEnd_4637130 : Nat := 793692182461182480416411

theorem tailTrace_4637130 : CollatzResearch.WordTrace tailWord_4637130 prefixEnd_4637130 793692182461182480416411 := by
  unfold tailWord_4637130
  simp only [CollatzResearch.WordTrace]
  refine ⟨42282506422619360899513211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112753350460318295732035229 42282506422619360899513211)
  ·
    refine ⟨63423759633929041349269817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42282506422619360899513211 63423759633929041349269817)
    ·
      refine ⟨47567819725446781011952363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63423759633929041349269817 47567819725446781011952363)
      ·
        refine ⟨71351729588170171517928545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47567819725446781011952363 71351729588170171517928545)
        ·
          refine ⟨53513797191127628638446409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71351729588170171517928545 53513797191127628638446409)
          ·
            refine ⟨40135347893345721478834807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53513797191127628638446409 40135347893345721478834807)
            ·
              refine ⟨60203021840018582218252211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40135347893345721478834807 60203021840018582218252211)
              ·
                refine ⟨90304532760027873327378317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60203021840018582218252211 90304532760027873327378317)
                ·
                  refine ⟨33864199785010452497766869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90304532760027873327378317 33864199785010452497766869)
                  ·
                    refine ⟨793692182461182480416411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33864199785010452497766869 793692182461182480416411)
                    ·
                      rfl

theorem cell23_4637130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_4637130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637130 prefixEnd_4637130 := by exact prefixLift 4637130
  have htrace : WordTrace (prefixWord ++ tailWord_4637130) baseStart_4637130 baseEnd_4637130 := by
    simpa [prefixWord, tailWord_4637130, baseEnd_4637130] using wordTrace_append hprefix tailTrace_4637130
  have hstable : (prefixWord ++ tailWord_4637130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637130).length < 2 ^ (prefixWord ++ tailWord_4637130).sum := by decide
  have hdescent : baseEnd_4637130 < baseStart_4637130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637137 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 2, 5, 2]
def baseStart_4637137 : Nat := 118140960795 + 4637137 * 2 ^ 59
def prefixEnd_4637137 : Nat := 4983230072969 + 3 ^ 40 * 4637137 * 2
def baseEnd_4637137 : Nat := 2381080141748128913861701

theorem tailTrace_4637137 : CollatzResearch.WordTrace tailWord_4637137 prefixEnd_4637137 2381080141748128913861701 := by
  unfold tailWord_4637137
  simp only [CollatzResearch.WordTrace]
  refine ⟨169130281001452083793557665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112753520667634722529038443 169130281001452083793557665)
  ·
    refine ⟨126847710751089062845168249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169130281001452083793557665 126847710751089062845168249)
    ·
      refine ⟨95135783063316797133876187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126847710751089062845168249 95135783063316797133876187)
      ·
        refine ⟨142703674594975195700814281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95135783063316797133876187 142703674594975195700814281)
        ·
          refine ⟨107027755946231396775610711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142703674594975195700814281 107027755946231396775610711)
          ·
            refine ⟨160541633919347095163416067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107027755946231396775610711 160541633919347095163416067)
            ·
              refine ⟨240812450879020642745124101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160541633919347095163416067 240812450879020642745124101)
              ·
                refine ⟨45152334539816370514710769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240812450879020642745124101 45152334539816370514710769)
                ·
                  refine ⟨33864250904862277886033077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45152334539816370514710769 33864250904862277886033077)
                  ·
                    refine ⟨3174773522330838551815601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33864250904862277886033077 3174773522330838551815601)
                    ·
                      refine ⟨2381080141748128913861701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3174773522330838551815601 2381080141748128913861701)
                      ·
                        rfl

theorem cell23_4637137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 5, 2].length) (baseStart_4637137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637137 prefixEnd_4637137 := by exact prefixLift 4637137
  have htrace : WordTrace (prefixWord ++ tailWord_4637137) baseStart_4637137 baseEnd_4637137 := by
    simpa [prefixWord, tailWord_4637137, baseEnd_4637137] using wordTrace_append hprefix tailTrace_4637137
  have hstable : (prefixWord ++ tailWord_4637137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637137).length < 2 ^ (prefixWord ++ tailWord_4637137).sum := by decide
  have hdescent : baseEnd_4637137 < baseStart_4637137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637187 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 3]
def baseStart_4637187 : Nat := 118140960795 + 4637187 * 2 ^ 59
def prefixEnd_4637187 : Nat := 4983230072969 + 3 ^ 40 * 4637187 * 2
def baseEnd_4637187 : Nat := 2381105815780853718236471

theorem tailTrace_4637187 : CollatzResearch.WordTrace tailWord_4637187 prefixEnd_4637187 2381105815780853718236471 := by
  unfold tailWord_4637187
  simp only [CollatzResearch.WordTrace]
  refine ⟨169132104651270942332877815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112754736434180628221918543 169132104651270942332877815)
  ·
    refine ⟨253698156976906413499316723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169132104651270942332877815 253698156976906413499316723)
    ·
      refine ⟨380547235465359620248975085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253698156976906413499316723 380547235465359620248975085)
      ·
        refine ⟨142705213299509857593365657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 380547235465359620248975085 142705213299509857593365657)
        ·
          refine ⟨107028909974632393195024243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142705213299509857593365657 107028909974632393195024243)
          ·
            refine ⟨160543364961948589792536365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107028909974632393195024243 160543364961948589792536365)
            ·
              refine ⟨60203761860730721172201137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160543364961948589792536365 60203761860730721172201137)
              ·
                refine ⟨45152821395548040879150853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60203761860730721172201137 45152821395548040879150853)
                ·
                  refine ⟨8466154011665257664840785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45152821395548040879150853 8466154011665257664840785)
                  ·
                    refine ⟨6349615508748943248630589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8466154011665257664840785 6349615508748943248630589)
                    ·
                      refine ⟨2381105815780853718236471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6349615508748943248630589 2381105815780853718236471)
                      ·
                        rfl

theorem cell23_4637187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_4637187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637187 prefixEnd_4637187 := by exact prefixLift 4637187
  have htrace : WordTrace (prefixWord ++ tailWord_4637187) baseStart_4637187 baseEnd_4637187 := by
    simpa [prefixWord, tailWord_4637187, baseEnd_4637187] using wordTrace_append hprefix tailTrace_4637187
  have hstable : (prefixWord ++ tailWord_4637187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637187).length < 2 ^ (prefixWord ++ tailWord_4637187).sum := by decide
  have hdescent : baseEnd_4637187 < baseStart_4637187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637224 : List Nat := [2, 1, 5, 2, 1, 1, 1, 4, 6]
def baseStart_4637224 : Nat := 118140960795 + 4637224 * 2 ^ 59
def prefixEnd_4637224 : Nat := 4983230072969 + 3 ^ 40 * 4637224 * 2
def baseEnd_4637224 : Nat := 264569423840563341497089

theorem tailTrace_4637224 : CollatzResearch.WordTrace tailWord_4637224 prefixEnd_4637224 264569423840563341497089 := by
  unfold tailWord_4637224
  simp only [CollatzResearch.WordTrace]
  refine ⟨84566727076068448825987363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112755636101424598434649817 84566727076068448825987363)
  ·
    refine ⟨126850090614102673238981045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84566727076068448825987363 126850090614102673238981045)
    ·
      refine ⟨11892195995072125616154473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126850090614102673238981045 11892195995072125616154473)
      ·
        refine ⟨8919146996304094212115855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11892195995072125616154473 8919146996304094212115855)
        ·
          refine ⟨13378720494456141318173783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8919146996304094212115855 13378720494456141318173783)
          ·
            refine ⟨20068080741684211977260675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13378720494456141318173783 20068080741684211977260675)
            ·
              refine ⟨30102121112526317965891013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20068080741684211977260675 30102121112526317965891013)
              ·
                refine ⟨5644147708598684618604565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30102121112526317965891013 5644147708598684618604565)
                ·
                  refine ⟨264569423840563341497089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5644147708598684618604565 264569423840563341497089)
                  ·
                    rfl

theorem cell23_4637224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 6].length) (baseStart_4637224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637224 prefixEnd_4637224 := by exact prefixLift 4637224
  have htrace : WordTrace (prefixWord ++ tailWord_4637224) baseStart_4637224 baseEnd_4637224 := by
    simpa [prefixWord, tailWord_4637224, baseEnd_4637224] using wordTrace_append hprefix tailTrace_4637224
  have hstable : (prefixWord ++ tailWord_4637224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637224).length < 2 ^ (prefixWord ++ tailWord_4637224).sum := by decide
  have hdescent : baseEnd_4637224 < baseStart_4637224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637237 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 5, 5]
def baseStart_4637237 : Nat := 118140960795 + 4637237 * 2 ^ 59
def prefixEnd_4637237 : Nat := 4983230072969 + 3 ^ 40 * 4637237 * 2
def baseEnd_4637237 : Nat := 793710496604526174203747

theorem tailTrace_4637237 : CollatzResearch.WordTrace tailWord_4637237 prefixEnd_4637237 793710496604526174203747 := by
  unfold tailWord_4637237
  simp only [CollatzResearch.WordTrace]
  refine ⟨169133928301089800872197965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112755952200726533914798643 169133928301089800872197965)
  ·
    refine ⟨63425223112908675327074237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169133928301089800872197965 63425223112908675327074237)
    ·
      refine ⟨23784458667340753247652839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63425223112908675327074237 23784458667340753247652839)
      ·
        refine ⟨35676688001011129871479259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23784458667340753247652839 35676688001011129871479259)
        ·
          refine ⟨53515032001516694807218889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35676688001011129871479259 53515032001516694807218889)
          ·
            refine ⟨40136274001137521105414167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53515032001516694807218889 40136274001137521105414167)
            ·
              refine ⟨60204411001706281658121251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40136274001137521105414167 60204411001706281658121251)
              ·
                refine ⟨90306616502559422487181877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60204411001706281658121251 90306616502559422487181877)
                ·
                  refine ⟨8466245297114945858173301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90306616502559422487181877 8466245297114945858173301)
                  ·
                    refine ⟨793710496604526174203747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8466245297114945858173301 793710496604526174203747)
                    ·
                      rfl

theorem cell23_4637237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_4637237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637237 prefixEnd_4637237 := by exact prefixLift 4637237
  have htrace : WordTrace (prefixWord ++ tailWord_4637237) baseStart_4637237 baseEnd_4637237 := by
    simpa [prefixWord, tailWord_4637237, baseEnd_4637237] using wordTrace_append hprefix tailTrace_4637237
  have hstable : (prefixWord ++ tailWord_4637237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637237).length < 2 ^ (prefixWord ++ tailWord_4637237).sum := by decide
  have hdescent : baseEnd_4637237 < baseStart_4637237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637252 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_4637252 : Nat := 118140960795 + 4637252 * 2 ^ 59
def prefixEnd_4637252 : Nat := 4983230072969 + 3 ^ 40 * 4637252 * 2
def baseEnd_4637252 : Nat := 2381139192023395963923673

theorem tailTrace_4637252 : CollatzResearch.WordTrace tailWord_4637252 prefixEnd_4637252 2381139192023395963923673 := by
  unfold tailWord_4637252
  simp only [CollatzResearch.WordTrace]
  refine ⟨84567237698017729216997005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112756316930690305622662673 84567237698017729216997005)
  ·
    refine ⟨31712714136756648456373877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84567237698017729216997005 31712714136756648456373877)
    ·
      refine ⟨2973066950320935792785051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31712714136756648456373877 2973066950320935792785051)
      ·
        refine ⟨4459600425481403689177577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2973066950320935792785051 4459600425481403689177577)
        ·
          refine ⟨3344700319111052766883183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4459600425481403689177577 3344700319111052766883183)
          ·
            refine ⟨5017050478666579150324775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3344700319111052766883183 5017050478666579150324775)
            ·
              refine ⟨7525575717999868725487163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5017050478666579150324775 7525575717999868725487163)
              ·
                refine ⟨11288363576999803088230745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7525575717999868725487163 11288363576999803088230745)
                ·
                  refine ⟨8466272682749852316173059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11288363576999803088230745 8466272682749852316173059)
                  ·
                    refine ⟨12699409024124778474259589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8466272682749852316173059 12699409024124778474259589)
                    ·
                      refine ⟨2381139192023395963923673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12699409024124778474259589 2381139192023395963923673)
                      ·
                        rfl

theorem cell23_4637252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_4637252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637252 prefixEnd_4637252 := by exact prefixLift 4637252
  have htrace : WordTrace (prefixWord ++ tailWord_4637252) baseStart_4637252 baseEnd_4637252 := by
    simpa [prefixWord, tailWord_4637252, baseEnd_4637252] using wordTrace_append hprefix tailTrace_4637252
  have hstable : (prefixWord ++ tailWord_4637252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637252).length < 2 ^ (prefixWord ++ tailWord_4637252).sum := by decide
  have hdescent : baseEnd_4637252 < baseStart_4637252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637268 : List Nat := [2, 4, 1, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_4637268 : Nat := 118140960795 + 4637268 * 2 ^ 59
def prefixEnd_4637268 : Nat := 4983230072969 + 3 ^ 40 * 4637268 * 2
def baseEnd_4637268 : Nat := 2381147407713867901323599

theorem tailTrace_4637268 : CollatzResearch.WordTrace tailWord_4637268 prefixEnd_4637268 2381147407713867901323599 := by
  unfold tailWord_4637268
  simp only [CollatzResearch.WordTrace]
  refine ⟨84567529481988746583288229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112756705975984995444384305 84567529481988746583288229)
  ·
    refine ⟨15856411777872889984366543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84567529481988746583288229 15856411777872889984366543)
    ·
      refine ⟨23784617666809334976549815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15856411777872889984366543 23784617666809334976549815)
      ·
        refine ⟨35676926500214002464824723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23784617666809334976549815 35676926500214002464824723)
        ·
          refine ⟨53515389750321003697237085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35676926500214002464824723 53515389750321003697237085)
          ·
            refine ⟨20068271156370376386463907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53515389750321003697237085 20068271156370376386463907)
            ·
              refine ⟨30102406734555564579695861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20068271156370376386463907 30102406734555564579695861)
              ·
                refine ⟨2822100631364584179346487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30102406734555564579695861 2822100631364584179346487)
                ·
                  refine ⟨4233150947046876269019731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2822100631364584179346487 4233150947046876269019731)
                  ·
                    refine ⟨6349726420570314403529597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4233150947046876269019731 6349726420570314403529597)
                    ·
                      refine ⟨2381147407713867901323599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6349726420570314403529597 2381147407713867901323599)
                      ·
                        rfl

theorem cell23_4637268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_4637268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637268 prefixEnd_4637268 := by exact prefixLift 4637268
  have htrace : WordTrace (prefixWord ++ tailWord_4637268) baseStart_4637268 baseEnd_4637268 := by
    simpa [prefixWord, tailWord_4637268, baseEnd_4637268] using wordTrace_append hprefix tailTrace_4637268
  have hstable : (prefixWord ++ tailWord_4637268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637268).length < 2 ^ (prefixWord ++ tailWord_4637268).sum := by decide
  have hdescent : baseEnd_4637268 < baseStart_4637268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637284 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_4637284 : Nat := 118140960795 + 4637284 * 2 ^ 59
def prefixEnd_4637284 : Nat := 4983230072969 + 3 ^ 40 * 4637284 * 2
def baseEnd_4637284 : Nat := 793718541134779946241175

theorem tailTrace_4637284 : CollatzResearch.WordTrace tailWord_4637284 prefixEnd_4637284 793718541134779946241175 := by
  unfold tailWord_4637284
  simp only [CollatzResearch.WordTrace]
  refine ⟨84567821265959763949579453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112757095021279685266105937 84567821265959763949579453)
  ·
    refine ⟨31712932974734911481092295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84567821265959763949579453 31712932974734911481092295)
    ·
      refine ⟨47569399462102367221638443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31712932974734911481092295 47569399462102367221638443)
      ·
        refine ⟨71354099193153550832457665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47569399462102367221638443 71354099193153550832457665)
        ·
          refine ⟨53515574394865163124343249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71354099193153550832457665 53515574394865163124343249)
          ·
            refine ⟨40136680796148872343257437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53515574394865163124343249 40136680796148872343257437)
            ·
              refine ⟨15051255298555827128721539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40136680796148872343257437 15051255298555827128721539)
              ·
                refine ⟨22576882947833740693082309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15051255298555827128721539 22576882947833740693082309)
                ·
                  refine ⟨4233165552718826379952933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22576882947833740693082309 4233165552718826379952933)
                  ·
                    refine ⟨793718541134779946241175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4233165552718826379952933 793718541134779946241175)
                    ·
                      rfl

theorem cell23_4637284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_4637284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637284 prefixEnd_4637284 := by exact prefixLift 4637284
  have htrace : WordTrace (prefixWord ++ tailWord_4637284) baseStart_4637284 baseEnd_4637284 := by
    simpa [prefixWord, tailWord_4637284, baseEnd_4637284] using wordTrace_append hprefix tailTrace_4637284
  have hstable : (prefixWord ++ tailWord_4637284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637284).length < 2 ^ (prefixWord ++ tailWord_4637284).sum := by decide
  have hdescent : baseEnd_4637284 < baseStart_4637284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637287 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_4637287 : Nat := 118140960795 + 4637287 * 2 ^ 59
def prefixEnd_4637287 : Nat := 4983230072969 + 3 ^ 40 * 4637287 * 2
def baseEnd_4637287 : Nat := 2381157163846303326986011

theorem tailTrace_4637287 : CollatzResearch.WordTrace tailWord_4637287 prefixEnd_4637287 2381157163846303326986011 := by
  unfold tailWord_4637287
  simp only [CollatzResearch.WordTrace]
  refine ⟨169135751950908659411518115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112757167967272439607678743 169135751950908659411518115)
  ·
    refine ⟨253703627926362989117277173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169135751950908659411518115 253703627926362989117277173)
    ·
      refine ⟨23784715118096530229744735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 253703627926362989117277173 23784715118096530229744735)
      ·
        refine ⟨35677072677144795344617103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23784715118096530229744735 35677072677144795344617103)
        ·
          refine ⟨53515609015717193016925655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35677072677144795344617103 53515609015717193016925655)
          ·
            refine ⟨80273413523575789525388483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53515609015717193016925655 80273413523575789525388483)
            ·
              refine ⟨120410120285363684288082725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80273413523575789525388483 120410120285363684288082725)
              ·
                refine ⟨22576897553505690804015511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120410120285363684288082725 22576897553505690804015511)
                ·
                  refine ⟨33865346330258536206023267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22576897553505690804015511 33865346330258536206023267)
                  ·
                    refine ⟨50798019495387804309034901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33865346330258536206023267 50798019495387804309034901)
                    ·
                      refine ⟨2381157163846303326986011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50798019495387804309034901 2381157163846303326986011)
                      ·
                        rfl

theorem cell23_4637287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_4637287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637287 prefixEnd_4637287 := by exact prefixLift 4637287
  have htrace : WordTrace (prefixWord ++ tailWord_4637287) baseStart_4637287 baseEnd_4637287 := by
    simpa [prefixWord, tailWord_4637287, baseEnd_4637287] using wordTrace_append hprefix tailTrace_4637287
  have hstable : (prefixWord ++ tailWord_4637287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637287).length < 2 ^ (prefixWord ++ tailWord_4637287).sum := by decide
  have hdescent : baseEnd_4637287 < baseStart_4637287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637294 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_4637294 : Nat := 118140960795 + 4637294 * 2 ^ 59
def prefixEnd_4637294 : Nat := 4983230072969 + 3 ^ 40 * 4637294 * 2
def baseEnd_4637294 : Nat := 2381160758210884799598479

theorem tailTrace_4637294 : CollatzResearch.WordTrace tailWord_4637294 prefixEnd_4637294 2381160758210884799598479 := by
  unfold tailWord_4637294
  simp only [CollatzResearch.WordTrace]
  refine ⟨21142000907735412450877867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112757338174588866404681957 21142000907735412450877867)
  ·
    refine ⟨31713001361603118676316801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21142000907735412450877867 31713001361603118676316801)
    ·
      refine ⟨23784751021202339007237601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31713001361603118676316801 23784751021202339007237601)
      ·
        refine ⟨17838563265901754255428201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23784751021202339007237601 17838563265901754255428201)
        ·
          refine ⟨13378922449426315691571151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17838563265901754255428201 13378922449426315691571151)
          ·
            refine ⟨20068383674139473537356727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13378922449426315691571151 20068383674139473537356727)
            ·
              refine ⟨30102575511209210306035091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20068383674139473537356727 30102575511209210306035091)
              ·
                refine ⟨45153863266813815459052637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30102575511209210306035091 45153863266813815459052637)
                ·
                  refine ⟨16932698725055180797144739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45153863266813815459052637 16932698725055180797144739)
                  ·
                    refine ⟨25399048087582771195717109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16932698725055180797144739 25399048087582771195717109)
                    ·
                      refine ⟨2381160758210884799598479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25399048087582771195717109 2381160758210884799598479)
                      ·
                        rfl

theorem cell23_4637294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_4637294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637294 prefixEnd_4637294 := by exact prefixLift 4637294
  have htrace : WordTrace (prefixWord ++ tailWord_4637294) baseStart_4637294 baseEnd_4637294 := by
    simpa [prefixWord, tailWord_4637294, baseEnd_4637294] using wordTrace_append hprefix tailTrace_4637294
  have hstable : (prefixWord ++ tailWord_4637294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637294).length < 2 ^ (prefixWord ++ tailWord_4637294).sum := by decide
  have hdescent : baseEnd_4637294 < baseStart_4637294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637337 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 5]
def baseStart_4637337 : Nat := 118140960795 + 4637337 * 2 ^ 59
def prefixEnd_4637337 : Nat := 4983230072969 + 3 ^ 40 * 4637337 * 2
def baseEnd_4637337 : Nat := 2381182837879028131360781

theorem tailTrace_4637337 : CollatzResearch.WordTrace tailWord_4637337 prefixEnd_4637337 2381182837879028131360781 := by
  unfold tailWord_4637337
  simp only [CollatzResearch.WordTrace]
  refine ⟨169137575600727517950838265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112758383733818345300558843 169137575600727517950838265)
  ·
    refine ⟨126853181700545638463128699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169137575600727517950838265 126853181700545638463128699)
    ·
      refine ⟨190279772550818457694693049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126853181700545638463128699 190279772550818457694693049)
      ·
        refine ⟨142709829413113843271019787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190279772550818457694693049 142709829413113843271019787)
        ·
          refine ⟨214064744119670764906529681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142709829413113843271019787 214064744119670764906529681)
          ·
            refine ⟨160548558089753073679897261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214064744119670764906529681 160548558089753073679897261)
            ·
              refine ⟨60205709283657402629961473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160548558089753073679897261 60205709283657402629961473)
              ·
                refine ⟨45154281962743051972471105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60205709283657402629961473 45154281962743051972471105)
                ·
                  refine ⟨33865711472057288979353329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45154281962743051972471105 33865711472057288979353329)
                  ·
                    refine ⟨25399283604042966734514997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33865711472057288979353329 25399283604042966734514997)
                    ·
                      refine ⟨2381182837879028131360781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25399283604042966734514997 2381182837879028131360781)
                      ·
                        rfl

theorem cell23_4637337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_4637337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637337 prefixEnd_4637337 := by exact prefixLift 4637337
  have htrace : WordTrace (prefixWord ++ tailWord_4637337) baseStart_4637337 baseEnd_4637337 := by
    simpa [prefixWord, tailWord_4637337, baseEnd_4637337] using wordTrace_append hprefix tailTrace_4637337
  have hstable : (prefixWord ++ tailWord_4637337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637337).length < 2 ^ (prefixWord ++ tailWord_4637337).sum := by decide
  have hdescent : baseEnd_4637337 < baseStart_4637337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637341 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_4637341 : Nat := 118140960795 + 4637341 * 2 ^ 59
def prefixEnd_4637341 : Nat := 4983230072969 + 3 ^ 40 * 4637341 * 2
def baseEnd_4637341 : Nat := 2381184891801646115710763

theorem tailTrace_4637341 : CollatzResearch.WordTrace tailWord_4637341 prefixEnd_4637341 2381184891801646115710763 := by
  unfold tailWord_4637341
  simp only [CollatzResearch.WordTrace]
  refine ⟨169137721492713026633983877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112758480995142017755989251 169137721492713026633983877)
  ·
    refine ⟨31713322779883692493871977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169137721492713026633983877 31713322779883692493871977)
    ·
      refine ⟨23784992084912769370403983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31713322779883692493871977 23784992084912769370403983)
      ·
        refine ⟨35677488127369154055605975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23784992084912769370403983 35677488127369154055605975)
        ·
          refine ⟨53516232191053731083408963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35677488127369154055605975 53516232191053731083408963)
          ·
            refine ⟨80274348286580596625113445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53516232191053731083408963 80274348286580596625113445)
            ·
              refine ⟨15051440303733861867208771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80274348286580596625113445 15051440303733861867208771)
              ·
                refine ⟨22577160455600792800813157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15051440303733861867208771 22577160455600792800813157)
                ·
                  refine ⟨4233217585425148650152467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22577160455600792800813157 4233217585425148650152467)
                  ·
                    refine ⟨6349826378137722975228701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4233217585425148650152467 6349826378137722975228701)
                    ·
                      refine ⟨2381184891801646115710763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6349826378137722975228701 2381184891801646115710763)
                      ·
                        rfl

theorem cell23_4637341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_4637341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637341 prefixEnd_4637341 := by exact prefixLift 4637341
  have htrace : WordTrace (prefixWord ++ tailWord_4637341) baseStart_4637341 baseEnd_4637341 := by
    simpa [prefixWord, tailWord_4637341, baseEnd_4637341] using wordTrace_append hprefix tailTrace_4637341
  have hstable : (prefixWord ++ tailWord_4637341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637341).length < 2 ^ (prefixWord ++ tailWord_4637341).sum := by decide
  have hdescent : baseEnd_4637341 < baseStart_4637341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637384 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_4637384 : Nat := 118140960795 + 4637384 * 2 ^ 59
def prefixEnd_4637384 : Nat := 4983230072969 + 3 ^ 40 * 4637384 * 2
def baseEnd_4637384 : Nat := 2381206971469789447473065

theorem tailTrace_4637384 : CollatzResearch.WordTrace tailWord_4637384 prefixEnd_4637384 2381206971469789447473065 := by
  unfold tailWord_4637384
  simp only [CollatzResearch.WordTrace]
  refine ⟨84569644915778622488899603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112759526554371496651866137 84569644915778622488899603)
  ·
    refine ⟨126854467373667933733349405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84569644915778622488899603 126854467373667933733349405)
    ·
      refine ⟨47570425265125475150006027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126854467373667933733349405 47570425265125475150006027)
      ·
        refine ⟨71355637897688212725009041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47570425265125475150006027 71355637897688212725009041)
        ·
          refine ⟨53516728423266159543756781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71355637897688212725009041 53516728423266159543756781)
          ·
            refine ⟨20068773158724809828908793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53516728423266159543756781 20068773158724809828908793)
            ·
              refine ⟨15051579869043607371681595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20068773158724809828908793 15051579869043607371681595)
              ·
                refine ⟨22577369803565411057522393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15051579869043607371681595 22577369803565411057522393)
                ·
                  refine ⟨16933027352674058293141795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22577369803565411057522393 16933027352674058293141795)
                  ·
                    refine ⟨25399541029011087439712693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16933027352674058293141795 25399541029011087439712693)
                    ·
                      refine ⟨2381206971469789447473065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25399541029011087439712693 2381206971469789447473065)
                      ·
                        rfl

theorem cell23_4637384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_4637384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637384 prefixEnd_4637384 := by exact prefixLift 4637384
  have htrace : WordTrace (prefixWord ++ tailWord_4637384) baseStart_4637384 baseEnd_4637384 := by
    simpa [prefixWord, tailWord_4637384, baseEnd_4637384] using wordTrace_append hprefix tailTrace_4637384
  have hstable : (prefixWord ++ tailWord_4637384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637384).length < 2 ^ (prefixWord ++ tailWord_4637384).sum := by decide
  have hdescent : baseEnd_4637384 < baseStart_4637384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637411 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4637411 : Nat := 118140960795 + 4637411 * 2 ^ 59
def prefixEnd_4637411 : Nat := 4983230072969 + 3 ^ 40 * 4637411 * 2
def baseEnd_4637411 : Nat := 2381220835447460841835441

theorem tailTrace_4637411 : CollatzResearch.WordTrace tailWord_4637411 prefixEnd_4637411 2381220835447460841835441 := by
  unfold tailWord_4637411
  simp only [CollatzResearch.WordTrace]
  refine ⟨169140274602459428589032087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112760183068306285726021391 169140274602459428589032087)
  ·
    refine ⟨253710411903689142883548131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169140274602459428589032087 253710411903689142883548131)
    ·
      refine ⟨380565617855533714325322197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253710411903689142883548131 380565617855533714325322197)
      ·
        refine ⟨8919506668489071429499739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 380565617855533714325322197 8919506668489071429499739)
        ·
          refine ⟨13379260002733607144249609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8919506668489071429499739 13379260002733607144249609)
          ·
            refine ⟨10034445002050205358187207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13379260002733607144249609 10034445002050205358187207)
            ·
              refine ⟨15051667503075308037280811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10034445002050205358187207 15051667503075308037280811)
              ·
                refine ⟨22577501254612962055921217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15051667503075308037280811 22577501254612962055921217)
                ·
                  refine ⟨16933125940959721541940913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22577501254612962055921217 16933125940959721541940913)
                  ·
                    refine ⟨12699844455719791156455685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16933125940959721541940913 12699844455719791156455685)
                    ·
                      refine ⟨2381220835447460841835441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12699844455719791156455685 2381220835447460841835441)
                      ·
                        rfl

theorem cell23_4637411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4637411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637411 prefixEnd_4637411 := by exact prefixLift 4637411
  have htrace : WordTrace (prefixWord ++ tailWord_4637411) baseStart_4637411 baseEnd_4637411 := by
    simpa [prefixWord, tailWord_4637411, baseEnd_4637411] using wordTrace_append hprefix tailTrace_4637411
  have hstable : (prefixWord ++ tailWord_4637411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637411).length < 2 ^ (prefixWord ++ tailWord_4637411).sum := by decide
  have hdescent : baseEnd_4637411 < baseStart_4637411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637438 : List Nat := [4, 2, 2, 1, 2, 1, 1, 5, 5]
def baseStart_4637438 : Nat := 118140960795 + 4637438 * 2 ^ 59
def prefixEnd_4637438 : Nat := 4983230072969 + 3 ^ 40 * 4637438 * 2
def baseEnd_4637438 : Nat := 264581633269459137355313

theorem tailTrace_4637438 : CollatzResearch.WordTrace tailWord_4637438 prefixEnd_4637438 264581633269459137355313 := by
  unfold tailWord_4637438
  simp only [CollatzResearch.WordTrace]
  refine ⟨21142657421670201525033121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112760839582241074800176645 21142657421670201525033121)
  ·
    refine ⟨15856993066252651143774841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21142657421670201525033121 15856993066252651143774841)
    ·
      refine ⟨11892744799689488357831131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15856993066252651143774841 11892744799689488357831131)
      ·
        refine ⟨17839117199534232536746697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11892744799689488357831131 17839117199534232536746697)
        ·
          refine ⟨13379337899650674402560023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17839117199534232536746697 13379337899650674402560023)
          ·
            refine ⟨20069006849476011603840035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13379337899650674402560023 20069006849476011603840035)
            ·
              refine ⟨30103510274214017405760053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20069006849476011603840035 30103510274214017405760053)
              ·
                refine ⟨2822204088207564131790005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30103510274214017405760053 2822204088207564131790005)
                ·
                  refine ⟨264581633269459137355313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2822204088207564131790005 264581633269459137355313)
                  ·
                    rfl

theorem cell23_4637438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_4637438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637438 prefixEnd_4637438 := by exact prefixLift 4637438
  have htrace : WordTrace (prefixWord ++ tailWord_4637438) baseStart_4637438 baseEnd_4637438 := by
    simpa [prefixWord, tailWord_4637438, baseEnd_4637438] using wordTrace_append hprefix tailTrace_4637438
  have hstable : (prefixWord ++ tailWord_4637438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637438).length < 2 ^ (prefixWord ++ tailWord_4637438).sum := by decide
  have hdescent : baseEnd_4637438 < baseStart_4637438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637484 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_4637484 : Nat := 118140960795 + 4637484 * 2 ^ 59
def prefixEnd_4637484 : Nat := 4983230072969 + 3 ^ 40 * 4637484 * 2
def baseEnd_4637484 : Nat := 2381258319535239056222605

theorem tailTrace_4637484 : CollatzResearch.WordTrace tailWord_4637484 prefixEnd_4637484 2381258319535239056222605 := by
  unfold tailWord_4637484
  simp only [CollatzResearch.WordTrace]
  refine ⟨84571468565597481028219753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112761958087463308037626337 84571468565597481028219753)
  ·
    refine ⟨63428601424198110771164815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84571468565597481028219753 63428601424198110771164815)
    ·
      refine ⟨95142902136297166156747223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63428601424198110771164815 95142902136297166156747223)
      ·
        refine ⟨142714353204445749235120835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95142902136297166156747223 142714353204445749235120835)
        ·
          refine ⟨214071529806668623852681253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142714353204445749235120835 214071529806668623852681253)
          ·
            refine ⟨40138411838750366972377735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214071529806668623852681253 40138411838750366972377735)
            ·
              refine ⟨60207617758125550458566603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40138411838750366972377735 60207617758125550458566603)
              ·
                refine ⟨90311426637188325687849905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60207617758125550458566603 90311426637188325687849905)
                ·
                  refine ⟨67733569977891244265887429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90311426637188325687849905 67733569977891244265887429)
                  ·
                    refine ⟨12700044370854608299853893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67733569977891244265887429 12700044370854608299853893)
                    ·
                      refine ⟨2381258319535239056222605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12700044370854608299853893 2381258319535239056222605)
                      ·
                        rfl

theorem cell23_4637484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_4637484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637484 prefixEnd_4637484 := by exact prefixLift 4637484
  have htrace : WordTrace (prefixWord ++ tailWord_4637484) baseStart_4637484 baseEnd_4637484 := by
    simpa [prefixWord, tailWord_4637484, baseEnd_4637484] using wordTrace_append hprefix tailTrace_4637484
  have hstable : (prefixWord ++ tailWord_4637484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637484).length < 2 ^ (prefixWord ++ tailWord_4637484).sum := by decide
  have hdescent : baseEnd_4637484 < baseStart_4637484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637491 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 3]
def baseStart_4637491 : Nat := 118140960795 + 4637491 * 2 ^ 59
def prefixEnd_4637491 : Nat := 4983230072969 + 3 ^ 40 * 4637491 * 2
def baseEnd_4637491 : Nat := 2381261913899820528835073

theorem tailTrace_4637491 : CollatzResearch.WordTrace tailWord_4637491 prefixEnd_4637491 2381261913899820528835073 := by
  unfold tailWord_4637491
  simp only [CollatzResearch.WordTrace]
  refine ⟨169143192442169602251944327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112762128294779734834629551 169143192442169602251944327)
  ·
    refine ⟨253714788663254403377916491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169143192442169602251944327 253714788663254403377916491)
    ·
      refine ⟨380572182994881605066874737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253714788663254403377916491 380572182994881605066874737)
      ·
        refine ⟨285429137246161203800156053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380572182994881605066874737 285429137246161203800156053)
        ·
          refine ⟨13379490808413806428132315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 285429137246161203800156053 13379490808413806428132315)
          ·
            refine ⟨20069236212620709642198473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13379490808413806428132315 20069236212620709642198473)
            ·
              refine ⟨15051927159465532231648855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20069236212620709642198473 15051927159465532231648855)
              ·
                refine ⟨22577890739198298347473283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15051927159465532231648855 22577890739198298347473283)
                ·
                  refine ⟨33866836108797447521209925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22577890739198298347473283 33866836108797447521209925)
                  ·
                    refine ⟨6350031770399521410226861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33866836108797447521209925 6350031770399521410226861)
                    ·
                      refine ⟨2381261913899820528835073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6350031770399521410226861 2381261913899820528835073)
                      ·
                        rfl

theorem cell23_4637491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 3].length) (baseStart_4637491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637491 prefixEnd_4637491 := by exact prefixLift 4637491
  have htrace : WordTrace (prefixWord ++ tailWord_4637491) baseStart_4637491 baseEnd_4637491 := by
    simpa [prefixWord, tailWord_4637491, baseEnd_4637491] using wordTrace_append hprefix tailTrace_4637491
  have hstable : (prefixWord ++ tailWord_4637491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637491).length < 2 ^ (prefixWord ++ tailWord_4637491).sum := by decide
  have hdescent : baseEnd_4637491 < baseStart_4637491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637505 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4637505 : Nat := 118140960795 + 4637505 * 2 ^ 59
def prefixEnd_4637505 : Nat := 4983230072969 + 3 ^ 40 * 4637505 * 2
def baseEnd_4637505 : Nat := 2381269102628983474060009

theorem tailTrace_4637505 : CollatzResearch.WordTrace tailWord_4637505 prefixEnd_4637505 2381269102628983474060009 := by
  unfold tailWord_4637505
  simp only [CollatzResearch.WordTrace]
  refine ⟨169143703064118882642953969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112762468709412588428635979 169143703064118882642953969)
  ·
    refine ⟨126857777298089161982215477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169143703064118882642953969 126857777298089161982215477)
    ·
      refine ⟨11892916621695858935832701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126857777298089161982215477 11892916621695858935832701)
      ·
        refine ⟨4459843733135947100937263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11892916621695858935832701 4459843733135947100937263)
        ·
          refine ⟨6689765599703920651405895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4459843733135947100937263 6689765599703920651405895)
          ·
            refine ⟨10034648399555880977108843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6689765599703920651405895 10034648399555880977108843)
            ·
              refine ⟨15051972599333821465663265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10034648399555880977108843 15051972599333821465663265)
              ·
                refine ⟨11288979449500366099247449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15051972599333821465663265 11288979449500366099247449)
                ·
                  refine ⟨8466734587125274574435587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11288979449500366099247449 8466734587125274574435587)
                  ·
                    refine ⟨12700101880687911861653381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8466734587125274574435587 12700101880687911861653381)
                    ·
                      refine ⟨2381269102628983474060009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12700101880687911861653381 2381269102628983474060009)
                      ·
                        rfl

theorem cell23_4637505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4637505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637505 prefixEnd_4637505 := by exact prefixLift 4637505
  have htrace : WordTrace (prefixWord ++ tailWord_4637505) baseStart_4637505 baseEnd_4637505 := by
    simpa [prefixWord, tailWord_4637505, baseEnd_4637505] using wordTrace_append hprefix tailTrace_4637505
  have hstable : (prefixWord ++ tailWord_4637505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637505).length < 2 ^ (prefixWord ++ tailWord_4637505).sum := by decide
  have hdescent : baseEnd_4637505 < baseStart_4637505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637514 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_4637514 : Nat := 118140960795 + 4637514 * 2 ^ 59
def prefixEnd_4637514 : Nat := 4983230072969 + 3 ^ 40 * 4637514 * 2
def baseEnd_4637514 : Nat := 2381273723954873938847467

theorem tailTrace_4637514 : CollatzResearch.WordTrace tailWord_4637514 prefixEnd_4637514 2381273723954873938847467 := by
  unfold tailWord_4637514
  simp only [CollatzResearch.WordTrace]
  refine ⟨42286007830271569295007899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112762687547390851453354397 42286007830271569295007899)
  ·
    refine ⟨63429011745407353942511849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42286007830271569295007899 63429011745407353942511849)
    ·
      refine ⟨47571758809055515456883887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63429011745407353942511849 47571758809055515456883887)
      ·
        refine ⟨71357638213583273185325831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47571758809055515456883887 71357638213583273185325831)
        ·
          refine ⟨107036457320374909777988747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71357638213583273185325831 107036457320374909777988747)
          ·
            refine ⟨160554685980562364666983121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107036457320374909777988747 160554685980562364666983121)
            ·
              refine ⟨120416014485421773500237341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160554685980562364666983121 120416014485421773500237341)
              ·
                refine ⟨45156005432033165062589003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120416014485421773500237341 45156005432033165062589003)
                ·
                  refine ⟨67734008148049747593883505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45156005432033165062589003 67734008148049747593883505)
                  ·
                    refine ⟨50800506111037310695412629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67734008148049747593883505 50800506111037310695412629)
                    ·
                      refine ⟨2381273723954873938847467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50800506111037310695412629 2381273723954873938847467)
                      ·
                        rfl

theorem cell23_4637514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_4637514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637514 prefixEnd_4637514 := by exact prefixLift 4637514
  have htrace : WordTrace (prefixWord ++ tailWord_4637514) baseStart_4637514 baseEnd_4637514 := by
    simpa [prefixWord, tailWord_4637514, baseEnd_4637514] using wordTrace_append hprefix tailTrace_4637514
  have hstable : (prefixWord ++ tailWord_4637514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637514).length < 2 ^ (prefixWord ++ tailWord_4637514).sum := by decide
  have hdescent : baseEnd_4637514 < baseStart_4637514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637566 : List Nat := [4, 2, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4637566 : Nat := 118140960795 + 4637566 * 2 ^ 59
def prefixEnd_4637566 : Nat := 4983230072969 + 3 ^ 40 * 4637566 * 2
def baseEnd_4637566 : Nat := 793766808316302578465743

theorem tailTrace_4637566 : CollatzResearch.WordTrace tailWord_4637566 prefixEnd_4637566 793766808316302578465743 := by
  unfold tailWord_4637566
  simp only [CollatzResearch.WordTrace]
  refine ⟨21143240989612236257615569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112763951944598593373949701 21143240989612236257615569)
  ·
    refine ⟨15857430742209177193211677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21143240989612236257615569 15857430742209177193211677)
    ·
      refine ⟨5946536528328441447454379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15857430742209177193211677 5946536528328441447454379)
      ·
        refine ⟨8919804792492662171181569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5946536528328441447454379 8919804792492662171181569)
        ·
          refine ⟨6689853594369496628386177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8919804792492662171181569 6689853594369496628386177)
          ·
            refine ⟨5017390195777122471289633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6689853594369496628386177 5017390195777122471289633)
            ·
              refine ⟨3763042646832841853467225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5017390195777122471289633 3763042646832841853467225)
              ·
                refine ⟨2822281985124631390100419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3763042646832841853467225 2822281985124631390100419)
                ·
                  refine ⟨4233422977686947085150629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2822281985124631390100419 4233422977686947085150629)
                  ·
                    refine ⟨793766808316302578465743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4233422977686947085150629 793766808316302578465743)
                    ·
                      rfl

theorem cell23_4637566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4637566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637566 prefixEnd_4637566 := by exact prefixLift 4637566
  have htrace : WordTrace (prefixWord ++ tailWord_4637566) baseStart_4637566 baseEnd_4637566 := by
    simpa [prefixWord, tailWord_4637566, baseEnd_4637566] using wordTrace_append hprefix tailTrace_4637566
  have hstable : (prefixWord ++ tailWord_4637566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637566).length < 2 ^ (prefixWord ++ tailWord_4637566).sum := by decide
  have hdescent : baseEnd_4637566 < baseStart_4637566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637578 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_4637578 : Nat := 118140960795 + 4637578 * 2 ^ 59
def prefixEnd_4637578 : Nat := 4983230072969 + 3 ^ 40 * 4637578 * 2
def baseEnd_4637578 : Nat := 2381306586716761688447173

theorem tailTrace_4637578 : CollatzResearch.WordTrace tailWord_4637578 prefixEnd_4637578 2381306586716761688447173 := by
  unfold tailWord_4637578
  simp only [CollatzResearch.WordTrace]
  refine ⟨42286591398213604027590347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112764243728569610740240925 42286591398213604027590347)
  ·
    refine ⟨63429887097320406041385521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42286591398213604027590347 63429887097320406041385521)
    ·
      refine ⟨47572415322990304531039141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63429887097320406041385521 47572415322990304531039141)
      ·
        refine ⟨8919827873060682099569839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47572415322990304531039141 8919827873060682099569839)
        ·
          refine ⟨13379741809591023149354759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8919827873060682099569839 13379741809591023149354759)
          ·
            refine ⟨20069612714386534724032139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13379741809591023149354759 20069612714386534724032139)
            ·
              refine ⟨30104419071579802086048209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20069612714386534724032139 30104419071579802086048209)
              ·
                refine ⟨22578314303684851564536157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30104419071579802086048209 22578314303684851564536157)
                ·
                  refine ⟨8466867863881819336701059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22578314303684851564536157 8466867863881819336701059)
                  ·
                    refine ⟨12700301795822729005051589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8466867863881819336701059 12700301795822729005051589)
                    ·
                      refine ⟨2381306586716761688447173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12700301795822729005051589 2381306586716761688447173)
                      ·
                        rfl

theorem cell23_4637578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_4637578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637578 prefixEnd_4637578 := by exact prefixLift 4637578
  have htrace : WordTrace (prefixWord ++ tailWord_4637578) baseStart_4637578 baseEnd_4637578 := by
    simpa [prefixWord, tailWord_4637578, baseEnd_4637578] using wordTrace_append hprefix tailTrace_4637578
  have hstable : (prefixWord ++ tailWord_4637578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637578).length < 2 ^ (prefixWord ++ tailWord_4637578).sum := by decide
  have hdescent : baseEnd_4637578 < baseStart_4637578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637588 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_4637588 : Nat := 118140960795 + 4637588 * 2 ^ 59
def prefixEnd_4637588 : Nat := 4983230072969 + 3 ^ 40 * 4637588 * 2
def baseEnd_4637588 : Nat := 793770573841102216440709

theorem tailTrace_4637588 : CollatzResearch.WordTrace tailWord_4637588 prefixEnd_4637588 793770573841102216440709 := by
  unfold tailWord_4637588
  simp only [CollatzResearch.WordTrace]
  refine ⟨84573365161409093909112709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112764486881878791878816945 84573365161409093909112709)
  ·
    refine ⟨15857505967764205107958633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84573365161409093909112709 15857505967764205107958633)
    ·
      refine ⟨11893129475823153830968975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15857505967764205107958633 11893129475823153830968975)
      ·
        refine ⟨17839694213734730746453463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11893129475823153830968975 17839694213734730746453463)
        ·
          refine ⟨26759541320602096119680195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17839694213734730746453463 26759541320602096119680195)
          ·
            refine ⟨40139311980903144179520293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26759541320602096119680195 40139311980903144179520293)
            ·
              refine ⟨7526120996419339533660055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40139311980903144179520293 7526120996419339533660055)
              ·
                refine ⟨11289181494629009300490083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7526120996419339533660055 11289181494629009300490083)
                ·
                  refine ⟨16933772241943513950735125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11289181494629009300490083 16933772241943513950735125)
                  ·
                    refine ⟨793770573841102216440709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16933772241943513950735125 793770573841102216440709)
                    ·
                      rfl

theorem cell23_4637588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_4637588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637588 prefixEnd_4637588 := by exact prefixLift 4637588
  have htrace : WordTrace (prefixWord ++ tailWord_4637588) baseStart_4637588 baseEnd_4637588 := by
    simpa [prefixWord, tailWord_4637588, baseEnd_4637588] using wordTrace_append hprefix tailTrace_4637588
  have hstable : (prefixWord ++ tailWord_4637588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637588).length < 2 ^ (prefixWord ++ tailWord_4637588).sum := by decide
  have hdescent : baseEnd_4637588 < baseStart_4637588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637721 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 1, 7]
def baseStart_4637721 : Nat := 118140960795 + 4637721 * 2 ^ 59
def prefixEnd_4637721 : Nat := 4983230072969 + 3 ^ 40 * 4637721 * 2
def baseEnd_4637721 : Nat := 793793338150118209653005

theorem tailTrace_4637721 : CollatzResearch.WordTrace tailWord_4637721 prefixEnd_4637721 793793338150118209653005 := by
  unfold tailWord_4637721
  simp only [CollatzResearch.WordTrace]
  refine ⟨169151581231336351532817017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112767720820890901021878011 169151581231336351532817017)
  ·
    refine ⟨126863685923502263649612763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169151581231336351532817017 126863685923502263649612763)
    ·
      refine ⟨190295528885253395474419145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126863685923502263649612763 190295528885253395474419145)
      ·
        refine ⟨142721646663940046605814359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190295528885253395474419145 142721646663940046605814359)
        ·
          refine ⟨214082469995910069908721539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142721646663940046605814359 214082469995910069908721539)
          ·
            refine ⟨321123704993865104863082309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214082469995910069908721539 321123704993865104863082309)
            ·
              refine ⟨60210694686349707161827933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 321123704993865104863082309 60210694686349707161827933)
              ·
                refine ⟨22579010507381140185685475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60210694686349707161827933 22579010507381140185685475)
                ·
                  refine ⟨33868515761071710278528213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22579010507381140185685475 33868515761071710278528213)
                  ·
                    refine ⟨793793338150118209653005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33868515761071710278528213 793793338150118209653005)
                    ·
                      rfl

theorem cell23_4637721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_4637721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637721 prefixEnd_4637721 := by exact prefixLift 4637721
  have htrace : WordTrace (prefixWord ++ tailWord_4637721) baseStart_4637721 baseEnd_4637721 := by
    simpa [prefixWord, tailWord_4637721, baseEnd_4637721] using wordTrace_append hprefix tailTrace_4637721
  have hstable : (prefixWord ++ tailWord_4637721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637721).length < 2 ^ (prefixWord ++ tailWord_4637721).sum := by decide
  have hdescent : baseEnd_4637721 < baseStart_4637721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637751 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 2, 8]
def baseStart_4637751 : Nat := 118140960795 + 4637751 * 2 ^ 59
def prefixEnd_4637751 : Nat := 4983230072969 + 3 ^ 40 * 4637751 * 2
def baseEnd_4637751 : Nat := 793798472956663170527959

theorem tailTrace_4637751 : CollatzResearch.WordTrace tailWord_4637751 prefixEnd_4637751 793798472956663170527959 := by
  unfold tailWord_4637751
  simp only [CollatzResearch.WordTrace]
  refine ⟨169152675421227666656409107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112768450280818444437606071 169152675421227666656409107)
  ·
    refine ⟨253729013131841499984613661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169152675421227666656409107 253729013131841499984613661)
    ·
      refine ⟨95148379924440562494230123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253729013131841499984613661 95148379924440562494230123)
      ·
        refine ⟨142722569886660843741345185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95148379924440562494230123 142722569886660843741345185)
        ·
          refine ⟨107041927414995632806008889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142722569886660843741345185 107041927414995632806008889)
          ·
            refine ⟨80281445561246724604506667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107041927414995632806008889 80281445561246724604506667)
            ·
              refine ⟨120422168341870086906760001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80281445561246724604506667 120422168341870086906760001)
              ·
                refine ⟨90316626256402565180070001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120422168341870086906760001 90316626256402565180070001)
                ·
                  refine ⟨67737469692301923885052501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90316626256402565180070001 67737469692301923885052501)
                  ·
                    refine ⟨793798472956663170527959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67737469692301923885052501 793798472956663170527959)
                    ·
                      rfl

theorem cell23_4637751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_4637751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637751 prefixEnd_4637751 := by exact prefixLift 4637751
  have htrace : WordTrace (prefixWord ++ tailWord_4637751) baseStart_4637751 baseEnd_4637751 := by
    simpa [prefixWord, tailWord_4637751, baseEnd_4637751] using wordTrace_append hprefix tailTrace_4637751
  have hstable : (prefixWord ++ tailWord_4637751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637751).length < 2 ^ (prefixWord ++ tailWord_4637751).sum := by decide
  have hdescent : baseEnd_4637751 < baseStart_4637751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637771 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 6]
def baseStart_4637771 : Nat := 118140960795 + 4637771 * 2 ^ 59
def prefixEnd_4637771 : Nat := 4983230072969 + 3 ^ 40 * 4637771 * 2
def baseEnd_4637771 : Nat := 2381405688483079433333785

theorem tailTrace_4637771 : CollatzResearch.WordTrace tailWord_4637771 prefixEnd_4637771 2381405688483079433333785 := by
  unfold tailWord_4637771
  simp only [CollatzResearch.WordTrace]
  refine ⟨169153404881155210072137167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112768936587436806714758111 169153404881155210072137167)
  ·
    refine ⟨253730107321732815108205751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169153404881155210072137167 253730107321732815108205751)
    ·
      refine ⟨380595160982599222662308627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253730107321732815108205751 380595160982599222662308627)
      ·
        refine ⟨570892741473898833993462941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380595160982599222662308627 570892741473898833993462941)
        ·
          refine ⟨214084778052712062747548603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 570892741473898833993462941 214084778052712062747548603)
          ·
            refine ⟨321127167079068094121322905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214084778052712062747548603 321127167079068094121322905)
            ·
              refine ⟨240845375309301070590992179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321127167079068094121322905 240845375309301070590992179)
              ·
                refine ⟨361268062963951605886488269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240845375309301070590992179 361268062963951605886488269)
                ·
                  refine ⟨135475523611481852207433101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361268062963951605886488269 135475523611481852207433101)
                  ·
                    refine ⟨50803321354305694577787413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135475523611481852207433101 50803321354305694577787413)
                    ·
                      refine ⟨2381405688483079433333785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50803321354305694577787413 2381405688483079433333785)
                      ·
                        rfl

theorem cell23_4637771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_4637771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637771 prefixEnd_4637771 := by exact prefixLift 4637771
  have htrace : WordTrace (prefixWord ++ tailWord_4637771) baseStart_4637771 baseEnd_4637771 := by
    simpa [prefixWord, tailWord_4637771, baseEnd_4637771] using wordTrace_append hprefix tailTrace_4637771
  have hstable : (prefixWord ++ tailWord_4637771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637771).length < 2 ^ (prefixWord ++ tailWord_4637771).sum := by decide
  have hdescent : baseEnd_4637771 < baseStart_4637771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637788 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_4637788 : Nat := 118140960795 + 4637788 * 2 ^ 59
def prefixEnd_4637788 : Nat := 4983230072969 + 3 ^ 40 * 4637788 * 2
def baseEnd_4637788 : Nat := 2381414417654205866821207

theorem tailTrace_4637788 : CollatzResearch.WordTrace tailWord_4637788 prefixEnd_4637788 2381414417654205866821207 := by
  unfold tailWord_4637788
  simp only [CollatzResearch.WordTrace]
  refine ⟨84577012461046810987753009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112769349948062414650337345 84577012461046810987753009)
  ·
    refine ⟨63432759345785108240814757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84577012461046810987753009 63432759345785108240814757)
    ·
      refine ⟨11893642377334707795152767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63432759345785108240814757 11893642377334707795152767)
      ·
        refine ⟨17840463566002061692729151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11893642377334707795152767 17840463566002061692729151)
        ·
          refine ⟨26760695349003092539093727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17840463566002061692729151 26760695349003092539093727)
          ·
            refine ⟨40141043023504638808640591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26760695349003092539093727 40141043023504638808640591)
            ·
              refine ⟨60211564535256958212960887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40141043023504638808640591 60211564535256958212960887)
              ·
                refine ⟨90317346802885437319441331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60211564535256958212960887 90317346802885437319441331)
                ·
                  refine ⟨135476020204328155979161997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90317346802885437319441331 135476020204328155979161997)
                  ·
                    refine ⟨50803507576623058492185749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135476020204328155979161997 50803507576623058492185749)
                    ·
                      refine ⟨2381414417654205866821207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50803507576623058492185749 2381414417654205866821207)
                      ·
                        rfl

theorem cell23_4637788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_4637788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637788 prefixEnd_4637788 := by exact prefixLift 4637788
  have htrace : WordTrace (prefixWord ++ tailWord_4637788) baseStart_4637788 baseEnd_4637788 := by
    simpa [prefixWord, tailWord_4637788, baseEnd_4637788] using wordTrace_append hprefix tailTrace_4637788
  have hstable : (prefixWord ++ tailWord_4637788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637788).length < 2 ^ (prefixWord ++ tailWord_4637788).sum := by decide
  have hdescent : baseEnd_4637788 < baseStart_4637788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637802 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 3, 4]
def baseStart_4637802 : Nat := 118140960795 + 4637802 * 2 ^ 59
def prefixEnd_4637802 : Nat := 4983230072969 + 3 ^ 40 * 4637802 * 2
def baseEnd_4637802 : Nat := 793807202127789604015381

theorem tailTrace_4637802 : CollatzResearch.WordTrace tailWord_4637802 prefixEnd_4637802 793807202127789604015381 := by
  unfold tailWord_4637802
  simp only [CollatzResearch.WordTrace]
  refine ⟨42288633886010725591628915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112769690362695268244343773 42288633886010725591628915)
  ·
    refine ⟨63432950829016088387443373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42288633886010725591628915 63432950829016088387443373)
    ·
      refine ⟨23787356560881033145291265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63432950829016088387443373 23787356560881033145291265)
      ·
        refine ⟨17840517420660774858968449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23787356560881033145291265 17840517420660774858968449)
        ·
          refine ⟨13380388065495581144226337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17840517420660774858968449 13380388065495581144226337)
          ·
            refine ⟨10035291049121685858169753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13380388065495581144226337 10035291049121685858169753)
            ·
              refine ⟨7526468286841264393627315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10035291049121685858169753 7526468286841264393627315)
              ·
                refine ⟨11289702430261896590440973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7526468286841264393627315 11289702430261896590440973)
                ·
                  refine ⟨4233638411348211221415365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11289702430261896590440973 4233638411348211221415365)
                  ·
                    refine ⟨793807202127789604015381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4233638411348211221415365 793807202127789604015381)
                    ·
                      rfl

theorem cell23_4637802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_4637802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637802 prefixEnd_4637802 := by exact prefixLift 4637802
  have htrace : WordTrace (prefixWord ++ tailWord_4637802) baseStart_4637802 baseEnd_4637802 := by
    simpa [prefixWord, tailWord_4637802, baseEnd_4637802] using wordTrace_append hprefix tailTrace_4637802
  have hstable : (prefixWord ++ tailWord_4637802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637802).length < 2 ^ (prefixWord ++ tailWord_4637802).sum := by decide
  have hdescent : baseEnd_4637802 < baseStart_4637802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637815 : List Nat := [1, 1, 3, 1, 1, 4, 5, 1, 6]
def baseStart_4637815 : Nat := 118140960795 + 4637815 * 2 ^ 59
def prefixEnd_4637815 : Nat := 4983230072969 + 3 ^ 40 * 4637815 * 2
def baseEnd_4637815 : Nat := 264603142403541917909287

theorem tailTrace_4637815 : CollatzResearch.WordTrace tailWord_4637815 prefixEnd_4637815 264603142403541917909287 := by
  unfold tailWord_4637815
  simp only [CollatzResearch.WordTrace]
  refine ⟨169155009692995805586738899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112770006461997203724492599 169155009692995805586738899)
  ·
    refine ⟨253732514539493708380108349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169155009692995805586738899 253732514539493708380108349)
    ·
      refine ⟨95149692952310140642540631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253732514539493708380108349 95149692952310140642540631)
      ·
        refine ⟨142724539428465210963810947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95149692952310140642540631 142724539428465210963810947)
        ·
          refine ⟨214086809142697816445716421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142724539428465210963810947 214086809142697816445716421)
          ·
            refine ⟨40141276714255840583571829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214086809142697816445716421 40141276714255840583571829)
            ·
              refine ⟨3763244691961485054709859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40141276714255840583571829 3763244691961485054709859)
              ·
                refine ⟨5644867037942227582064789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3763244691961485054709859 5644867037942227582064789)
                ·
                  refine ⟨264603142403541917909287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5644867037942227582064789 264603142403541917909287)
                  ·
                    rfl

theorem cell23_4637815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 6].length) (baseStart_4637815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637815 prefixEnd_4637815 := by exact prefixLift 4637815
  have htrace : WordTrace (prefixWord ++ tailWord_4637815) baseStart_4637815 baseEnd_4637815 := by
    simpa [prefixWord, tailWord_4637815, baseEnd_4637815] using wordTrace_append hprefix tailTrace_4637815
  have hstable : (prefixWord ++ tailWord_4637815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637815).length < 2 ^ (prefixWord ++ tailWord_4637815).sum := by decide
  have hdescent : baseEnd_4637815 < baseStart_4637815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637835 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 6, 3, 2]
def baseStart_4637835 : Nat := 118140960795 + 4637835 * 2 ^ 59
def prefixEnd_4637835 : Nat := 4983230072969 + 3 ^ 40 * 4637835 * 2
def baseEnd_4637835 : Nat := 2381438551244967182933491

theorem tailTrace_4637835 : CollatzResearch.WordTrace tailWord_4637835 prefixEnd_4637835 2381438551244967182933491 := by
  unfold tailWord_4637835
  simp only [CollatzResearch.WordTrace]
  refine ⟨169155739152923349002466959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112770492768615566001644639 169155739152923349002466959)
  ·
    refine ⟨253733608729385023503700439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169155739152923349002466959 253733608729385023503700439)
    ·
      refine ⟨380600413094077535255550659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253733608729385023503700439 380600413094077535255550659)
      ·
        refine ⟨570900619641116302883325989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380600413094077535255550659 570900619641116302883325989)
        ·
          refine ⟨107043866182709306790623623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 570900619641116302883325989 107043866182709306790623623)
          ·
            refine ⟨160565799274063960185935435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107043866182709306790623623 160565799274063960185935435)
            ·
              refine ⟨240848698911095940278903153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160565799274063960185935435 240848698911095940278903153)
              ·
                refine ⟨180636524183321955209177365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240848698911095940278903153 180636524183321955209177365)
                ·
                  refine ⟨8467337071093216650430189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 180636524183321955209177365 8467337071093216650430189)
                  ·
                    refine ⟨3175251401659956243911321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8467337071093216650430189 3175251401659956243911321)
                    ·
                      refine ⟨2381438551244967182933491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3175251401659956243911321 2381438551244967182933491)
                      ·
                        rfl

theorem cell23_4637835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 3, 2].length) (baseStart_4637835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637835 prefixEnd_4637835 := by exact prefixLift 4637835
  have htrace : WordTrace (prefixWord ++ tailWord_4637835) baseStart_4637835 baseEnd_4637835 := by
    simpa [prefixWord, tailWord_4637835, baseEnd_4637835] using wordTrace_append hprefix tailTrace_4637835
  have hstable : (prefixWord ++ tailWord_4637835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637835).length < 2 ^ (prefixWord ++ tailWord_4637835).sum := by decide
  have hdescent : baseEnd_4637835 < baseStart_4637835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637852 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_4637852 : Nat := 118140960795 + 4637852 * 2 ^ 59
def prefixEnd_4637852 : Nat := 4983230072969 + 3 ^ 40 * 4637852 * 2
def baseEnd_4637852 : Nat := 2381447280416093616420913

theorem tailTrace_4637852 : CollatzResearch.WordTrace tailWord_4637852 prefixEnd_4637852 2381447280416093616420913 := by
  unfold tailWord_4637852
  simp only [CollatzResearch.WordTrace]
  refine ⟨84578179596930880452917905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112770906129241173937223873 84578179596930880452917905)
  ·
    refine ⟨63433634697698160339688429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84578179596930880452917905 63433634697698160339688429)
    ·
      refine ⟨23787613011636810127383161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63433634697698160339688429 23787613011636810127383161)
      ·
        refine ⟨17840709758727607595537371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23787613011636810127383161 17840709758727607595537371)
        ·
          refine ⟨26761064638091411393306057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17840709758727607595537371 26761064638091411393306057)
          ·
            refine ⟨20070798478568558544979543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26761064638091411393306057 20070798478568558544979543)
            ·
              refine ⟨30106197717852837817469315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20070798478568558544979543 30106197717852837817469315)
              ·
                refine ⟨45159296576779256726203973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30106197717852837817469315 45159296576779256726203973)
                ·
                  refine ⟨8467368108146110636163245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45159296576779256726203973 8467368108146110636163245)
                  ·
                    refine ⟨3175263040554791488561217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8467368108146110636163245 3175263040554791488561217)
                    ·
                      refine ⟨2381447280416093616420913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3175263040554791488561217 2381447280416093616420913)
                      ·
                        rfl

theorem cell23_4637852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_4637852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637852 prefixEnd_4637852 := by exact prefixLift 4637852
  have htrace : WordTrace (prefixWord ++ tailWord_4637852) baseStart_4637852 baseEnd_4637852 := by
    simpa [prefixWord, tailWord_4637852, baseEnd_4637852] using wordTrace_append hprefix tailTrace_4637852
  have hstable : (prefixWord ++ tailWord_4637852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637852).length < 2 ^ (prefixWord ++ tailWord_4637852).sum := by decide
  have hdescent : baseEnd_4637852 < baseStart_4637852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637868 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_4637868 : Nat := 118140960795 + 4637868 * 2 ^ 59
def prefixEnd_4637868 : Nat := 4983230072969 + 3 ^ 40 * 4637868 * 2
def baseEnd_4637868 : Nat := 2381455496106565553820839

theorem tailTrace_4637868 : CollatzResearch.WordTrace tailWord_4637868 prefixEnd_4637868 2381455496106565553820839 := by
  unfold tailWord_4637868
  simp only [CollatzResearch.WordTrace]
  refine ⟨84578471380901897819209129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112771295174535863758945505 84578471380901897819209129)
  ·
    refine ⟨63433853535676423364406847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84578471380901897819209129 63433853535676423364406847)
    ·
      refine ⟨95150780303514635046610271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63433853535676423364406847 95150780303514635046610271)
      ·
        refine ⟨142726170455271952569915407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95150780303514635046610271 142726170455271952569915407)
        ·
          refine ⟨214089255682907928854873111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142726170455271952569915407 214089255682907928854873111)
          ·
            refine ⟨321133883524361893282309667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214089255682907928854873111 321133883524361893282309667)
            ·
              refine ⟨481700825286542839923464501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321133883524361893282309667 481700825286542839923464501)
              ·
                refine ⟨45159452370613391242824797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 481700825286542839923464501 45159452370613391242824797)
                ·
                  refine ⟨16934794638980021716059299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45159452370613391242824797 16934794638980021716059299)
                  ·
                    refine ⟨25402191958470032574088949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16934794638980021716059299 25402191958470032574088949)
                    ·
                      refine ⟨2381455496106565553820839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25402191958470032574088949 2381455496106565553820839)
                      ·
                        rfl

theorem cell23_4637868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_4637868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637868 prefixEnd_4637868 := by exact prefixLift 4637868
  have htrace : WordTrace (prefixWord ++ tailWord_4637868) baseStart_4637868 baseEnd_4637868 := by
    simpa [prefixWord, tailWord_4637868, baseEnd_4637868] using wordTrace_append hprefix tailTrace_4637868
  have hstable : (prefixWord ++ tailWord_4637868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637868).length < 2 ^ (prefixWord ++ tailWord_4637868).sum := by decide
  have hdescent : baseEnd_4637868 < baseStart_4637868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637882 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2]
def baseStart_4637882 : Nat := 118140960795 + 4637882 * 2 ^ 59
def prefixEnd_4637882 : Nat := 4983230072969 + 3 ^ 40 * 4637882 * 2
def baseEnd_4637882 : Nat := 2381462684835728499045775

theorem tailTrace_4637882 : CollatzResearch.WordTrace tailWord_4637882 prefixEnd_4637882 2381462684835728499045775 := by
  unfold tailWord_4637882
  simp only [CollatzResearch.WordTrace]
  refine ⟨42289363345938269007356975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112771635589168717352951933 42289363345938269007356975)
  ·
    refine ⟨63434045018907403511035463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42289363345938269007356975 63434045018907403511035463)
    ·
      refine ⟨95151067528361105266553195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63434045018907403511035463 95151067528361105266553195)
      ·
        refine ⟨142726601292541657899829793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95151067528361105266553195 142726601292541657899829793)
        ·
          refine ⟨107044950969406243424872345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142726601292541657899829793 107044950969406243424872345)
          ·
            refine ⟨80283713227054682568654259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107044950969406243424872345 80283713227054682568654259)
            ·
              refine ⟨120425569840582023852981389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80283713227054682568654259 120425569840582023852981389)
              ·
                refine ⟨45159588690218258944868021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120425569840582023852981389 45159588690218258944868021)
                ·
                  refine ⟨4233711439707961776081377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45159588690218258944868021 4233711439707961776081377)
                  ·
                    refine ⟨3175283579780971332061033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4233711439707961776081377 3175283579780971332061033)
                    ·
                      refine ⟨2381462684835728499045775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3175283579780971332061033 2381462684835728499045775)
                      ·
                        rfl

theorem cell23_4637882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2].length) (baseStart_4637882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637882 prefixEnd_4637882 := by exact prefixLift 4637882
  have htrace : WordTrace (prefixWord ++ tailWord_4637882) baseStart_4637882 baseEnd_4637882 := by
    simpa [prefixWord, tailWord_4637882, baseEnd_4637882] using wordTrace_append hprefix tailTrace_4637882
  have hstable : (prefixWord ++ tailWord_4637882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637882).length < 2 ^ (prefixWord ++ tailWord_4637882).sum := by decide
  have hdescent : baseEnd_4637882 < baseStart_4637882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637892 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_4637892 : Nat := 118140960795 + 4637892 * 2 ^ 59
def prefixEnd_4637892 : Nat := 4983230072969 + 3 ^ 40 * 4637892 * 2
def baseEnd_4637892 : Nat := 793822606547424486640243

theorem tailTrace_4637892 : CollatzResearch.WordTrace tailWord_4637892 prefixEnd_4637892 793822606547424486640243 := by
  unfold tailWord_4637892
  simp only [CollatzResearch.WordTrace]
  refine ⟨84578909056858423868645965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112771878742477898491527953 84578909056858423868645965)
  ·
    refine ⟨31717090896321908950742237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84578909056858423868645965 31717090896321908950742237)
    ·
      refine ⟨11893909086120715856528339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31717090896321908950742237 11893909086120715856528339)
      ·
        refine ⟨17840863629181073784792509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11893909086120715856528339 17840863629181073784792509)
        ·
          refine ⟨6690323860942902669297191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17840863629181073784792509 6690323860942902669297191)
          ·
            refine ⟨10035485791414354003945787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6690323860942902669297191 10035485791414354003945787)
            ·
              refine ⟨15053228687121531005918681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10035485791414354003945787 15053228687121531005918681)
              ·
                refine ⟨11289921515341148254439011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15053228687121531005918681 11289921515341148254439011)
                ·
                  refine ⟨16934882273011722381658517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11289921515341148254439011 16934882273011722381658517)
                  ·
                    refine ⟨793822606547424486640243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16934882273011722381658517 793822606547424486640243)
                    ·
                      rfl

theorem cell23_4637892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_4637892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637892 prefixEnd_4637892 := by exact prefixLift 4637892
  have htrace : WordTrace (prefixWord ++ tailWord_4637892) baseStart_4637892 baseEnd_4637892 := by
    simpa [prefixWord, tailWord_4637892, baseEnd_4637892] using wordTrace_append hprefix tailTrace_4637892
  have hstable : (prefixWord ++ tailWord_4637892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637892).length < 2 ^ (prefixWord ++ tailWord_4637892).sum := by decide
  have hdescent : baseEnd_4637892 < baseStart_4637892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637909 : List Nat := [1, 3, 2, 4, 1, 2, 2, 2, 2, 4]
def baseStart_4637909 : Nat := 118140960795 + 4637909 * 2 ^ 59
def prefixEnd_4637909 : Nat := 4983230072969 + 3 ^ 40 * 4637909 * 2
def baseEnd_4637909 : Nat := 793825516271133297802717

theorem tailTrace_4637909 : CollatzResearch.WordTrace tailWord_4637909 prefixEnd_4637909 793825516271133297802717 := by
  unfold tailWord_4637909
  simp only [CollatzResearch.WordTrace]
  refine ⟨169158438154655259640660781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112772292103103506427107187 169158438154655259640660781)
  ·
    refine ⟨63434414307995722365247793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169158438154655259640660781 63434414307995722365247793)
    ·
      refine ⟨47575810730996791773935845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63434414307995722365247793 47575810730996791773935845)
      ·
        refine ⟨8920464512061898457612971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47575810730996791773935845 8920464512061898457612971)
        ·
          refine ⟨13380696768092847686419457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8920464512061898457612971 13380696768092847686419457)
          ·
            refine ⟨10035522576069635764814593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13380696768092847686419457 10035522576069635764814593)
            ·
              refine ⟨7526641932052226823610945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10035522576069635764814593 7526641932052226823610945)
              ·
                refine ⟨5644981449039170117708209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7526641932052226823610945 5644981449039170117708209)
                ·
                  refine ⟨4233736086779377588281157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5644981449039170117708209 4233736086779377588281157)
                  ·
                    refine ⟨793825516271133297802717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4233736086779377588281157 793825516271133297802717)
                    ·
                      rfl

theorem cell23_4637909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_4637909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637909 prefixEnd_4637909 := by exact prefixLift 4637909
  have htrace : WordTrace (prefixWord ++ tailWord_4637909) baseStart_4637909 baseEnd_4637909 := by
    simpa [prefixWord, tailWord_4637909, baseEnd_4637909] using wordTrace_append hprefix tailTrace_4637909
  have hstable : (prefixWord ++ tailWord_4637909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637909).length < 2 ^ (prefixWord ++ tailWord_4637909).sum := by decide
  have hdescent : baseEnd_4637909 < baseStart_4637909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637932 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 3]
def baseStart_4637932 : Nat := 118140960795 + 4637932 * 2 ^ 59
def prefixEnd_4637932 : Nat := 4983230072969 + 3 ^ 40 * 4637932 * 2
def baseEnd_4637932 : Nat := 2381488358868453303420545

theorem tailTrace_4637932 : CollatzResearch.WordTrace tailWord_4637932 prefixEnd_4637932 2381488358868453303420545 := by
  unfold tailWord_4637932
  simp only [CollatzResearch.WordTrace]
  refine ⟨84579638516785967284374025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112772851355714623045832033 84579638516785967284374025)
  ·
    refine ⟨63434728887589475463280519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84579638516785967284374025 63434728887589475463280519)
    ·
      refine ⟨95152093331384213194920779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63434728887589475463280519 95152093331384213194920779)
      ·
        refine ⟨142728139997076319792381169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95152093331384213194920779 142728139997076319792381169)
        ·
          refine ⟨107046104997807239844285877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142728139997076319792381169 107046104997807239844285877)
          ·
            refine ⟨10035572343544428735401801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107046104997807239844285877 10035572343544428735401801)
            ·
              refine ⟨7526679257658321551551351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10035572343544428735401801 7526679257658321551551351)
              ·
                refine ⟨11290018886487482327327027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7526679257658321551551351 11290018886487482327327027)
                ·
                  refine ⟨16935028329731223490990541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11290018886487482327327027 16935028329731223490990541)
                  ·
                    refine ⟨6350635623649208809121453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16935028329731223490990541 6350635623649208809121453)
                    ·
                      refine ⟨2381488358868453303420545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6350635623649208809121453 2381488358868453303420545)
                      ·
                        rfl

theorem cell23_4637932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_4637932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637932 prefixEnd_4637932 := by exact prefixLift 4637932
  have htrace : WordTrace (prefixWord ++ tailWord_4637932) baseStart_4637932 baseEnd_4637932 := by
    simpa [prefixWord, tailWord_4637932, baseEnd_4637932] using wordTrace_append hprefix tailTrace_4637932
  have hstable : (prefixWord ++ tailWord_4637932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637932).length < 2 ^ (prefixWord ++ tailWord_4637932).sum := by decide
  have hdescent : baseEnd_4637932 < baseStart_4637932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637966 : List Nat := [4, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_4637966 : Nat := 118140960795 + 4637966 * 2 ^ 59
def prefixEnd_4637966 : Nat := 4983230072969 + 3 ^ 40 * 4637966 * 2
def baseEnd_4637966 : Nat := 2381505817210706170395389

theorem tailTrace_4637966 : CollatzResearch.WordTrace tailWord_4637966 prefixEnd_4637966 2381505817210706170395389 := by
  unfold tailWord_4637966
  simp only [CollatzResearch.WordTrace]
  refine ⟨21145064639431094796935719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112773678076965838916990501 21145064639431094796935719)
  ·
    refine ⟨31717596959146642195403579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21145064639431094796935719 31717596959146642195403579)
    ·
      refine ⟨47576395438719963293105369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31717596959146642195403579 47576395438719963293105369)
      ·
        refine ⟨35682296579039972469829027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47576395438719963293105369 35682296579039972469829027)
        ·
          refine ⟨53523444868559958704743541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35682296579039972469829027 53523444868559958704743541)
          ·
            refine ⟨5017822956427496128569707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53523444868559958704743541 5017822956427496128569707)
            ·
              refine ⟨7526734434641244192854561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5017822956427496128569707 7526734434641244192854561)
              ·
                refine ⟨5645050825980933144640921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7526734434641244192854561 5645050825980933144640921)
                ·
                  refine ⟨4233788119485699858480691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5645050825980933144640921 4233788119485699858480691)
                  ·
                    refine ⟨6350682179228549787721037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4233788119485699858480691 6350682179228549787721037)
                    ·
                      refine ⟨2381505817210706170395389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6350682179228549787721037 2381505817210706170395389)
                      ·
                        rfl

theorem cell23_4637966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_4637966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637966 prefixEnd_4637966 := by exact prefixLift 4637966
  have htrace : WordTrace (prefixWord ++ tailWord_4637966) baseStart_4637966 baseEnd_4637966 := by
    simpa [prefixWord, tailWord_4637966, baseEnd_4637966] using wordTrace_append hprefix tailTrace_4637966
  have hstable : (prefixWord ++ tailWord_4637966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637966).length < 2 ^ (prefixWord ++ tailWord_4637966).sum := by decide
  have hdescent : baseEnd_4637966 < baseStart_4637966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637989 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 1, 4, 2]
def baseStart_4637989 : Nat := 118140960795 + 4637989 * 2 ^ 59
def prefixEnd_4637989 : Nat := 4983230072969 + 3 ^ 40 * 4637989 * 2
def baseEnd_4637989 : Nat := 2381517627265759580407783

theorem tailTrace_4637989 : CollatzResearch.WordTrace tailWord_4637989 prefixEnd_4637989 2381517627265759580407783 := by
  unfold tailWord_4637989
  simp only [CollatzResearch.WordTrace]
  refine ⟨169161355994365433303573021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112774237329576955535715347 169161355994365433303573021)
  ·
    refine ⟨63435508497887037488839883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169161355994365433303573021 63435508497887037488839883)
    ·
      refine ⟨95153262746830556233259825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63435508497887037488839883 95153262746830556233259825)
      ·
        refine ⟨71364947060122917174944869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95153262746830556233259825 71364947060122917174944869)
        ·
          refine ⟨13380927573773046970302163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71364947060122917174944869 13380927573773046970302163)
          ·
            refine ⟨20071391360659570455453245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13380927573773046970302163 20071391360659570455453245)
            ·
              refine ⟨7526771760247338920794967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20071391360659570455453245 7526771760247338920794967)
              ·
                refine ⟨11290157640371008381192451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7526771760247338920794967 11290157640371008381192451)
                ·
                  refine ⟨16935236460556512571788677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11290157640371008381192451 16935236460556512571788677)
                  ·
                    refine ⟨3175356836354346107210377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16935236460556512571788677 3175356836354346107210377)
                    ·
                      refine ⟨2381517627265759580407783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3175356836354346107210377 2381517627265759580407783)
                      ·
                        rfl

theorem cell23_4637989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_4637989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4637989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4637989 prefixEnd_4637989 := by exact prefixLift 4637989
  have htrace : WordTrace (prefixWord ++ tailWord_4637989) baseStart_4637989 baseEnd_4637989 := by
    simpa [prefixWord, tailWord_4637989, baseEnd_4637989] using wordTrace_append hprefix tailTrace_4637989
  have hstable : (prefixWord ++ tailWord_4637989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637989).length < 2 ^ (prefixWord ++ tailWord_4637989).sum := by decide
  have hdescent : baseEnd_4637989 < baseStart_4637989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638025 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 4, 5]
def baseStart_4638025 : Nat := 118140960795 + 4638025 * 2 ^ 59
def prefixEnd_4638025 : Nat := 4983230072969 + 3 ^ 40 * 4638025 * 2
def baseEnd_4638025 : Nat := 793845370856440479852539

theorem tailTrace_4638025 : CollatzResearch.WordTrace tailWord_4638025 prefixEnd_4638025 793845370856440479852539 := by
  unfold tailWord_4638025
  simp only [CollatzResearch.WordTrace]
  refine ⟨169162669022235011451883529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112775112681490007634589019 169162669022235011451883529)
  ·
    refine ⟨126872001766676258588912647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169162669022235011451883529 126872001766676258588912647)
    ·
      refine ⟨190308002650014387883368971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126872001766676258588912647 190308002650014387883368971)
      ·
        refine ⟨285462003975021581825053457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190308002650014387883368971 285462003975021581825053457)
        ·
          refine ⟨214096502981266186368790093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285462003975021581825053457 214096502981266186368790093)
          ·
            refine ⟨80286188617974819888296285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214096502981266186368790093 80286188617974819888296285)
            ·
              refine ⟨30107320731740557458111107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80286188617974819888296285 30107320731740557458111107)
              ·
                refine ⟨45160981097610836187166661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30107320731740557458111107 45160981097610836187166661)
                ·
                  refine ⟨8467683955802031785093749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45160981097610836187166661 8467683955802031785093749)
                  ·
                    refine ⟨793845370856440479852539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8467683955802031785093749 793845370856440479852539)
                    ·
                      rfl

theorem cell23_4638025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 5].length) (baseStart_4638025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638025 prefixEnd_4638025 := by exact prefixLift 4638025
  have htrace : WordTrace (prefixWord ++ tailWord_4638025) baseStart_4638025 baseEnd_4638025 := by
    simpa [prefixWord, tailWord_4638025, baseEnd_4638025] using wordTrace_append hprefix tailTrace_4638025
  have hstable : (prefixWord ++ tailWord_4638025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638025).length < 2 ^ (prefixWord ++ tailWord_4638025).sum := by decide
  have hdescent : baseEnd_4638025 < baseStart_4638025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638032 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 2, 5, 2]
def baseStart_4638032 : Nat := 118140960795 + 4638032 * 2 ^ 59
def prefixEnd_4638032 : Nat := 4983230072969 + 3 ^ 40 * 4638032 * 2
def baseEnd_4638032 : Nat := 2381539706933902912170085

theorem tailTrace_4638032 : CollatzResearch.WordTrace tailWord_4638032 prefixEnd_4638032 2381539706933902912170085 := by
  unfold tailWord_4638032
  simp only [CollatzResearch.WordTrace]
  refine ⟨84581462166604825823694175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112775282888806434431592233 84581462166604825823694175)
  ·
    refine ⟨126872193249907238735541263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84581462166604825823694175 126872193249907238735541263)
    ·
      refine ⟨190308289874860858103311895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126872193249907238735541263 190308289874860858103311895)
      ·
        refine ⟨285462434812291287154967843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190308289874860858103311895 285462434812291287154967843)
        ·
          refine ⟨428193652218436930732451765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285462434812291287154967843 428193652218436930732451765)
          ·
            refine ⟨40143154895478462256167353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 428193652218436930732451765 40143154895478462256167353)
            ·
              refine ⟨30107366171608846692125515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40143154895478462256167353 30107366171608846692125515)
              ·
                refine ⟨45161049257413270038188273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30107366171608846692125515 45161049257413270038188273)
                ·
                  refine ⟨33870786943059952528641205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45161049257413270038188273 33870786943059952528641205)
                  ·
                    refine ⟨3175386275911870549560113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33870786943059952528641205 3175386275911870549560113)
                    ·
                      refine ⟨2381539706933902912170085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3175386275911870549560113 2381539706933902912170085)
                      ·
                        rfl

theorem cell23_4638032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 5, 2].length) (baseStart_4638032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638032 prefixEnd_4638032 := by exact prefixLift 4638032
  have htrace : WordTrace (prefixWord ++ tailWord_4638032) baseStart_4638032 baseEnd_4638032 := by
    simpa [prefixWord, tailWord_4638032, baseEnd_4638032] using wordTrace_append hprefix tailTrace_4638032
  have hstable : (prefixWord ++ tailWord_4638032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638032).length < 2 ^ (prefixWord ++ tailWord_4638032).sum := by decide
  have hdescent : baseEnd_4638032 < baseStart_4638032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638035 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 5]
def baseStart_4638035 : Nat := 118140960795 + 4638035 * 2 ^ 59
def prefixEnd_4638035 : Nat := 4983230072969 + 3 ^ 40 * 4638035 * 2
def baseEnd_4638035 : Nat := 2381541247375866400432571

theorem tailTrace_4638035 : CollatzResearch.WordTrace tailWord_4638035 prefixEnd_4638035 2381541247375866400432571 := by
  unfold tailWord_4638035
  simp only [CollatzResearch.WordTrace]
  refine ⟨169163033752198783159747559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112775355834799188773165039 169163033752198783159747559)
  ·
    refine ⟨253744550628298174739621339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169163033752198783159747559 253744550628298174739621339)
    ·
      refine ⟨380616825942447262109432009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253744550628298174739621339 380616825942447262109432009)
      ·
        refine ⟨285462619456835446582074007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380616825942447262109432009 285462619456835446582074007)
        ·
          refine ⟨428193929185253169873111011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285462619456835446582074007 428193929185253169873111011)
          ·
            refine ⟨642290893777879754809666517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428193929185253169873111011 642290893777879754809666517)
            ·
              refine ⟨15053692822919056753351559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 642290893777879754809666517 15053692822919056753351559)
              ·
                refine ⟨22580539234378585130027339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15053692822919056753351559 22580539234378585130027339)
                ·
                  refine ⟨33870808851567877695041009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22580539234378585130027339 33870808851567877695041009)
                  ·
                    refine ⟨25403106638675908271280757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33870808851567877695041009 25403106638675908271280757)
                    ·
                      refine ⟨2381541247375866400432571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25403106638675908271280757 2381541247375866400432571)
                      ·
                        rfl

theorem cell23_4638035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_4638035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638035 prefixEnd_4638035 := by exact prefixLift 4638035
  have htrace : WordTrace (prefixWord ++ tailWord_4638035) baseStart_4638035 baseEnd_4638035 := by
    simpa [prefixWord, tailWord_4638035, baseEnd_4638035] using wordTrace_append hprefix tailTrace_4638035
  have hstable : (prefixWord ++ tailWord_4638035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638035).length < 2 ^ (prefixWord ++ tailWord_4638035).sum := by decide
  have hdescent : baseEnd_4638035 < baseStart_4638035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638075 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 6]
def baseStart_4638075 : Nat := 118140960795 + 4638075 * 2 ^ 59
def prefixEnd_4638075 : Nat := 4983230072969 + 3 ^ 40 * 4638075 * 2
def baseEnd_4638075 : Nat := 2381561786602046243932387

theorem tailTrace_4638075 : CollatzResearch.WordTrace tailWord_4638075 prefixEnd_4638075 2381561786602046243932387 := by
  unfold tailWord_4638075
  simp only [CollatzResearch.WordTrace]
  refine ⟨169164492672053869991203679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112776328448035913327469119 169164492672053869991203679)
  ·
    refine ⟨253746739008080804986805519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169164492672053869991203679 253746739008080804986805519)
    ·
      refine ⟨380620108512121207480208279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253746739008080804986805519 380620108512121207480208279)
      ·
        refine ⟨570930162768181811220312419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380620108512121207480208279 570930162768181811220312419)
        ·
          refine ⟨856395244152272716830468629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570930162768181811220312419 856395244152272716830468629)
          ·
            refine ⟨40143527069637783601428217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 856395244152272716830468629 40143527069637783601428217)
            ·
              refine ⟨30107645302228337701071163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40143527069637783601428217 30107645302228337701071163)
              ·
                refine ⟨45161467953342506551606745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30107645302228337701071163 45161467953342506551606745)
                ·
                  refine ⟨33871100965006879913705059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45161467953342506551606745 33871100965006879913705059)
                  ·
                    refine ⟨50806651447510319870557589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33871100965006879913705059 50806651447510319870557589)
                    ·
                      refine ⟨2381561786602046243932387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50806651447510319870557589 2381561786602046243932387)
                      ·
                        rfl

theorem cell23_4638075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 6].length) (baseStart_4638075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638075 prefixEnd_4638075 := by exact prefixLift 4638075
  have htrace : WordTrace (prefixWord ++ tailWord_4638075) baseStart_4638075 baseEnd_4638075 := by
    simpa [prefixWord, tailWord_4638075, baseEnd_4638075] using wordTrace_append hprefix tailTrace_4638075
  have hstable : (prefixWord ++ tailWord_4638075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638075).length < 2 ^ (prefixWord ++ tailWord_4638075).sum := by decide
  have hdescent : baseEnd_4638075 < baseStart_4638075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638085 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 8]
def baseStart_4638085 : Nat := 118140960795 + 4638085 * 2 ^ 59
def prefixEnd_4638085 : Nat := 4983230072969 + 3 ^ 40 * 4638085 * 2
def baseEnd_4638085 : Nat := 264618546823176800534149

theorem tailTrace_4638085 : CollatzResearch.WordTrace tailWord_4638085 prefixEnd_4638085 264618546823176800534149 := by
  unfold tailWord_4638085
  simp only [CollatzResearch.WordTrace]
  refine ⟨169164857402017641699067709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112776571601345094466045139 169164857402017641699067709)
  ·
    refine ⟨63436821525756615637150391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169164857402017641699067709 63436821525756615637150391)
    ·
      refine ⟨95155232288634923455725587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63436821525756615637150391 95155232288634923455725587)
      ·
        refine ⟨142732848432952385183588381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95155232288634923455725587 142732848432952385183588381)
        ·
          refine ⟨53524818162357144443845643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142732848432952385183588381 53524818162357144443845643)
          ·
            refine ⟨80287227243535716665768465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53524818162357144443845643 80287227243535716665768465)
            ·
              refine ⟨60215420432651787499326349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80287227243535716665768465 60215420432651787499326349)
              ·
                refine ⟨22580782662244420312247381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60215420432651787499326349 22580782662244420312247381)
                ·
                  refine ⟨264618546823176800534149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22580782662244420312247381 264618546823176800534149)
                  ·
                    rfl

theorem cell23_4638085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_4638085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638085 prefixEnd_4638085 := by exact prefixLift 4638085
  have htrace : WordTrace (prefixWord ++ tailWord_4638085) baseStart_4638085 baseEnd_4638085 := by
    simpa [prefixWord, tailWord_4638085, baseEnd_4638085] using wordTrace_append hprefix tailTrace_4638085
  have hstable : (prefixWord ++ tailWord_4638085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638085).length < 2 ^ (prefixWord ++ tailWord_4638085).sum := by decide
  have hdescent : baseEnd_4638085 < baseStart_4638085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638129 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 5, 1, 3]
def baseStart_4638129 : Nat := 118140960795 + 4638129 * 2 ^ 59
def prefixEnd_4638129 : Nat := 4983230072969 + 3 ^ 40 * 4638129 * 2
def baseEnd_4638129 : Nat := 2381589514557389032657139

theorem tailTrace_4638129 : CollatzResearch.WordTrace tailWord_4638129 prefixEnd_4638129 2381589514557389032657139 := by
  unfold tailWord_4638129
  simp only [CollatzResearch.WordTrace]
  refine ⟨169166462213858237213669441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112777641475905491475779627 169166462213858237213669441)
  ·
    refine ⟨126874846660393677910252081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169166462213858237213669441 126874846660393677910252081)
    ·
      refine ⟨95156134995295258432689061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126874846660393677910252081 95156134995295258432689061)
      ·
        refine ⟨17841775311617860956129199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95156134995295258432689061 17841775311617860956129199)
        ·
          refine ⟨26762662967426791434193799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17841775311617860956129199 26762662967426791434193799)
          ·
            refine ⟨40143994451140187151290699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26762662967426791434193799 40143994451140187151290699)
            ·
              refine ⟨60215991676710280726936049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40143994451140187151290699 60215991676710280726936049)
              ·
                refine ⟨45161993757532710545202037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60215991676710280726936049 45161993757532710545202037)
                ·
                  refine ⟨4233936914768691613612691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45161993757532710545202037 4233936914768691613612691)
                  ·
                    refine ⟨6350905372153037420419037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4233936914768691613612691 6350905372153037420419037)
                    ·
                      refine ⟨2381589514557389032657139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6350905372153037420419037 2381589514557389032657139)
                      ·
                        rfl

theorem cell23_4638129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_4638129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638129 prefixEnd_4638129 := by exact prefixLift 4638129
  have htrace : WordTrace (prefixWord ++ tailWord_4638129) baseStart_4638129 baseEnd_4638129 := by
    simpa [prefixWord, tailWord_4638129, baseEnd_4638129] using wordTrace_append hprefix tailTrace_4638129
  have hstable : (prefixWord ++ tailWord_4638129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638129).length < 2 ^ (prefixWord ++ tailWord_4638129).sum := by decide
  have hdescent : baseEnd_4638129 < baseStart_4638129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638166 : List Nat := [5, 2, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_4638166 : Nat := 118140960795 + 4638166 * 2 ^ 59
def prefixEnd_4638166 : Nat := 4983230072969 + 3 ^ 40 * 4638166 * 2
def baseEnd_4638166 : Nat := 793869504447201795964823

theorem tailTrace_4638166 : CollatzResearch.WordTrace tailWord_4638166 prefixEnd_4638166 793869504447201795964823 := by
  unfold tailWord_4638166
  simp only [CollatzResearch.WordTrace]
  refine ⟨10572988232170262033297897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112778541143149461688510901 10572988232170262033297897)
  ·
    refine ⟨7929741174127696524973423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10572988232170262033297897 7929741174127696524973423)
    ·
      refine ⟨11894611761191544787460135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7929741174127696524973423 11894611761191544787460135)
      ·
        refine ⟨17841917641787317181190203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11894611761191544787460135 17841917641787317181190203)
        ·
          refine ⟨26762876462680975771785305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17841917641787317181190203 26762876462680975771785305)
          ·
            refine ⟨20072157347010731828838979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26762876462680975771785305 20072157347010731828838979)
            ·
              refine ⟨30108236020516097743258469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20072157347010731828838979 30108236020516097743258469)
              ·
                refine ⟨5645294253846768326860963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30108236020516097743258469 5645294253846768326860963)
                ·
                  refine ⟨8467941380770152490291445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5645294253846768326860963 8467941380770152490291445)
                  ·
                    refine ⟨793869504447201795964823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8467941380770152490291445 793869504447201795964823)
                    ·
                      rfl

theorem cell23_4638166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_4638166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638166 prefixEnd_4638166 := by exact prefixLift 4638166
  have htrace : WordTrace (prefixWord ++ tailWord_4638166) baseStart_4638166 baseEnd_4638166 := by
    simpa [prefixWord, tailWord_4638166, baseEnd_4638166] using wordTrace_append hprefix tailTrace_4638166
  have hstable : (prefixWord ++ tailWord_4638166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638166).length < 2 ^ (prefixWord ++ tailWord_4638166).sum := by decide
  have hdescent : baseEnd_4638166 < baseStart_4638166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638169 : List Nat := [1, 2, 1, 2, 4, 2, 1, 4, 1, 1, 4]
def baseStart_4638169 : Nat := 118140960795 + 4638169 * 2 ^ 59
def prefixEnd_4638169 : Nat := 4983230072969 + 3 ^ 40 * 4638169 * 2
def baseEnd_4638169 : Nat := 2381610053783568876156955

theorem tailTrace_4638169 : CollatzResearch.WordTrace tailWord_4638169 prefixEnd_4638169 2381610053783568876156955 := by
  unfold tailWord_4638169
  simp only [CollatzResearch.WordTrace]
  refine ⟨169167921133713324045125561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112778614089142216030083707 169167921133713324045125561)
  ·
    refine ⟨126875940850284993033844171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169167921133713324045125561 126875940850284993033844171)
    ·
      refine ⟨190313911275427489550766257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126875940850284993033844171 190313911275427489550766257)
      ·
        refine ⟨142735433456570617163074693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190313911275427489550766257 142735433456570617163074693)
        ·
          refine ⟨26762893773106990718076505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142735433456570617163074693 26762893773106990718076505)
          ·
            refine ⟨20072170329830243038557379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26762893773106990718076505 20072170329830243038557379)
            ·
              refine ⟨30108255494745364557836069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20072170329830243038557379 30108255494745364557836069)
              ·
                refine ⟨5645297905264755854594263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30108255494745364557836069 5645297905264755854594263)
                ·
                  refine ⟨8467946857897133781891395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5645297905264755854594263 8467946857897133781891395)
                  ·
                    refine ⟨12701920286845700672837093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8467946857897133781891395 12701920286845700672837093)
                    ·
                      refine ⟨2381610053783568876156955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12701920286845700672837093 2381610053783568876156955)
                      ·
                        rfl

theorem cell23_4638169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_4638169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638169 prefixEnd_4638169 := by exact prefixLift 4638169
  have htrace : WordTrace (prefixWord ++ tailWord_4638169) baseStart_4638169 baseEnd_4638169 := by
    simpa [prefixWord, tailWord_4638169, baseEnd_4638169] using wordTrace_append hprefix tailTrace_4638169
  have hstable : (prefixWord ++ tailWord_4638169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638169).length < 2 ^ (prefixWord ++ tailWord_4638169).sum := by decide
  have hdescent : baseEnd_4638169 < baseStart_4638169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638179 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 4, 4]
def baseStart_4638179 : Nat := 118140960795 + 4638179 * 2 ^ 59
def prefixEnd_4638179 : Nat := 4983230072969 + 3 ^ 40 * 4638179 * 2
def baseEnd_4638179 : Nat := 793871729530037945677303

theorem tailTrace_4638179 : CollatzResearch.WordTrace tailWord_4638179 prefixEnd_4638179 793871729530037945677303 := by
  unfold tailWord_4638179
  simp only [CollatzResearch.WordTrace]
  refine ⟨169168285863677095752989591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112778857242451397168659727 169168285863677095752989591)
  ·
    refine ⟨253752428795515643629484387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169168285863677095752989591 253752428795515643629484387)
    ·
      refine ⟨380628643193273465444226581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253752428795515643629484387 380628643193273465444226581)
      ·
        refine ⟨17841967649684693692698121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 380628643193273465444226581 17841967649684693692698121)
        ·
          refine ⟨13381475737263520269523591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17841967649684693692698121 13381475737263520269523591)
          ·
            refine ⟨20072213605895280404285387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13381475737263520269523591 20072213605895280404285387)
            ·
              refine ⟨30108320408842920606428081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20072213605895280404285387 30108320408842920606428081)
              ·
                refine ⟨22581240306632190454821061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30108320408842920606428081 22581240306632190454821061)
                ·
                  refine ⟨4233982557493535710278949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22581240306632190454821061 4233982557493535710278949)
                  ·
                    refine ⟨793871729530037945677303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4233982557493535710278949 793871729530037945677303)
                    ·
                      rfl

theorem cell23_4638179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 4].length) (baseStart_4638179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638179 prefixEnd_4638179 := by exact prefixLift 4638179
  have htrace : WordTrace (prefixWord ++ tailWord_4638179) baseStart_4638179 baseEnd_4638179 := by
    simpa [prefixWord, tailWord_4638179, baseEnd_4638179] using wordTrace_append hprefix tailTrace_4638179
  have hstable : (prefixWord ++ tailWord_4638179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638179).length < 2 ^ (prefixWord ++ tailWord_4638179).sum := by decide
  have hdescent : baseEnd_4638179 < baseStart_4638179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638192 : List Nat := [2, 1, 1, 1, 3, 6, 9]
def baseStart_4638192 : Nat := 118140960795 + 4638192 * 2 ^ 59
def prefixEnd_4638192 : Nat := 4983230072969 + 3 ^ 40 * 4638192 * 2
def baseEnd_4638192 : Nat := 29402739059736077607029

theorem tailTrace_4638192 : CollatzResearch.WordTrace tailWord_4638192 prefixEnd_4638192 29402739059736077607029 := by
  unfold tailWord_4638192
  simp only [CollatzResearch.WordTrace]
  refine ⟨84584380006314999486606415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112779173341753332648808553 84584380006314999486606415)
  ·
    refine ⟨126876570009472499229909623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84584380006314999486606415 126876570009472499229909623)
    ·
      refine ⟨190314855014208748844864435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126876570009472499229909623 190314855014208748844864435)
      ·
        refine ⟨285472282521313123267296653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190314855014208748844864435 285472282521313123267296653)
        ·
          refine ⟨107052105945492421225236245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285472282521313123267296653 107052105945492421225236245)
          ·
            refine ⟨5018067466194957244932949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107052105945492421225236245 5018067466194957244932949)
            ·
              refine ⟨29402739059736077607029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5018067466194957244932949 29402739059736077607029)
              ·
                rfl

theorem cell23_4638192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 9].length) (baseStart_4638192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638192 prefixEnd_4638192 := by exact prefixLift 4638192
  have htrace : WordTrace (prefixWord ++ tailWord_4638192) baseStart_4638192 baseEnd_4638192 := by
    simpa [prefixWord, tailWord_4638192, baseEnd_4638192] using wordTrace_append hprefix tailTrace_4638192
  have hstable : (prefixWord ++ tailWord_4638192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638192).length < 2 ^ (prefixWord ++ tailWord_4638192).sum := by decide
  have hdescent : baseEnd_4638192 < baseStart_4638192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638197 : List Nat := [1, 3, 5, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_4638197 : Nat := 118140960795 + 4638197 * 2 ^ 59
def prefixEnd_4638197 : Nat := 4983230072969 + 3 ^ 40 * 4638197 * 2
def baseEnd_4638197 : Nat := 2381624431241894766606827

theorem tailTrace_4638197 : CollatzResearch.WordTrace tailWord_4638197 prefixEnd_4638197 2381624431241894766606827 := by
  unfold tailWord_4638197
  simp only [CollatzResearch.WordTrace]
  refine ⟨169168942377611884827144845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112779294918407923218096563 169168942377611884827144845)
  ·
    refine ⟨63438353391604456810179317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169168942377611884827144845 63438353391604456810179317)
    ·
      refine ⟨5947345630462917825954311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63438353391604456810179317 5947345630462917825954311)
      ·
        refine ⟨8921018445694376738931467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5947345630462917825954311 8921018445694376738931467)
        ·
          refine ⟨13381527668541565108397201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8921018445694376738931467 13381527668541565108397201)
          ·
            refine ⟨10036145751406173831297901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13381527668541565108397201 10036145751406173831297901)
            ·
              refine ⟨3763554656777315186736713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10036145751406173831297901 3763554656777315186736713)
              ·
                refine ⟨2822665992582986390052535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3763554656777315186736713 2822665992582986390052535)
                ·
                  refine ⟨4233998988874479585078803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2822665992582986390052535 4233998988874479585078803)
                  ·
                    refine ⟨6350998483311719377618205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4233998988874479585078803 6350998483311719377618205)
                    ·
                      refine ⟨2381624431241894766606827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6350998483311719377618205 2381624431241894766606827)
                      ·
                        rfl

theorem cell23_4638197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_4638197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638197 prefixEnd_4638197 := by exact prefixLift 4638197
  have htrace : WordTrace (prefixWord ++ tailWord_4638197) baseStart_4638197 baseEnd_4638197 := by
    simpa [prefixWord, tailWord_4638197, baseEnd_4638197] using wordTrace_append hprefix tailTrace_4638197
  have hstable : (prefixWord ++ tailWord_4638197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638197).length < 2 ^ (prefixWord ++ tailWord_4638197).sum := by decide
  have hdescent : baseEnd_4638197 < baseStart_4638197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638209 : List Nat := [1, 2, 4, 1, 4, 1, 2, 8]
def baseStart_4638209 : Nat := 118140960795 + 4638209 * 2 ^ 59
def prefixEnd_4638209 : Nat := 4983230072969 + 3 ^ 40 * 4638209 * 2
def baseEnd_4638209 : Nat := 88208540481842545172473

theorem tailTrace_4638209 : CollatzResearch.WordTrace tailWord_4638209 prefixEnd_4638209 88208540481842545172473 := by
  unfold tailWord_4638209
  simp only [CollatzResearch.WordTrace]
  refine ⟨169169380053568410876581681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112779586702378940584387787 169169380053568410876581681)
  ·
    refine ⟨126877035040176308157436261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169169380053568410876581681 126877035040176308157436261)
    ·
      refine ⟨23789444070033057779519299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126877035040176308157436261 23789444070033057779519299)
      ·
        refine ⟨35684166105049586669278949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23789444070033057779519299 35684166105049586669278949)
        ·
          refine ⟨6690781144696797500489803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35684166105049586669278949 6690781144696797500489803)
          ·
            refine ⟨10036171717045196250734705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6690781144696797500489803 10036171717045196250734705)
            ·
              refine ⟨7527128787783897188051029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10036171717045196250734705 7527128787783897188051029)
              ·
                refine ⟨88208540481842545172473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7527128787783897188051029 88208540481842545172473)
                ·
                  rfl

theorem cell23_4638209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 8].length) (baseStart_4638209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638209 prefixEnd_4638209 := by exact prefixLift 4638209
  have htrace : WordTrace (prefixWord ++ tailWord_4638209) baseStart_4638209 baseEnd_4638209 := by
    simpa [prefixWord, tailWord_4638209, baseEnd_4638209] using wordTrace_append hprefix tailTrace_4638209
  have hstable : (prefixWord ++ tailWord_4638209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638209).length < 2 ^ (prefixWord ++ tailWord_4638209).sum := by decide
  have hdescent : baseEnd_4638209 < baseStart_4638209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638254 : List Nat := [4, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_4638254 : Nat := 118140960795 + 4638254 * 2 ^ 59
def prefixEnd_4638254 : Nat := 4983230072969 + 3 ^ 40 * 4638254 * 2
def baseEnd_4638254 : Nat := 2381653699639201043594065

theorem tailTrace_4638254 : CollatzResearch.WordTrace tailWord_4638254 prefixEnd_4638254 2381653699639201043594065 := by
  unfold tailWord_4638254
  simp only [CollatzResearch.WordTrace]
  refine ⟨21146377667300672945246227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112780680892270255707979877 21146377667300672945246227)
  ·
    refine ⟨31719566500951009417869341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21146377667300672945246227 31719566500951009417869341)
    ·
      refine ⟨11894837437856628531701003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31719566500951009417869341 11894837437856628531701003)
      ·
        refine ⟨17842256156784942797551505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11894837437856628531701003 17842256156784942797551505)
        ·
          refine ⟨13381692117588707098163629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17842256156784942797551505 13381692117588707098163629)
          ·
            refine ⟨5018134544095765161811361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13381692117588707098163629 5018134544095765161811361)
            ·
              refine ⟨3763600908071823871358521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5018134544095765161811361 3763600908071823871358521)
              ·
                refine ⟨2822700681053867903518891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3763600908071823871358521 2822700681053867903518891)
                ·
                  refine ⟨4234051021580801855278337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2822700681053867903518891 4234051021580801855278337)
                  ·
                    refine ⟨3175538266185601391458753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4234051021580801855278337 3175538266185601391458753)
                    ·
                      refine ⟨2381653699639201043594065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3175538266185601391458753 2381653699639201043594065)
                      ·
                        rfl

theorem cell23_4638254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_4638254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638254 prefixEnd_4638254 := by exact prefixLift 4638254
  have htrace : WordTrace (prefixWord ++ tailWord_4638254) baseStart_4638254 baseEnd_4638254 := by
    simpa [prefixWord, tailWord_4638254, baseEnd_4638254] using wordTrace_append hprefix tailTrace_4638254
  have hstable : (prefixWord ++ tailWord_4638254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638254).length < 2 ^ (prefixWord ++ tailWord_4638254).sum := by decide
  have hdescent : baseEnd_4638254 < baseStart_4638254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638416 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 7, 1, 3]
def baseStart_4638416 : Nat := 118140960795 + 4638416 * 2 ^ 59
def prefixEnd_4638416 : Nat := 4983230072969 + 3 ^ 40 * 4638416 * 2
def baseEnd_4638416 : Nat := 2381736883505229409768319

theorem tailTrace_4638416 : CollatzResearch.WordTrace tailWord_4638416 prefixEnd_4638416 2381736883505229409768319 := by
  unfold tailWord_4638416
  simp only [CollatzResearch.WordTrace]
  refine ⟨84588464981909242614683551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112784619975878990152911401 84588464981909242614683551)
  ·
    refine ⟨126882697472863863922025327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84588464981909242614683551 126882697472863863922025327)
    ·
      refine ⟨190324046209295795883037991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126882697472863863922025327 190324046209295795883037991)
      ·
        refine ⟨285486069313943693824556987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190324046209295795883037991 285486069313943693824556987)
        ·
          refine ⟨428229103970915540736835481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285486069313943693824556987 428229103970915540736835481)
          ·
            refine ⟨321171827978186655552626611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428229103970915540736835481 321171827978186655552626611)
            ·
              refine ⟨481757741967279983328939917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321171827978186655552626611 481757741967279983328939917)
              ·
                refine ⟨180659153237729993748352469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 481757741967279983328939917 180659153237729993748352469)
                ·
                  refine ⟨4234198904009296728477011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 180659153237729993748352469 4234198904009296728477011)
                  ·
                    refine ⟨6351298356013945092715517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4234198904009296728477011 6351298356013945092715517)
                    ·
                      refine ⟨2381736883505229409768319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6351298356013945092715517 2381736883505229409768319)
                      ·
                        rfl

theorem cell23_4638416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 7, 1, 3].length) (baseStart_4638416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638416 prefixEnd_4638416 := by exact prefixLift 4638416
  have htrace : WordTrace (prefixWord ++ tailWord_4638416) baseStart_4638416 baseEnd_4638416 := by
    simpa [prefixWord, tailWord_4638416, baseEnd_4638416] using wordTrace_append hprefix tailTrace_4638416
  have hstable : (prefixWord ++ tailWord_4638416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638416).length < 2 ^ (prefixWord ++ tailWord_4638416).sum := by decide
  have hdescent : baseEnd_4638416 < baseStart_4638416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638456 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 1, 8, 2]
def baseStart_4638456 : Nat := 118140960795 + 4638456 * 2 ^ 59
def prefixEnd_4638456 : Nat := 4983230072969 + 3 ^ 40 * 4638456 * 2
def baseEnd_4638456 : Nat := 2381757422731409253268135

theorem tailTrace_4638456 : CollatzResearch.WordTrace tailWord_4638456 prefixEnd_4638456 2381757422731409253268135 := by
  unfold tailWord_4638456
  simp only [CollatzResearch.WordTrace]
  refine ⟨84589194441836786030411611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112785592589115714707215481 84589194441836786030411611)
  ·
    refine ⟨126883791662755179045617417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84589194441836786030411611 126883791662755179045617417)
    ·
      refine ⟨95162843747066384284213063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126883791662755179045617417 95162843747066384284213063)
      ·
        refine ⟨142744265620599576426319595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95162843747066384284213063 142744265620599576426319595)
        ·
          refine ⟨214116398430899364639479393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142744265620599576426319595 214116398430899364639479393)
          ·
            refine ⟨160587298823174523479609545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214116398430899364639479393 160587298823174523479609545)
            ·
              refine ⟨120440474117380892609707159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160587298823174523479609545 120440474117380892609707159)
              ·
                refine ⟨180660711176071338914560739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120440474117380892609707159 180660711176071338914560739)
                ·
                  refine ⟨270991066764107008371841109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180660711176071338914560739 270991066764107008371841109)
                  ·
                    refine ⟨3175676563641879004357513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 270991066764107008371841109 3175676563641879004357513)
                    ·
                      refine ⟨2381757422731409253268135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3175676563641879004357513 2381757422731409253268135)
                      ·
                        rfl

theorem cell23_4638456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 8, 2].length) (baseStart_4638456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638456 prefixEnd_4638456 := by exact prefixLift 4638456
  have htrace : WordTrace (prefixWord ++ tailWord_4638456) baseStart_4638456 baseEnd_4638456 := by
    simpa [prefixWord, tailWord_4638456, baseEnd_4638456] using wordTrace_append hprefix tailTrace_4638456
  have hstable : (prefixWord ++ tailWord_4638456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638456).length < 2 ^ (prefixWord ++ tailWord_4638456).sum := by decide
  have hdescent : baseEnd_4638456 < baseStart_4638456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638459 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 5]
def baseStart_4638459 : Nat := 118140960795 + 4638459 * 2 ^ 59
def prefixEnd_4638459 : Nat := 4983230072969 + 3 ^ 40 * 4638459 * 2
def baseEnd_4638459 : Nat := 2381758963173372741530621

theorem tailTrace_4638459 : CollatzResearch.WordTrace tailWord_4638459 prefixEnd_4638459 2381758963173372741530621 := by
  unfold tailWord_4638459
  simp only [CollatzResearch.WordTrace]
  refine ⟨169178498302662703573182431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112785665535108469048788287 169178498302662703573182431)
  ·
    refine ⟨253767747453994055359773647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169178498302662703573182431 253767747453994055359773647)
    ·
      refine ⟨380651621180991083039660471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253767747453994055359773647 380651621180991083039660471)
      ·
        refine ⟨570977431771486624559490707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380651621180991083039660471 570977431771486624559490707)
        ·
          refine ⟨856466147657229936839236061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570977431771486624559490707 856466147657229936839236061)
          ·
            refine ⟨321174805371461226314713523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 856466147657229936839236061 321174805371461226314713523)
            ·
              refine ⟨481762208057191839472070285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321174805371461226314713523 481762208057191839472070285)
              ·
                refine ⟨180660828021446939802026357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 481762208057191839472070285 180660828021446939802026357)
                ·
                  refine ⟨16936952627010650606439971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 180660828021446939802026357 16936952627010650606439971)
                  ·
                    refine ⟨25405428940515975909659957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16936952627010650606439971 25405428940515975909659957)
                    ·
                      refine ⟨2381758963173372741530621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25405428940515975909659957 2381758963173372741530621)
                      ·
                        rfl

theorem cell23_4638459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 5].length) (baseStart_4638459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638459 prefixEnd_4638459 := by exact prefixLift 4638459
  have htrace : WordTrace (prefixWord ++ tailWord_4638459) baseStart_4638459 baseEnd_4638459 := by
    simpa [prefixWord, tailWord_4638459, baseEnd_4638459] using wordTrace_append hprefix tailTrace_4638459
  have hstable : (prefixWord ++ tailWord_4638459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638459).length < 2 ^ (prefixWord ++ tailWord_4638459).sum := by decide
  have hdescent : baseEnd_4638459 < baseStart_4638459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638469 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_4638469 : Nat := 118140960795 + 4638469 * 2 ^ 59
def prefixEnd_4638469 : Nat := 4983230072969 + 3 ^ 40 * 4638469 * 2
def baseEnd_4638469 : Nat := 2381764097979917702405575

theorem tailTrace_4638469 : CollatzResearch.WordTrace tailWord_4638469 prefixEnd_4638469 2381764097979917702405575 := by
  unfold tailWord_4638469
  simp only [CollatzResearch.WordTrace]
  refine ⟨169178863032626475281046461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112785908688417650187364307 169178863032626475281046461)
  ·
    refine ⟨63442073637234928230392423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169178863032626475281046461 63442073637234928230392423)
    ·
      refine ⟨95163110455852392345588635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63442073637234928230392423 95163110455852392345588635)
      ·
        refine ⟨142744665683778588518382953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95163110455852392345588635 142744665683778588518382953)
        ·
          refine ⟨107058499262833941388787215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142744665683778588518382953 107058499262833941388787215)
          ·
            refine ⟨160587748894250912083180823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107058499262833941388787215 160587748894250912083180823)
            ·
              refine ⟨240881623341376368124771235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160587748894250912083180823 240881623341376368124771235)
              ·
                refine ⟨361322435012064552187156853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240881623341376368124771235 361322435012064552187156853)
                ·
                  refine ⟨33873978282381051767545955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 361322435012064552187156853 33873978282381051767545955)
                  ·
                    refine ⟨50810967423571577651318933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33873978282381051767545955 50810967423571577651318933)
                    ·
                      refine ⟨2381764097979917702405575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50810967423571577651318933 2381764097979917702405575)
                      ·
                        rfl

theorem cell23_4638469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_4638469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638469 prefixEnd_4638469 := by exact prefixLift 4638469
  have htrace : WordTrace (prefixWord ++ tailWord_4638469) baseStart_4638469 baseEnd_4638469 := by
    simpa [prefixWord, tailWord_4638469, baseEnd_4638469] using wordTrace_append hprefix tailTrace_4638469
  have hstable : (prefixWord ++ tailWord_4638469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638469).length < 2 ^ (prefixWord ++ tailWord_4638469).sum := by decide
  have hdescent : baseEnd_4638469 < baseStart_4638469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638473 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 7, 2, 2]
def baseStart_4638473 : Nat := 118140960795 + 4638473 * 2 ^ 59
def prefixEnd_4638473 : Nat := 4983230072969 + 3 ^ 40 * 4638473 * 2
def baseEnd_4638473 : Nat := 2381766151902535686755557

theorem tailTrace_4638473 : CollatzResearch.WordTrace tailWord_4638473 prefixEnd_4638473 2381766151902535686755557 := by
  unfold tailWord_4638473
  simp only [CollatzResearch.WordTrace]
  refine ⟨169179008924611983964192073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112786005949741322642794715 169179008924611983964192073)
  ·
    refine ⟨126884256693458987973144055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169179008924611983964192073 126884256693458987973144055)
    ·
      refine ⟨190326385040188481959716083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126884256693458987973144055 190326385040188481959716083)
      ·
        refine ⟨285489577560282722939574125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190326385040188481959716083 285489577560282722939574125)
        ·
          refine ⟨107058591585106021102340297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285489577560282722939574125 107058591585106021102340297)
          ·
            refine ⟨80293943688829515826755223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107058591585106021102340297 80293943688829515826755223)
            ·
              refine ⟨120440915533244273740132835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80293943688829515826755223 120440915533244273740132835)
              ·
                refine ⟨180661373299866410610199253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120440915533244273740132835 180661373299866410610199253)
                ·
                  refine ⟨4234250936715618998676545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 180661373299866410610199253 4234250936715618998676545)
                  ·
                    refine ⟨3175688202536714249007409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4234250936715618998676545 3175688202536714249007409)
                    ·
                      refine ⟨2381766151902535686755557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3175688202536714249007409 2381766151902535686755557)
                      ·
                        rfl

theorem cell23_4638473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 2, 2].length) (baseStart_4638473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638473 prefixEnd_4638473 := by exact prefixLift 4638473
  have htrace : WordTrace (prefixWord ++ tailWord_4638473) baseStart_4638473 baseEnd_4638473 := by
    simpa [prefixWord, tailWord_4638473, baseEnd_4638473] using wordTrace_append hprefix tailTrace_4638473
  have hstable : (prefixWord ++ tailWord_4638473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638473).length < 2 ^ (prefixWord ++ tailWord_4638473).sum := by decide
  have hdescent : baseEnd_4638473 < baseStart_4638473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638490 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2]
def baseStart_4638490 : Nat := 118140960795 + 4638490 * 2 ^ 59
def prefixEnd_4638490 : Nat := 4983230072969 + 3 ^ 40 * 4638490 * 2
def baseEnd_4638490 : Nat := 2381774881073662120242979

theorem tailTrace_4638490 : CollatzResearch.WordTrace tailWord_4638490 prefixEnd_4638490 2381774881073662120242979 := by
  unfold tailWord_4638490
  simp only [CollatzResearch.WordTrace]
  refine ⟨42294907241387598966890231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112786419310366930578373949 42294907241387598966890231)
  ·
    refine ⟨63442360862081398450335347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42294907241387598966890231 63442360862081398450335347)
    ·
      refine ⟨95163541293122097675503021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63442360862081398450335347 95163541293122097675503021)
      ·
        refine ⟨35686327984920786628313633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95163541293122097675503021 35686327984920786628313633)
        ·
          refine ⟨26764745988690589971235225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35686327984920786628313633 26764745988690589971235225)
          ·
            refine ⟨20073559491517942478426419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26764745988690589971235225 20073559491517942478426419)
            ·
              refine ⟨30110339237276913717639629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20073559491517942478426419 30110339237276913717639629)
              ·
                refine ⟨11291377213978842644114861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30110339237276913717639629 11291377213978842644114861)
                ·
                  refine ⟨4234266455242065991543073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11291377213978842644114861 4234266455242065991543073)
                  ·
                    refine ⟨3175699841431549493657305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4234266455242065991543073 3175699841431549493657305)
                    ·
                      refine ⟨2381774881073662120242979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3175699841431549493657305 2381774881073662120242979)
                      ·
                        rfl

theorem cell23_4638490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_4638490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638490 prefixEnd_4638490 := by exact prefixLift 4638490
  have htrace : WordTrace (prefixWord ++ tailWord_4638490) baseStart_4638490 baseEnd_4638490 := by
    simpa [prefixWord, tailWord_4638490, baseEnd_4638490] using wordTrace_append hprefix tailTrace_4638490
  have hstable : (prefixWord ++ tailWord_4638490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638490).length < 2 ^ (prefixWord ++ tailWord_4638490).sum := by decide
  have hdescent : baseEnd_4638490 < baseStart_4638490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638513 : List Nat := [1, 2, 2, 3, 2, 4, 2, 7]
def baseStart_4638513 : Nat := 118140960795 + 4638513 * 2 ^ 59
def prefixEnd_4638513 : Nat := 4983230072969 + 3 ^ 40 * 4638513 * 2
def baseEnd_4638513 : Nat := 88214321893656130750199

theorem tailTrace_4638513 : CollatzResearch.WordTrace tailWord_4638513 prefixEnd_4638513 88214321893656130750199 := by
  unfold tailWord_4638513
  simp only [CollatzResearch.WordTrace]
  refine ⟨169180467844467070795648193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112786978562978047197098795 169180467844467070795648193)
  ·
    refine ⟨126885350883350303096736145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169180467844467070795648193 126885350883350303096736145)
    ·
      refine ⟨95164013162512727322552109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126885350883350303096736145 95164013162512727322552109)
      ·
        refine ⟨35686504935942272745957041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95164013162512727322552109 35686504935942272745957041)
        ·
          refine ⟨26764878701956704559467781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35686504935942272745957041 26764878701956704559467781)
          ·
            refine ⟨5018414756616882104900209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26764878701956704559467781 5018414756616882104900209)
            ·
              refine ⟨3763811067462661578675157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5018414756616882104900209 3763811067462661578675157)
              ·
                refine ⟨88214321893656130750199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3763811067462661578675157 88214321893656130750199)
                ·
                  rfl

theorem cell23_4638513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 7].length) (baseStart_4638513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638513 prefixEnd_4638513 := by exact prefixLift 4638513
  have htrace : WordTrace (prefixWord ++ tailWord_4638513) baseStart_4638513 baseEnd_4638513 := by
    simpa [prefixWord, tailWord_4638513, baseEnd_4638513] using wordTrace_append hprefix tailTrace_4638513
  have hstable : (prefixWord ++ tailWord_4638513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638513).length < 2 ^ (prefixWord ++ tailWord_4638513).sum := by decide
  have hdescent : baseEnd_4638513 < baseStart_4638513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638576 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 4]
def baseStart_4638576 : Nat := 118140960795 + 4638576 * 2 ^ 59
def prefixEnd_4638576 : Nat := 4983230072969 + 3 ^ 40 * 4638576 * 2
def baseEnd_4638576 : Nat := 2381819040409948783767583

theorem tailTrace_4638576 : CollatzResearch.WordTrace tailWord_4638576 prefixEnd_4638576 2381819040409948783767583 := by
  unfold tailWord_4638576
  simp only [CollatzResearch.WordTrace]
  refine ⟨84591382821619416277595791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112788510428825888370127721 84591382821619416277595791)
  ·
    refine ⟨126887074232429124416393687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84591382821619416277595791 126887074232429124416393687)
    ·
      refine ⟨190330611348643686624590531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126887074232429124416393687 190330611348643686624590531)
      ·
        refine ⟨285495917022965529936885797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190330611348643686624590531 285495917022965529936885797)
        ·
          refine ⟨53530484441806036863166087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 285495917022965529936885797 53530484441806036863166087)
          ·
            refine ⟨80295726662709055294749131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53530484441806036863166087 80295726662709055294749131)
            ·
              refine ⟨120443589994063582942123697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80295726662709055294749131 120443589994063582942123697)
              ·
                refine ⟨90332692495547687206592773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120443589994063582942123697 90332692495547687206592773)
                ·
                  refine ⟨16937379842915191351236145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90332692495547687206592773 16937379842915191351236145)
                  ·
                    refine ⟨12703034882186393513427109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16937379842915191351236145 12703034882186393513427109)
                    ·
                      refine ⟨2381819040409948783767583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12703034882186393513427109 2381819040409948783767583)
                      ·
                        rfl

theorem cell23_4638576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_4638576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638576 prefixEnd_4638576 := by exact prefixLift 4638576
  have htrace : WordTrace (prefixWord ++ tailWord_4638576) baseStart_4638576 baseEnd_4638576 := by
    simpa [prefixWord, tailWord_4638576, baseEnd_4638576] using wordTrace_append hprefix tailTrace_4638576
  have hstable : (prefixWord ++ tailWord_4638576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638576).length < 2 ^ (prefixWord ++ tailWord_4638576).sum := by decide
  have hdescent : baseEnd_4638576 < baseStart_4638576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638596 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_4638596 : Nat := 118140960795 + 4638596 * 2 ^ 59
def prefixEnd_4638596 : Nat := 4983230072969 + 3 ^ 40 * 4638596 * 2
def baseEnd_4638596 : Nat := 2381829310023038705517491

theorem tailTrace_4638596 : CollatzResearch.WordTrace tailWord_4638596 prefixEnd_4638596 2381829310023038705517491 := by
  unfold tailWord_4638596
  simp only [CollatzResearch.WordTrace]
  refine ⟨84591747551583187985459821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112788996735444250647279761 84591747551583187985459821)
  ·
    refine ⟨31721905331843695494547433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84591747551583187985459821 31721905331843695494547433)
    ·
      refine ⟨23791428998882771620910575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31721905331843695494547433 23791428998882771620910575)
      ·
        refine ⟨35687143498324157431365863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23791428998882771620910575 35687143498324157431365863)
        ·
          refine ⟨53530715247486236147048795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35687143498324157431365863 53530715247486236147048795)
          ·
            refine ⟨80296072871229354220573193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53530715247486236147048795 80296072871229354220573193)
            ·
              refine ⟨60222054653422015665429895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80296072871229354220573193 60222054653422015665429895)
              ·
                refine ⟨90333081980133023498144843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60222054653422015665429895 90333081980133023498144843)
                ·
                  refine ⟨135499622970199535247217265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90333081980133023498144843 135499622970199535247217265)
                  ·
                    refine ⟨101624717227649651435412949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 135499622970199535247217265 101624717227649651435412949)
                    ·
                      refine ⟨2381829310023038705517491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101624717227649651435412949 2381829310023038705517491)
                      ·
                        rfl

theorem cell23_4638596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_4638596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638596 prefixEnd_4638596 := by exact prefixLift 4638596
  have htrace : WordTrace (prefixWord ++ tailWord_4638596) baseStart_4638596 baseEnd_4638596 := by
    simpa [prefixWord, tailWord_4638596, baseEnd_4638596] using wordTrace_append hprefix tailTrace_4638596
  have hstable : (prefixWord ++ tailWord_4638596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638596).length < 2 ^ (prefixWord ++ tailWord_4638596).sum := by decide
  have hdescent : baseEnd_4638596 < baseStart_4638596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638597 : List Nat := [1, 3, 1, 1, 3, 2, 4, 2, 2, 2, 2]
def baseStart_4638597 : Nat := 118140960795 + 4638597 * 2 ^ 59
def prefixEnd_4638597 : Nat := 4983230072969 + 3 ^ 40 * 4638597 * 2
def baseEnd_4638597 : Nat := 2381829823503693201604987

theorem tailTrace_4638597 : CollatzResearch.WordTrace tailWord_4638597 prefixEnd_4638597 2381829823503693201604987 := by
  unfold tailWord_4638597
  simp only [CollatzResearch.WordTrace]
  refine ⟨169183531576162753141706045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112789021050775168761137363 169183531576162753141706045)
  ·
    refine ⟨63443824341061032428139767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169183531576162753141706045 63443824341061032428139767)
    ·
      refine ⟨95165736511591548642209651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63443824341061032428139767 95165736511591548642209651)
      ·
        refine ⟨142748604767387322963314477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95165736511591548642209651 142748604767387322963314477)
        ·
          refine ⟨53530726787770246111242929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142748604767387322963314477 53530726787770246111242929)
          ·
            refine ⟨40148045090827684583432197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53530726787770246111242929 40148045090827684583432197)
            ·
              refine ⟨7527758454530190859393537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40148045090827684583432197 7527758454530190859393537)
              ·
                refine ⟨5645818840897643144545153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7527758454530190859393537 5645818840897643144545153)
                ·
                  refine ⟨4234364130673232358408865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5645818840897643144545153 4234364130673232358408865)
                  ·
                    refine ⟨3175773098004924268806649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4234364130673232358408865 3175773098004924268806649)
                    ·
                      refine ⟨2381829823503693201604987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3175773098004924268806649 2381829823503693201604987)
                      ·
                        rfl

theorem cell23_4638597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 2, 2].length) (baseStart_4638597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638597 prefixEnd_4638597 := by exact prefixLift 4638597
  have htrace : WordTrace (prefixWord ++ tailWord_4638597) baseStart_4638597 baseEnd_4638597 := by
    simpa [prefixWord, tailWord_4638597, baseEnd_4638597] using wordTrace_append hprefix tailTrace_4638597
  have hstable : (prefixWord ++ tailWord_4638597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638597).length < 2 ^ (prefixWord ++ tailWord_4638597).sum := by decide
  have hdescent : baseEnd_4638597 < baseStart_4638597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638610 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4638610 : Nat := 118140960795 + 4638610 * 2 ^ 59
def prefixEnd_4638610 : Nat := 4983230072969 + 3 ^ 40 * 4638610 * 2
def baseEnd_4638610 : Nat := 2381836498752201650742427

theorem tailTrace_4638610 : CollatzResearch.WordTrace tailWord_4638610 prefixEnd_4638610 2381836498752201650742427 := by
  unfold tailWord_4638610
  simp only [CollatzResearch.WordTrace]
  refine ⟨42296001431278914090482321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112789337150077104241286189 42296001431278914090482321)
  ·
    refine ⟨31722001073459185567861741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42296001431278914090482321 31722001073459185567861741)
    ·
      refine ⟨11895750402547194587948153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31722001073459185567861741 11895750402547194587948153)
      ·
        refine ⟨8921812801910395940961115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11895750402547194587948153 8921812801910395940961115)
        ·
          refine ⟨13382719202865593911441673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8921812801910395940961115 13382719202865593911441673)
          ·
            refine ⟨10037039402149195433581255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13382719202865593911441673 10037039402149195433581255)
            ·
              refine ⟨15055559103223793150371883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10037039402149195433581255 15055559103223793150371883)
              ·
                refine ⟨22583338654835689725557825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15055559103223793150371883 22583338654835689725557825)
                ·
                  refine ⟨16937503991126767294168369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22583338654835689725557825 16937503991126767294168369)
                  ·
                    refine ⟨12703127993345075470626277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16937503991126767294168369 12703127993345075470626277)
                    ·
                      refine ⟨2381836498752201650742427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12703127993345075470626277 2381836498752201650742427)
                      ·
                        rfl

theorem cell23_4638610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4638610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638610 prefixEnd_4638610 := by exact prefixLift 4638610
  have htrace : WordTrace (prefixWord ++ tailWord_4638610) baseStart_4638610 baseEnd_4638610 := by
    simpa [prefixWord, tailWord_4638610, baseEnd_4638610] using wordTrace_append hprefix tailTrace_4638610
  have hstable : (prefixWord ++ tailWord_4638610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638610).length < 2 ^ (prefixWord ++ tailWord_4638610).sum := by decide
  have hdescent : baseEnd_4638610 < baseStart_4638610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638613 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_4638613 : Nat := 118140960795 + 4638613 * 2 ^ 59
def prefixEnd_4638613 : Nat := 4983230072969 + 3 ^ 40 * 4638613 * 2
def baseEnd_4638613 : Nat := 2381838039194165139004913

theorem tailTrace_4638613 : CollatzResearch.WordTrace tailWord_4638613 prefixEnd_4638613 2381838039194165139004913 := by
  unfold tailWord_4638613
  simp only [CollatzResearch.WordTrace]
  refine ⟨169184115144104787874288493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112789410096069858582858995 169184115144104787874288493)
  ·
    refine ⟨63444043179039295452858185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169184115144104787874288493 63444043179039295452858185)
    ·
      refine ⟨47583032384279471589643639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63444043179039295452858185 47583032384279471589643639)
      ·
        refine ⟨71374548576419207384465459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47583032384279471589643639 71374548576419207384465459)
        ·
          refine ⟨107061822864628811076698189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71374548576419207384465459 107061822864628811076698189)
          ·
            refine ⟨40148183574235804153761821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107061822864628811076698189 40148183574235804153761821)
            ·
              refine ⟨15055568840338426557660683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40148183574235804153761821 15055568840338426557660683)
              ·
                refine ⟨22583353260507639836491025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15055568840338426557660683 22583353260507639836491025)
                ·
                  refine ⟨16937514945380729877368269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22583353260507639836491025 16937514945380729877368269)
                  ·
                    refine ⟨6351568104517773704013101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16937514945380729877368269 6351568104517773704013101)
                    ·
                      refine ⟨2381838039194165139004913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6351568104517773704013101 2381838039194165139004913)
                      ·
                        rfl

theorem cell23_4638613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_4638613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638613 prefixEnd_4638613 := by exact prefixLift 4638613
  have htrace : WordTrace (prefixWord ++ tailWord_4638613) baseStart_4638613 baseEnd_4638613 := by
    simpa [prefixWord, tailWord_4638613, baseEnd_4638613] using wordTrace_append hprefix tailTrace_4638613
  have hstable : (prefixWord ++ tailWord_4638613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638613).length < 2 ^ (prefixWord ++ tailWord_4638613).sum := by decide
  have hdescent : baseEnd_4638613 < baseStart_4638613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638670 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2]
def baseStart_4638670 : Nat := 118140960795 + 4638670 * 2 ^ 59
def prefixEnd_4638670 : Nat := 4983230072969 + 3 ^ 40 * 4638670 * 2
def baseEnd_4638670 : Nat := 2381867307591471415992151

theorem tailTrace_4638670 : CollatzResearch.WordTrace tailWord_4638670 prefixEnd_4638670 2381867307591471415992151 := by
  unfold tailWord_4638670
  simp only [CollatzResearch.WordTrace]
  refine ⟨21148274263112285826139183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112790796069932191072742309 21148274263112285826139183)
  ·
    refine ⟨31722411394668428739208775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21148274263112285826139183 31722411394668428739208775)
    ·
      refine ⟨47583617092002643108813163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31722411394668428739208775 47583617092002643108813163)
      ·
        refine ⟨71375425638003964663219745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47583617092002643108813163 71375425638003964663219745)
        ·
          refine ⟨53531569228502973497414809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71375425638003964663219745 53531569228502973497414809)
          ·
            refine ⟨40148676921377230123061107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53531569228502973497414809 40148676921377230123061107)
            ·
              refine ⟨60223015382065845184591661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40148676921377230123061107 60223015382065845184591661)
              ·
                refine ⟨22583630768274691944221873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60223015382065845184591661 22583630768274691944221873)
                ·
                  refine ⟨16937723076206018958166405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22583630768274691944221873 16937723076206018958166405)
                  ·
                    refine ⟨3175823076788628554656201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16937723076206018958166405 3175823076788628554656201)
                    ·
                      refine ⟨2381867307591471415992151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3175823076788628554656201 2381867307591471415992151)
                      ·
                        rfl

theorem cell23_4638670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_4638670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638670 prefixEnd_4638670 := by exact prefixLift 4638670
  have htrace : WordTrace (prefixWord ++ tailWord_4638670) baseStart_4638670 baseEnd_4638670 := by
    simpa [prefixWord, tailWord_4638670, baseEnd_4638670] using wordTrace_append hprefix tailTrace_4638670
  have hstable : (prefixWord ++ tailWord_4638670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638670).length < 2 ^ (prefixWord ++ tailWord_4638670).sum := by decide
  have hdescent : baseEnd_4638670 < baseStart_4638670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638673 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 6, 2, 3]
def baseStart_4638673 : Nat := 118140960795 + 4638673 * 2 ^ 59
def prefixEnd_4638673 : Nat := 4983230072969 + 3 ^ 40 * 4638673 * 2
def baseEnd_4638673 : Nat := 2381868848033434904254637

theorem tailTrace_4638673 : CollatzResearch.WordTrace tailWord_4638673 prefixEnd_4638673 2381868848033434904254637 := by
  unfold tailWord_4638673
  simp only [CollatzResearch.WordTrace]
  refine ⟨169186303523887418121472673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112790869015924945414315115 169186303523887418121472673)
  ·
    refine ⟨126889727642915563591104505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169186303523887418121472673 126889727642915563591104505)
    ·
      refine ⟨95167295732186672693328379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126889727642915563591104505 95167295732186672693328379)
      ·
        refine ⟨142750943598280009039992569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95167295732186672693328379 142750943598280009039992569)
        ·
          refine ⟨107063207698710006779994427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142750943598280009039992569 107063207698710006779994427)
          ·
            refine ⟨160594811548065010169991641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107063207698710006779994427 160594811548065010169991641)
            ·
              refine ⟨120446108661048757627493731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160594811548065010169991641 120446108661048757627493731)
              ·
                refine ⟨180669162991573136441240597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120446108661048757627493731 180669162991573136441240597)
                ·
                  refine ⟨8468867015229990770683153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 180669162991573136441240597 8468867015229990770683153)
                  ·
                    refine ⟨6351650261422493078012365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8468867015229990770683153 6351650261422493078012365)
                    ·
                      refine ⟨2381868848033434904254637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6351650261422493078012365 2381868848033434904254637)
                      ·
                        rfl

theorem cell23_4638673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_4638673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638673 prefixEnd_4638673 := by exact prefixLift 4638673
  have htrace : WordTrace (prefixWord ++ tailWord_4638673) baseStart_4638673 baseEnd_4638673 := by
    simpa [prefixWord, tailWord_4638673, baseEnd_4638673] using wordTrace_append hprefix tailTrace_4638673
  have hstable : (prefixWord ++ tailWord_4638673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638673).length < 2 ^ (prefixWord ++ tailWord_4638673).sum := by decide
  have hdescent : baseEnd_4638673 < baseStart_4638673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638720 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 3, 1, 3]
def baseStart_4638720 : Nat := 118140960795 + 4638720 * 2 ^ 59
def prefixEnd_4638720 : Nat := 4983230072969 + 3 ^ 40 * 4638720 * 2
def baseEnd_4638720 : Nat := 2381892981624196220366921

theorem tailTrace_4638720 : CollatzResearch.WordTrace tailWord_4638720 prefixEnd_4638720 2381892981624196220366921 := by
  unfold tailWord_4638720
  simp only [CollatzResearch.WordTrace]
  refine ⟨84594008877358572574216807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112792011836478096765622409 84594008877358572574216807)
  ·
    refine ⟨126891013316037858861325211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84594008877358572574216807 126891013316037858861325211)
    ·
      refine ⟨190336519974056788291987817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126891013316037858861325211 190336519974056788291987817)
      ·
        refine ⟨142752389980542591218990863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190336519974056788291987817 142752389980542591218990863)
        ·
          refine ⟨214128584970813886828486295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142752389980542591218990863 214128584970813886828486295)
          ·
            refine ⟨321192877456220830242729443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214128584970813886828486295 321192877456220830242729443)
            ·
              refine ⟨481789316184331245364094165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321192877456220830242729443 481789316184331245364094165)
              ·
                refine ⟨11291937098070263563220957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 481789316184331245364094165 11291937098070263563220957)
                ·
                  refine ⟨4234476411776348836207859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11291937098070263563220957 4234476411776348836207859)
                  ·
                    refine ⟨6351714617664523254311789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4234476411776348836207859 6351714617664523254311789)
                    ·
                      refine ⟨2381892981624196220366921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6351714617664523254311789 2381892981624196220366921)
                      ·
                        rfl

theorem cell23_4638720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_4638720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638720 prefixEnd_4638720 := by exact prefixLift 4638720
  have htrace : WordTrace (prefixWord ++ tailWord_4638720) baseStart_4638720 baseEnd_4638720 := by
    simpa [prefixWord, tailWord_4638720, baseEnd_4638720] using wordTrace_append hprefix tailTrace_4638720
  have hstable : (prefixWord ++ tailWord_4638720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638720).length < 2 ^ (prefixWord ++ tailWord_4638720).sum := by decide
  have hdescent : baseEnd_4638720 < baseStart_4638720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638727 : List Nat := [1, 1, 4, 3, 1, 4, 2, 1, 6]
def baseStart_4638727 : Nat := 118140960795 + 4638727 * 2 ^ 59
def prefixEnd_4638727 : Nat := 4983230072969 + 3 ^ 40 * 4638727 * 2
def baseEnd_4638727 : Nat := 264655175109864188108821

theorem tailTrace_4638727 : CollatzResearch.WordTrace tailWord_4638727 prefixEnd_4638727 264655175109864188108821 := by
  unfold tailWord_4638727
  simp only [CollatzResearch.WordTrace]
  refine ⟨169188273065691785343938435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112792182043794523562625623 169188273065691785343938435)
  ·
    refine ⟨253782409598537678015907653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169188273065691785343938435 253782409598537678015907653)
    ·
      refine ⟨47584201799725814627982685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 253782409598537678015907653 47584201799725814627982685)
      ·
        refine ⟨17844075674897180485493507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47584201799725814627982685 17844075674897180485493507)
        ·
          refine ⟨26766113512345770728240261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17844075674897180485493507 26766113512345770728240261)
          ·
            refine ⟨5018646283564832011545049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26766113512345770728240261 5018646283564832011545049)
            ·
              refine ⟨3763984712673624008658787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5018646283564832011545049 3763984712673624008658787)
              ·
                refine ⟨5645977069010436012988181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3763984712673624008658787 5645977069010436012988181)
                ·
                  refine ⟨264655175109864188108821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5645977069010436012988181 264655175109864188108821)
                  ·
                    rfl

theorem cell23_4638727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 6].length) (baseStart_4638727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638727 prefixEnd_4638727 := by exact prefixLift 4638727
  have htrace : WordTrace (prefixWord ++ tailWord_4638727) baseStart_4638727 baseEnd_4638727 := by
    simpa [prefixWord, tailWord_4638727, baseEnd_4638727] using wordTrace_append hprefix tailTrace_4638727
  have hstable : (prefixWord ++ tailWord_4638727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638727).length < 2 ^ (prefixWord ++ tailWord_4638727).sum := by decide
  have hdescent : baseEnd_4638727 < baseStart_4638727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638754 : List Nat := [3, 3, 1, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_4638754 : Nat := 118140960795 + 4638754 * 2 ^ 59
def prefixEnd_4638754 : Nat := 4983230072969 + 3 ^ 40 * 4638754 * 2
def baseEnd_4638754 : Nat := 2381910439966449087341765

theorem tailTrace_4638754 : CollatzResearch.WordTrace tailWord_4638754 prefixEnd_4638754 2381910439966449087341765 := by
  unfold tailWord_4638754
  simp only [CollatzResearch.WordTrace]
  refine ⟨42297314459148492238792829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112792838557729312636780877 42297314459148492238792829)
  ·
    refine ⟨15861492922180684589547311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42297314459148492238792829 15861492922180684589547311)
    ·
      refine ⟨23792239383271026884320967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15861492922180684589547311 23792239383271026884320967)
      ·
        refine ⟨35688359074906540326481451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23792239383271026884320967 35688359074906540326481451)
        ·
          refine ⟨53532538612359810489722177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35688359074906540326481451 53532538612359810489722177)
          ·
            refine ⟨40149403959269857867291633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53532538612359810489722177 40149403959269857867291633)
            ·
              refine ⟨30112052969452393400468725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40149403959269857867291633 30112052969452393400468725)
              ·
                refine ⟨2823004965886161881293943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30112052969452393400468725 2823004965886161881293943)
                ·
                  refine ⟨4234507448829242821940915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823004965886161881293943 4234507448829242821940915)
                  ·
                    refine ⟨6351761173243864232911373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4234507448829242821940915 6351761173243864232911373)
                    ·
                      refine ⟨2381910439966449087341765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6351761173243864232911373 2381910439966449087341765)
                      ·
                        rfl

theorem cell23_4638754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_4638754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638754 prefixEnd_4638754 := by exact prefixLift 4638754
  have htrace : WordTrace (prefixWord ++ tailWord_4638754) baseStart_4638754 baseEnd_4638754 := by
    simpa [prefixWord, tailWord_4638754, baseEnd_4638754] using wordTrace_append hprefix tailTrace_4638754
  have hstable : (prefixWord ++ tailWord_4638754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638754).length < 2 ^ (prefixWord ++ tailWord_4638754).sum := by decide
  have hdescent : baseEnd_4638754 < baseStart_4638754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638757 : List Nat := [1, 3, 1, 2, 2, 4, 3, 1, 1, 5]
def baseStart_4638757 : Nat := 118140960795 + 4638757 * 2 ^ 59
def prefixEnd_4638757 : Nat := 4983230072969 + 3 ^ 40 * 4638757 * 2
def baseEnd_4638757 : Nat := 793970660136137525201417

theorem tailTrace_4638757 : CollatzResearch.WordTrace tailWord_4638757 prefixEnd_4638757 793970660136137525201417 := by
  unfold tailWord_4638757
  simp only [CollatzResearch.WordTrace]
  refine ⟨169189367255583100467530525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112792911503722066978353683 169189367255583100467530525)
  ·
    refine ⟨63446012720843662675323947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169189367255583100467530525 63446012720843662675323947)
    ·
      refine ⟨95169019081265494012985921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63446012720843662675323947 95169019081265494012985921)
      ·
        refine ⟨71376764310949120509739441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95169019081265494012985921 71376764310949120509739441)
        ·
          refine ⟨53532573233211840382304581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71376764310949120509739441 53532573233211840382304581)
          ·
            refine ⟨10037357481227220071682109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53532573233211840382304581 10037357481227220071682109)
            ·
              refine ⟨3764009055460207526880791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10037357481227220071682109 3764009055460207526880791)
              ·
                refine ⟨5646013583190311290321187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3764009055460207526880791 5646013583190311290321187)
                ·
                  refine ⟨8469020374785466935481781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5646013583190311290321187 8469020374785466935481781)
                  ·
                    refine ⟨793970660136137525201417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8469020374785466935481781 793970660136137525201417)
                    ·
                      rfl

theorem cell23_4638757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_4638757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638757 prefixEnd_4638757 := by exact prefixLift 4638757
  have htrace : WordTrace (prefixWord ++ tailWord_4638757) baseStart_4638757 baseEnd_4638757 := by
    simpa [prefixWord, tailWord_4638757, baseEnd_4638757] using wordTrace_append hprefix tailTrace_4638757
  have hstable : (prefixWord ++ tailWord_4638757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638757).length < 2 ^ (prefixWord ++ tailWord_4638757).sum := by decide
  have hdescent : baseEnd_4638757 < baseStart_4638757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638763 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 5]
def baseStart_4638763 : Nat := 118140960795 + 4638763 * 2 ^ 59
def prefixEnd_4638763 : Nat := 4983230072969 + 3 ^ 40 * 4638763 * 2
def baseEnd_4638763 : Nat := 2381915061292339552129223

theorem tailTrace_4638763 : CollatzResearch.WordTrace tailWord_4638763 prefixEnd_4638763 2381915061292339552129223 := by
  unfold tailWord_4638763
  simp only [CollatzResearch.WordTrace]
  refine ⟨169189586093561363492248943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112793057395707575661499295 169189586093561363492248943)
  ·
    refine ⟨253784379140342045238373415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169189586093561363492248943 253784379140342045238373415)
    ·
      refine ⟨380676568710513067857560123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253784379140342045238373415 380676568710513067857560123)
      ·
        refine ⟨571014853065769601786340185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380676568710513067857560123 571014853065769601786340185)
        ·
          refine ⟨428261139799327201339755139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571014853065769601786340185 428261139799327201339755139)
          ·
            refine ⟨642391709698990802009632709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428261139799327201339755139 642391709698990802009632709)
            ·
              refine ⟨120448445568560775376806133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 642391709698990802009632709 120448445568560775376806133)
              ·
                refine ⟨11292041772052572691575575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120448445568560775376806133 11292041772052572691575575)
                ·
                  refine ⟨16938062658078859037363363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11292041772052572691575575 16938062658078859037363363)
                  ·
                    refine ⟨25407093987118288556045045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16938062658078859037363363 25407093987118288556045045)
                    ·
                      refine ⟨2381915061292339552129223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25407093987118288556045045 2381915061292339552129223)
                      ·
                        rfl

theorem cell23_4638763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 5].length) (baseStart_4638763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638763 prefixEnd_4638763 := by exact prefixLift 4638763
  have htrace : WordTrace (prefixWord ++ tailWord_4638763) baseStart_4638763 baseEnd_4638763 := by
    simpa [prefixWord, tailWord_4638763, baseEnd_4638763] using wordTrace_append hprefix tailTrace_4638763
  have hstable : (prefixWord ++ tailWord_4638763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638763).length < 2 ^ (prefixWord ++ tailWord_4638763).sum := by decide
  have hdescent : baseEnd_4638763 < baseStart_4638763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638773 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_4638773 : Nat := 118140960795 + 4638773 * 2 ^ 59
def prefixEnd_4638773 : Nat := 4983230072969 + 3 ^ 40 * 4638773 * 2
def baseEnd_4638773 : Nat := 2381920196098884513004177

theorem tailTrace_4638773 : CollatzResearch.WordTrace tailWord_4638773 prefixEnd_4638773 2381920196098884513004177 := by
  unfold tailWord_4638773
  simp only [CollatzResearch.WordTrace]
  refine ⟨169189950823525135200112973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112793300549016756800075315 169189950823525135200112973)
  ·
    refine ⟨63446231558821925700042365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169189950823525135200112973 63446231558821925700042365)
    ·
      refine ⟨23792336834558222137515887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63446231558821925700042365 23792336834558222137515887)
      ·
        refine ⟨35688505251837333206273831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23792336834558222137515887 35688505251837333206273831)
        ·
          refine ⟨53532757877755999809410747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35688505251837333206273831 53532757877755999809410747)
          ·
            refine ⟨80299136816633999714116121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53532757877755999809410747 80299136816633999714116121)
            ·
              refine ⟨60224352612475499785587091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80299136816633999714116121 60224352612475499785587091)
              ·
                refine ⟨90336528918713249678380637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60224352612475499785587091 90336528918713249678380637)
                ·
                  refine ⟨33876198344517468629392739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90336528918713249678380637 33876198344517468629392739)
                  ·
                    refine ⟨50814297516776202944089109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33876198344517468629392739 50814297516776202944089109)
                    ·
                      refine ⟨2381920196098884513004177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50814297516776202944089109 2381920196098884513004177)
                      ·
                        rfl

theorem cell23_4638773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_4638773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638773 prefixEnd_4638773 := by exact prefixLift 4638773
  have htrace : WordTrace (prefixWord ++ tailWord_4638773) baseStart_4638773 baseEnd_4638773 := by
    simpa [prefixWord, tailWord_4638773, baseEnd_4638773] using wordTrace_append hprefix tailTrace_4638773
  have hstable : (prefixWord ++ tailWord_4638773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638773).length < 2 ^ (prefixWord ++ tailWord_4638773).sum := by decide
  have hdescent : baseEnd_4638773 < baseStart_4638773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638780 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_4638780 : Nat := 118140960795 + 4638780 * 2 ^ 59
def prefixEnd_4638780 : Nat := 4983230072969 + 3 ^ 40 * 4638780 * 2
def baseEnd_4638780 : Nat := 2381923790463465985616645

theorem tailTrace_4638780 : CollatzResearch.WordTrace tailWord_4638780 prefixEnd_4638780 2381923790463465985616645 := by
  unfold tailWord_4638780
  simp only [CollatzResearch.WordTrace]
  refine ⟨84595103067249887697808897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112793470756333183597078529 84595103067249887697808897)
  ·
    refine ⟨63446327300437415773356673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84595103067249887697808897 63446327300437415773356673)
    ·
      refine ⟨47584745475328061830017505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63446327300437415773356673 47584745475328061830017505)
      ·
        refine ⟨35688559106496046372513129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47584745475328061830017505 35688559106496046372513129)
        ·
          refine ⟨26766419329872034779384847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35688559106496046372513129 26766419329872034779384847)
          ·
            refine ⟨40149628994808052169077271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26766419329872034779384847 40149628994808052169077271)
            ·
              refine ⟨60224443492212078253615907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40149628994808052169077271 60224443492212078253615907)
              ·
                refine ⟨90336665238318117380423861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60224443492212078253615907 90336665238318117380423861)
                ·
                  refine ⟨8469062366092323504414737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90336665238318117380423861 8469062366092323504414737)
                  ·
                    refine ⟨6351796774569242628311053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8469062366092323504414737 6351796774569242628311053)
                    ·
                      refine ⟨2381923790463465985616645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6351796774569242628311053 2381923790463465985616645)
                      ·
                        rfl

theorem cell23_4638780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_4638780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638780 prefixEnd_4638780 := by exact prefixLift 4638780
  have htrace : WordTrace (prefixWord ++ tailWord_4638780) baseStart_4638780 baseEnd_4638780 := by
    simpa [prefixWord, tailWord_4638780, baseEnd_4638780] using wordTrace_append hprefix tailTrace_4638780
  have hstable : (prefixWord ++ tailWord_4638780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638780).length < 2 ^ (prefixWord ++ tailWord_4638780).sum := by decide
  have hdescent : baseEnd_4638780 < baseStart_4638780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638783 : List Nat := [1, 1, 2, 2, 3, 1, 5, 8]
def baseStart_4638783 : Nat := 118140960795 + 4638783 * 2 ^ 59
def prefixEnd_4638783 : Nat := 4983230072969 + 3 ^ 40 * 4638783 * 2
def baseEnd_4638783 : Nat := 88219456700201091625153

theorem tailTrace_4638783 : CollatzResearch.WordTrace tailWord_4638783 prefixEnd_4638783 88219456700201091625153 := by
  unfold tailWord_4638783
  simp only [CollatzResearch.WordTrace]
  refine ⟨169190315553488906907977003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112793543702325937938651335 169190315553488906907977003)
  ·
    refine ⟨253785473330233360361965505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169190315553488906907977003 253785473330233360361965505)
    ·
      refine ⟨190339104997675020271474129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253785473330233360361965505 190339104997675020271474129)
      ·
        refine ⟨142754328748256265203605597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190339104997675020271474129 142754328748256265203605597)
        ·
          refine ⟨53532873280596099451352099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142754328748256265203605597 53532873280596099451352099)
          ·
            refine ⟨80299309920894149177028149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53532873280596099451352099 80299309920894149177028149)
            ·
              refine ⟨7528060305083826485346389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80299309920894149177028149 7528060305083826485346389)
              ·
                refine ⟨88219456700201091625153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7528060305083826485346389 88219456700201091625153)
                ·
                  rfl

theorem cell23_4638783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 8].length) (baseStart_4638783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638783 prefixEnd_4638783 := by exact prefixLift 4638783
  have htrace : WordTrace (prefixWord ++ tailWord_4638783) baseStart_4638783 baseEnd_4638783 := by
    simpa [prefixWord, tailWord_4638783, baseEnd_4638783] using wordTrace_append hprefix tailTrace_4638783
  have hstable : (prefixWord ++ tailWord_4638783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638783).length < 2 ^ (prefixWord ++ tailWord_4638783).sum := by decide
  have hdescent : baseEnd_4638783 < baseStart_4638783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638797 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_4638797 : Nat := 118140960795 + 4638797 * 2 ^ 59
def prefixEnd_4638797 : Nat := 4983230072969 + 3 ^ 40 * 4638797 * 2
def baseEnd_4638797 : Nat := 2381932519634592419104067

theorem tailTrace_4638797 : CollatzResearch.WordTrace tailWord_4638797 prefixEnd_4638797 2381932519634592419104067 := by
  unfold tailWord_4638797
  simp only [CollatzResearch.WordTrace]
  refine ⟨169190826175438187298986645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112793884116958791532657763 169190826175438187298986645)
  ·
    refine ⟨7930819976973665029639999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 169190826175438187298986645 7930819976973665029639999)
    ·
      refine ⟨11896229965460497544459999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7930819976973665029639999 11896229965460497544459999)
      ·
        refine ⟨17844344948190746316689999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11896229965460497544459999 17844344948190746316689999)
        ·
          refine ⟨26766517422286119475034999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17844344948190746316689999 26766517422286119475034999)
          ·
            refine ⟨40149776133429179212552499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26766517422286119475034999 40149776133429179212552499)
            ·
              refine ⟨60224664200143768818828749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40149776133429179212552499 60224664200143768818828749)
              ·
                refine ⟨22584249075053913307060781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60224664200143768818828749 22584249075053913307060781)
                ·
                  refine ⟨8469093403145217490147793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22584249075053913307060781 8469093403145217490147793)
                  ·
                    refine ⟨6351820052358913117610845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8469093403145217490147793 6351820052358913117610845)
                    ·
                      refine ⟨2381932519634592419104067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6351820052358913117610845 2381932519634592419104067)
                      ·
                        rfl

theorem cell23_4638797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_4638797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638797 prefixEnd_4638797 := by exact prefixLift 4638797
  have htrace : WordTrace (prefixWord ++ tailWord_4638797) baseStart_4638797 baseEnd_4638797 := by
    simpa [prefixWord, tailWord_4638797, baseEnd_4638797] using wordTrace_append hprefix tailTrace_4638797
  have hstable : (prefixWord ++ tailWord_4638797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638797).length < 2 ^ (prefixWord ++ tailWord_4638797).sum := by decide
  have hdescent : baseEnd_4638797 < baseStart_4638797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638810 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3]
def baseStart_4638810 : Nat := 118140960795 + 4638810 * 2 ^ 59
def prefixEnd_4638810 : Nat := 4983230072969 + 3 ^ 40 * 4638810 * 2
def baseEnd_4638810 : Nat := 2381939194883100868241507

theorem tailTrace_4638810 : CollatzResearch.WordTrace tailWord_4638810 prefixEnd_4638810 2381939194883100868241507 := by
  unfold tailWord_4638810
  simp only [CollatzResearch.WordTrace]
  refine ⟨42297825081097772629802471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112794200216260727012806589 42297825081097772629802471)
  ·
    refine ⟨63446737621646658944703707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42297825081097772629802471 63446737621646658944703707)
    ·
      refine ⟨95170106432469988417055561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63446737621646658944703707 95170106432469988417055561)
      ·
        refine ⟨71377579824352491312791671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95170106432469988417055561 71377579824352491312791671)
        ·
          refine ⟨107066369736528736969187507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71377579824352491312791671 107066369736528736969187507)
          ·
            refine ⟨160599554604793105453781261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107066369736528736969187507 160599554604793105453781261)
            ·
              refine ⟨60224832976797414545167973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160599554604793105453781261 60224832976797414545167973)
              ·
                refine ⟨11292156183149515227218995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60224832976797414545167973 11292156183149515227218995)
                ·
                  refine ⟨16938234274724272840828493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11292156183149515227218995 16938234274724272840828493)
                  ·
                    refine ⟨6351837853021602315310685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16938234274724272840828493 6351837853021602315310685)
                    ·
                      refine ⟨2381939194883100868241507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6351837853021602315310685 2381939194883100868241507)
                      ·
                        rfl

theorem cell23_4638810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_4638810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638810 prefixEnd_4638810 := by exact prefixLift 4638810
  have htrace : WordTrace (prefixWord ++ tailWord_4638810) baseStart_4638810 baseEnd_4638810 := by
    simpa [prefixWord, tailWord_4638810, baseEnd_4638810] using wordTrace_append hprefix tailTrace_4638810
  have hstable : (prefixWord ++ tailWord_4638810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638810).length < 2 ^ (prefixWord ++ tailWord_4638810).sum := by decide
  have hdescent : baseEnd_4638810 < baseStart_4638810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638873 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 9]
def baseStart_4638873 : Nat := 118140960795 + 4638873 * 2 ^ 59
def prefixEnd_4638873 : Nat := 4983230072969 + 3 ^ 40 * 4638873 * 2
def baseEnd_4638873 : Nat := 264663504907148235750413

theorem tailTrace_4638873 : CollatzResearch.WordTrace tailWord_4638873 prefixEnd_4638873 264663504907148235750413 := by
  unfold tailWord_4638873
  simp only [CollatzResearch.WordTrace]
  refine ⟨169193598123162852278753273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112795732082108568185835515 169193598123162852278753273)
  ·
    refine ⟨126895198592372139209064955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169193598123162852278753273 126895198592372139209064955)
    ·
      refine ⟨190342797888558208813597433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126895198592372139209064955 190342797888558208813597433)
      ·
        refine ⟨142757098416418656610198075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190342797888558208813597433 142757098416418656610198075)
        ·
          refine ⟨214135647624627984915297113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142757098416418656610198075 214135647624627984915297113)
          ·
            refine ⟨160601735718470988686472835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214135647624627984915297113 160601735718470988686472835)
            ·
              refine ⟨240902603577706483029709253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160601735718470988686472835 240902603577706483029709253)
              ·
                refine ⟨45169238170819965568070485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240902603577706483029709253 45169238170819965568070485)
                ·
                  refine ⟨264663504907148235750413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45169238170819965568070485 264663504907148235750413)
                  ·
                    rfl

theorem cell23_4638873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 9].length) (baseStart_4638873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638873 prefixEnd_4638873 := by exact prefixLift 4638873
  have htrace : WordTrace (prefixWord ++ tailWord_4638873) baseStart_4638873 baseEnd_4638873 := by
    simpa [prefixWord, tailWord_4638873, baseEnd_4638873] using wordTrace_append hprefix tailTrace_4638873
  have hstable : (prefixWord ++ tailWord_4638873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638873).length < 2 ^ (prefixWord ++ tailWord_4638873).sum := by decide
  have hdescent : baseEnd_4638873 < baseStart_4638873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638941 : List Nat := [1, 4, 3, 2, 1, 1, 4, 2, 5]
def baseStart_4638941 : Nat := 118140960795 + 4638941 * 2 ^ 59
def prefixEnd_4638941 : Nat := 4983230072969 + 3 ^ 40 * 4638941 * 2
def baseEnd_4638941 : Nat := 264667384538759983967045

theorem tailTrace_4638941 : CollatzResearch.WordTrace tailWord_4638941 prefixEnd_4638941 264667384538759983967045 := by
  unfold tailWord_4638941
  simp only [CollatzResearch.WordTrace]
  refine ⟨169196078286916499892228677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112797385524610999928152451 169196078286916499892228677)
  ·
    refine ⟨31724264678796843729792877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169196078286916499892228677 31724264678796843729792877)
    ·
      refine ⟨11896599254548816398672329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31724264678796843729792877 11896599254548816398672329)
      ·
        refine ⟨8922449440911612299004247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11896599254548816398672329 8922449440911612299004247)
        ·
          refine ⟨13383674161367418448506371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8922449440911612299004247 13383674161367418448506371)
          ·
            refine ⟨20075511242051127672759557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13383674161367418448506371 20075511242051127672759557)
            ·
              refine ⟨3764158357884586438642417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20075511242051127672759557 3764158357884586438642417)
              ·
                refine ⟨2823118768413439828981813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3764158357884586438642417 2823118768413439828981813)
                ·
                  refine ⟨264667384538759983967045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2823118768413439828981813 264667384538759983967045)
                  ·
                    rfl

theorem cell23_4638941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_4638941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638941 prefixEnd_4638941 := by exact prefixLift 4638941
  have htrace : WordTrace (prefixWord ++ tailWord_4638941) baseStart_4638941 baseEnd_4638941 := by
    simpa [prefixWord, tailWord_4638941, baseEnd_4638941] using wordTrace_append hprefix tailTrace_4638941
  have hstable : (prefixWord ++ tailWord_4638941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638941).length < 2 ^ (prefixWord ++ tailWord_4638941).sum := by decide
  have hdescent : baseEnd_4638941 < baseStart_4638941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638974 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_4638974 : Nat := 118140960795 + 4638974 * 2 ^ 59
def prefixEnd_4638974 : Nat := 4983230072969 + 3 ^ 40 * 4638974 * 2
def baseEnd_4638974 : Nat := 2382023405710438226590753

theorem tailTrace_4638974 : CollatzResearch.WordTrace tailWord_4638974 prefixEnd_4638974 2382023405710438226590753 := by
  unfold tailWord_4638974
  simp only [CollatzResearch.WordTrace]
  refine ⟨21149660236974618316022497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112798187930531297685453317 21149660236974618316022497)
  ·
    refine ⟨15862245177730963737016873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21149660236974618316022497 15862245177730963737016873)
    ·
      refine ⟨11896683883298222802762655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15862245177730963737016873 11896683883298222802762655)
      ·
        refine ⟨17845025824947334204143983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11896683883298222802762655 17845025824947334204143983)
        ·
          refine ⟨26767538737421001306215975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17845025824947334204143983 26767538737421001306215975)
          ·
            refine ⟨40151308106131501959323963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26767538737421001306215975 40151308106131501959323963)
            ·
              refine ⟨60226962159197252938985945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40151308106131501959323963 60226962159197252938985945)
              ·
                refine ⟨45170221619397939704239459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60226962159197252938985945 45170221619397939704239459)
                ·
                  refine ⟨67755332429096909556359189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45170221619397939704239459 67755332429096909556359189)
                  ·
                    refine ⟨3176031207613917635454337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67755332429096909556359189 3176031207613917635454337)
                    ·
                      refine ⟨2382023405710438226590753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176031207613917635454337 2382023405710438226590753)
                      ·
                        rfl

theorem cell23_4638974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_4638974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638974 prefixEnd_4638974 := by exact prefixLift 4638974
  have htrace : WordTrace (prefixWord ++ tailWord_4638974) baseStart_4638974 baseEnd_4638974 := by
    simpa [prefixWord, tailWord_4638974, baseEnd_4638974] using wordTrace_append hprefix tailTrace_4638974
  have hstable : (prefixWord ++ tailWord_4638974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638974).length < 2 ^ (prefixWord ++ tailWord_4638974).sum := by decide
  have hdescent : baseEnd_4638974 < baseStart_4638974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638977 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_4638977 : Nat := 118140960795 + 4638977 * 2 ^ 59
def prefixEnd_4638977 : Nat := 4983230072969 + 3 ^ 40 * 4638977 * 2
def baseEnd_4638977 : Nat := 2382024946152401714853239

theorem tailTrace_4638977 : CollatzResearch.WordTrace tailWord_4638977 prefixEnd_4638977 2382024946152401714853239 := by
  unfold tailWord_4638977
  simp only [CollatzResearch.WordTrace]
  refine ⟨169197391314786078040539185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112798260876524052027026123 169197391314786078040539185)
  ·
    refine ⟨126898043486089558530404389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169197391314786078040539185 126898043486089558530404389)
    ·
      refine ⟨23793383153641792224450823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126898043486089558530404389 23793383153641792224450823)
      ·
        refine ⟨35690074730462688336676235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23793383153641792224450823 35690074730462688336676235)
        ·
          refine ⟨53535112095694032505014353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35690074730462688336676235 53535112095694032505014353)
          ·
            refine ⟨40151334071770524378760765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53535112095694032505014353 40151334071770524378760765)
            ·
              refine ⟨15056750276913946642035287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40151334071770524378760765 15056750276913946642035287)
              ·
                refine ⟨22585125415370919963052931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15056750276913946642035287 22585125415370919963052931)
                ·
                  refine ⟨33877688123056379944579397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22585125415370919963052931 33877688123056379944579397)
                  ·
                    refine ⟨6352066523073071239608637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33877688123056379944579397 6352066523073071239608637)
                    ·
                      refine ⟨2382024946152401714853239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6352066523073071239608637 2382024946152401714853239)
                      ·
                        rfl

theorem cell23_4638977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_4638977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638977 prefixEnd_4638977 := by exact prefixLift 4638977
  have htrace : WordTrace (prefixWord ++ tailWord_4638977) baseStart_4638977 baseEnd_4638977 := by
    simpa [prefixWord, tailWord_4638977, baseEnd_4638977] using wordTrace_append hprefix tailTrace_4638977
  have hstable : (prefixWord ++ tailWord_4638977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638977).length < 2 ^ (prefixWord ++ tailWord_4638977).sum := by decide
  have hdescent : baseEnd_4638977 < baseStart_4638977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4638997 : List Nat := [1, 3, 2, 1, 2, 1, 5, 2, 6]
def baseStart_4638997 : Nat := 118140960795 + 4638997 * 2 ^ 59
def prefixEnd_4638997 : Nat := 4983230072969 + 3 ^ 40 * 4638997 * 2
def baseEnd_4638997 : Nat := 264670579529499070733683

theorem tailTrace_4638997 : CollatzResearch.WordTrace tailWord_4638997 prefixEnd_4638997 264670579529499070733683 := by
  unfold tailWord_4638997
  simp only [CollatzResearch.WordTrace]
  refine ⟨169198120774713621456267245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112798747183142414304178163 169198120774713621456267245)
  ·
    refine ⟨63449295290517608046100217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169198120774713621456267245 63449295290517608046100217)
    ·
      refine ⟨47586971467888206034575163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63449295290517608046100217 47586971467888206034575163)
      ·
        refine ⟨71380457201832309051862745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47586971467888206034575163 71380457201832309051862745)
        ·
          refine ⟨53535342901374231788897059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71380457201832309051862745 53535342901374231788897059)
          ·
            refine ⟨80303014352061347683345589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53535342901374231788897059 80303014352061347683345589)
            ·
              refine ⟨7528407595505751345313649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80303014352061347683345589 7528407595505751345313649)
              ·
                refine ⟨5646305696629313508985237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7528407595505751345313649 5646305696629313508985237)
                ·
                  refine ⟨264670579529499070733683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5646305696629313508985237 264670579529499070733683)
                  ·
                    rfl

theorem cell23_4638997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_4638997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4638997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4638997 prefixEnd_4638997 := by exact prefixLift 4638997
  have htrace : WordTrace (prefixWord ++ tailWord_4638997) baseStart_4638997 baseEnd_4638997 := by
    simpa [prefixWord, tailWord_4638997, baseEnd_4638997] using wordTrace_append hprefix tailTrace_4638997
  have hstable : (prefixWord ++ tailWord_4638997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4638997).length < 2 ^ (prefixWord ++ tailWord_4638997).sum := by decide
  have hdescent : baseEnd_4638997 < baseStart_4638997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4638997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639000 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_4639000 : Nat := 118140960795 + 4639000 * 2 ^ 59
def prefixEnd_4639000 : Nat := 4983230072969 + 3 ^ 40 * 4639000 * 2
def baseEnd_4639000 : Nat := 2382036756207455124865633

theorem tailTrace_4639000 : CollatzResearch.WordTrace tailWord_4639000 prefixEnd_4639000 2382036756207455124865633 := by
  unfold tailWord_4639000
  simp only [CollatzResearch.WordTrace]
  refine ⟨84599115096851376484313227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112798820129135168645750969 84599115096851376484313227)
  ·
    refine ⟨126898672645277064726469841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84599115096851376484313227 126898672645277064726469841)
    ·
      refine ⟨95174004483957798544852381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126898672645277064726469841 95174004483957798544852381)
      ·
        refine ⟨35690251681484174454319643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95174004483957798544852381 35690251681484174454319643)
        ·
          refine ⟨53535377522226261681479465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35690251681484174454319643 53535377522226261681479465)
          ·
            refine ⟨40151533141669696261109599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53535377522226261681479465 40151533141669696261109599)
            ·
              refine ⟨60227299712504544391664399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40151533141669696261109599 60227299712504544391664399)
              ·
                refine ⟨90340949568756816587496599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60227299712504544391664399 90340949568756816587496599)
                ·
                  refine ⟨135511424353135224881244899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90340949568756816587496599 135511424353135224881244899)
                  ·
                    refine ⟨203267136529702837321867349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 135511424353135224881244899 203267136529702837321867349)
                    ·
                      refine ⟨2382036756207455124865633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 203267136529702837321867349 2382036756207455124865633)
                      ·
                        rfl

theorem cell23_4639000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_4639000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639000 prefixEnd_4639000 := by exact prefixLift 4639000
  have htrace : WordTrace (prefixWord ++ tailWord_4639000) baseStart_4639000 baseEnd_4639000 := by
    simpa [prefixWord, tailWord_4639000, baseEnd_4639000] using wordTrace_append hprefix tailTrace_4639000
  have hstable : (prefixWord ++ tailWord_4639000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639000).length < 2 ^ (prefixWord ++ tailWord_4639000).sum := by decide
  have hdescent : baseEnd_4639000 < baseStart_4639000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639020 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_4639020 : Nat := 118140960795 + 4639020 * 2 ^ 59
def prefixEnd_4639020 : Nat := 4983230072969 + 3 ^ 40 * 4639020 * 2
def baseEnd_4639020 : Nat := 2382047025820545046615541

theorem tailTrace_4639020 : CollatzResearch.WordTrace tailWord_4639020 prefixEnd_4639020 2382047025820545046615541 := by
  unfold tailWord_4639020
  simp only [CollatzResearch.WordTrace]
  refine ⟨84599479826815148192177257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112799306435753530922903009 84599479826815148192177257)
  ·
    refine ⟨63449609870111361144132943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84599479826815148192177257 63449609870111361144132943)
    ·
      refine ⟨95174414805167041716199415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63449609870111361144132943 95174414805167041716199415)
      ·
        refine ⟨142761622207750562574299123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95174414805167041716199415 142761622207750562574299123)
        ·
          refine ⟨214142433311625843861448685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142761622207750562574299123 214142433311625843861448685)
          ·
            refine ⟨80303412491859691448043257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214142433311625843861448685 80303412491859691448043257)
            ·
              refine ⟨60227559368894768586032443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80303412491859691448043257 60227559368894768586032443)
              ·
                refine ⟨90341339053342152879048665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60227559368894768586032443 90341339053342152879048665)
                ·
                  refine ⟨67756004290006614659286499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90341339053342152879048665 67756004290006614659286499)
                  ·
                    refine ⟨101634006435009921988929749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67756004290006614659286499 101634006435009921988929749)
                    ·
                      refine ⟨2382047025820545046615541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101634006435009921988929749 2382047025820545046615541)
                      ·
                        rfl

theorem cell23_4639020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_4639020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639020 prefixEnd_4639020 := by exact prefixLift 4639020
  have htrace : WordTrace (prefixWord ++ tailWord_4639020) baseStart_4639020 baseEnd_4639020 := by
    simpa [prefixWord, tailWord_4639020, baseEnd_4639020] using wordTrace_append hprefix tailTrace_4639020
  have hstable : (prefixWord ++ tailWord_4639020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639020).length < 2 ^ (prefixWord ++ tailWord_4639020).sum := by decide
  have hdescent : baseEnd_4639020 < baseStart_4639020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639034 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2]
def baseStart_4639034 : Nat := 118140960795 + 4639034 * 2 ^ 59
def prefixEnd_4639034 : Nat := 4983230072969 + 3 ^ 40 * 4639034 * 2
def baseEnd_4639034 : Nat := 2382054214549707991840477

theorem tailTrace_4639034 : CollatzResearch.WordTrace tailWord_4639034 prefixEnd_4639034 2382054214549707991840477 := by
  unfold tailWord_4639034
  simp only [CollatzResearch.WordTrace]
  refine ⟨42299867568894894193841039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112799646850386384516909437 42299867568894894193841039)
  ·
    refine ⟨63449801353342341290761559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42299867568894894193841039 63449801353342341290761559)
    ·
      refine ⟨95174702030013511936142339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63449801353342341290761559 95174702030013511936142339)
      ·
        refine ⟨142762053045020267904213509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95174702030013511936142339 142762053045020267904213509)
        ·
          refine ⟨26767884945941300232040033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142762053045020267904213509 26767884945941300232040033)
          ·
            refine ⟨20075913709455975174030025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26767884945941300232040033 20075913709455975174030025)
            ·
              refine ⟨15056935282091981380522519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20075913709455975174030025 15056935282091981380522519)
              ·
                refine ⟨22585402923137972070783779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15056935282091981380522519 22585402923137972070783779)
                ·
                  refine ⟨33878104384706958106175669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22585402923137972070783779 33878104384706958106175669)
                  ·
                    refine ⟨3176072286066277322453969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33878104384706958106175669 3176072286066277322453969)
                    ·
                      refine ⟨2382054214549707991840477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176072286066277322453969 2382054214549707991840477)
                      ·
                        rfl

theorem cell23_4639034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2].length) (baseStart_4639034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639034 prefixEnd_4639034 := by exact prefixLift 4639034
  have htrace : WordTrace (prefixWord ++ tailWord_4639034) baseStart_4639034 baseEnd_4639034 := by
    simpa [prefixWord, tailWord_4639034, baseEnd_4639034] using wordTrace_append hprefix tailTrace_4639034
  have hstable : (prefixWord ++ tailWord_4639034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639034).length < 2 ^ (prefixWord ++ tailWord_4639034).sum := by decide
  have hdescent : baseEnd_4639034 < baseStart_4639034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639077 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_4639077 : Nat := 118140960795 + 4639077 * 2 ^ 59
def prefixEnd_4639077 : Nat := 4983230072969 + 3 ^ 40 * 4639077 * 2
def baseEnd_4639077 : Nat := 2382076294217851323602779

theorem tailTrace_4639077 : CollatzResearch.WordTrace tailWord_4639077 prefixEnd_4639077 2382076294217851323602779 := by
  unfold tailWord_4639077
  simp only [CollatzResearch.WordTrace]
  refine ⟨169201038614423795119179485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112800692409615863412786323 169201038614423795119179485)
  ·
    refine ⟨63450389480408923169692307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169201038614423795119179485 63450389480408923169692307)
    ·
      refine ⟨95175584220613384754538461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63450389480408923169692307 95175584220613384754538461)
      ·
        refine ⟨35690844082730019282951923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95175584220613384754538461 35690844082730019282951923)
        ·
          refine ⟨53536266124095028924427885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35690844082730019282951923 53536266124095028924427885)
          ·
            refine ⟨20076099796535635846660457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53536266124095028924427885 20076099796535635846660457)
            ·
              refine ⟨15057074847401726884995343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20076099796535635846660457 15057074847401726884995343)
              ·
                refine ⟨22585612271102590327493015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15057074847401726884995343 22585612271102590327493015)
                ·
                  refine ⟨33878418406653885491239523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22585612271102590327493015 33878418406653885491239523)
                  ·
                    refine ⟨50817627609980828236859285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33878418406653885491239523 50817627609980828236859285)
                    ·
                      refine ⟨2382076294217851323602779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50817627609980828236859285 2382076294217851323602779)
                      ·
                        rfl

theorem cell23_4639077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_4639077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639077 prefixEnd_4639077 := by exact prefixLift 4639077
  have htrace : WordTrace (prefixWord ++ tailWord_4639077) baseStart_4639077 baseEnd_4639077 := by
    simpa [prefixWord, tailWord_4639077, baseEnd_4639077] using wordTrace_append hprefix tailTrace_4639077
  have hstable : (prefixWord ++ tailWord_4639077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639077).length < 2 ^ (prefixWord ++ tailWord_4639077).sum := by decide
  have hdescent : baseEnd_4639077 < baseStart_4639077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639115 : List Nat := [1, 1, 1, 1, 4, 4, 4, 2, 1, 2, 2]
def baseStart_4639115 : Nat := 118140960795 + 4639115 * 2 ^ 59
def prefixEnd_4639115 : Nat := 4983230072969 + 3 ^ 40 * 4639115 * 2
def baseEnd_4639115 : Nat := 2382095806482722174927605

theorem tailTrace_4639115 : CollatzResearch.WordTrace tailWord_4639115 prefixEnd_4639115 2382095806482722174927605 := by
  unfold tailWord_4639115
  simp only [CollatzResearch.WordTrace]
  refine ⟨169202424588286127609062799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112801616392190751739375199 169202424588286127609062799)
  ·
    refine ⟨253803636882429191413594199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169202424588286127609062799 253803636882429191413594199)
    ·
      refine ⟨380705455323643787120391299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253803636882429191413594199 380705455323643787120391299)
      ·
        refine ⟨571058182985465680680586949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380705455323643787120391299 571058182985465680680586949)
        ·
          refine ⟨107073409309774815127610053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 571058182985465680680586949 107073409309774815127610053)
          ·
            refine ⟨20076264245582777836426885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107073409309774815127610053 20076264245582777836426885)
            ·
              refine ⟨3764299546046770844330041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20076264245582777836426885 3764299546046770844330041)
              ·
                refine ⟨2823224659535078133247531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3764299546046770844330041 2823224659535078133247531)
                ·
                  refine ⟨4234836989302617199871297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823224659535078133247531 4234836989302617199871297)
                  ·
                    refine ⟨3176127741976962899903473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4234836989302617199871297 3176127741976962899903473)
                    ·
                      refine ⟨2382095806482722174927605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176127741976962899903473 2382095806482722174927605)
                      ·
                        rfl

theorem cell23_4639115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 1, 2, 2].length) (baseStart_4639115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639115 prefixEnd_4639115 := by exact prefixLift 4639115
  have htrace : WordTrace (prefixWord ++ tailWord_4639115) baseStart_4639115 baseEnd_4639115 := by
    simpa [prefixWord, tailWord_4639115, baseEnd_4639115] using wordTrace_append hprefix tailTrace_4639115
  have hstable : (prefixWord ++ tailWord_4639115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639115).length < 2 ^ (prefixWord ++ tailWord_4639115).sum := by decide
  have hdescent : baseEnd_4639115 < baseStart_4639115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639141 : List Nat := [1, 3, 1, 2, 1, 1, 4, 4, 1, 3, 2]
def baseStart_4639141 : Nat := 118140960795 + 4639141 * 2 ^ 59
def prefixEnd_4639141 : Nat := 4983230072969 + 3 ^ 40 * 4639141 * 2
def baseEnd_4639141 : Nat := 2382109156979739073202485

theorem tailTrace_4639141 : CollatzResearch.WordTrace tailWord_4639141 prefixEnd_4639141 2382109156979739073202485 := by
  unfold tailWord_4639141
  simp only [CollatzResearch.WordTrace]
  refine ⟨169203372886191934049509277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112802248590794622699672851 169203372886191934049509277)
  ·
    refine ⟨63451264832321975268565979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169203372886191934049509277 63451264832321975268565979)
    ·
      refine ⟨95176897248482962902848969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63451264832321975268565979 95176897248482962902848969)
      ·
        refine ⟨71382672936362222177136727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95176897248482962902848969 71382672936362222177136727)
        ·
          refine ⟨107074009404543333265705091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71382672936362222177136727 107074009404543333265705091)
          ·
            refine ⟨160611014106814999898557637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107074009404543333265705091 160611014106814999898557637)
            ·
              refine ⟨30114565145027812480979557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160611014106814999898557637 30114565145027812480979557)
              ·
                refine ⟨5646480964692714840183667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30114565145027812480979557 5646480964692714840183667)
                ·
                  refine ⟨8469721447039072260275501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5646480964692714840183667 8469721447039072260275501)
                  ·
                    refine ⟨3176145542639652097603313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8469721447039072260275501 3176145542639652097603313)
                    ·
                      refine ⟨2382109156979739073202485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176145542639652097603313 2382109156979739073202485)
                      ·
                        rfl

theorem cell23_4639141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_4639141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639141 prefixEnd_4639141 := by exact prefixLift 4639141
  have htrace : WordTrace (prefixWord ++ tailWord_4639141) baseStart_4639141 baseEnd_4639141 := by
    simpa [prefixWord, tailWord_4639141, baseEnd_4639141] using wordTrace_append hprefix tailTrace_4639141
  have hstable : (prefixWord ++ tailWord_4639141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639141).length < 2 ^ (prefixWord ++ tailWord_4639141).sum := by decide
  have hdescent : baseEnd_4639141 < baseStart_4639141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639164 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 2, 6]
def baseStart_4639164 : Nat := 118140960795 + 4639164 * 2 ^ 59
def prefixEnd_4639164 : Nat := 4983230072969 + 3 ^ 40 * 4639164 * 2
def baseEnd_4639164 : Nat := 794040322344930827738293

theorem tailTrace_4639164 : CollatzResearch.WordTrace tailWord_4639164 prefixEnd_4639164 794040322344930827738293 := by
  unfold tailWord_4639164
  simp only [CollatzResearch.WordTrace]
  refine ⟨84602105882554304488798273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112802807843405739318397697 84602105882554304488798273)
  ·
    refine ⟨63451579411915728366598705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84602105882554304488798273 63451579411915728366598705)
    ·
      refine ⟨47588684558936796274949029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63451579411915728366598705 47588684558936796274949029)
      ·
        refine ⟨8922878354800649301552943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47588684558936796274949029 8922878354800649301552943)
        ·
          refine ⟨13384317532200973952329415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8922878354800649301552943 13384317532200973952329415)
          ·
            refine ⟨20076476298301460928494123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13384317532200973952329415 20076476298301460928494123)
            ·
              refine ⟨30114714447452191392741185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20076476298301460928494123 30114714447452191392741185)
              ·
                refine ⟨22586035835589143544555889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30114714447452191392741185 22586035835589143544555889)
                ·
                  refine ⟨16939526876691857658416917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22586035835589143544555889 16939526876691857658416917)
                  ·
                    refine ⟨794040322344930827738293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16939526876691857658416917 794040322344930827738293)
                    ·
                      rfl

theorem cell23_4639164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_4639164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639164 prefixEnd_4639164 := by exact prefixLift 4639164
  have htrace : WordTrace (prefixWord ++ tailWord_4639164) baseStart_4639164 baseEnd_4639164 := by
    simpa [prefixWord, tailWord_4639164, baseEnd_4639164] using wordTrace_append hprefix tailTrace_4639164
  have hstable : (prefixWord ++ tailWord_4639164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639164).length < 2 ^ (prefixWord ++ tailWord_4639164).sum := by decide
  have hdescent : baseEnd_4639164 < baseStart_4639164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639177 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 7]
def baseStart_4639177 : Nat := 118140960795 + 4639177 * 2 ^ 59
def prefixEnd_4639177 : Nat := 4983230072969 + 3 ^ 40 * 4639177 * 2
def baseEnd_4639177 : Nat := 264680849142588992483591

theorem tailTrace_4639177 : CollatzResearch.WordTrace tailWord_4639177 prefixEnd_4639177 264680849142588992483591 := by
  unfold tailWord_4639177
  simp only [CollatzResearch.WordTrace]
  refine ⟨169204685914061512197819785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112803123942707674798546523 169204685914061512197819785)
  ·
    refine ⟨126903514435546134148364839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169204685914061512197819785 126903514435546134148364839)
    ·
      refine ⟨190355271653319201222547259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126903514435546134148364839 190355271653319201222547259)
      ·
        refine ⟨285532907479978801833820889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190355271653319201222547259 285532907479978801833820889)
        ·
          refine ⟨214149680609984101375365667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285532907479978801833820889 214149680609984101375365667)
          ·
            refine ⟨321224520914976152063048501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214149680609984101375365667 321224520914976152063048501)
            ·
              refine ⟨30114798835779014255910797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 321224520914976152063048501 30114798835779014255910797)
              ·
                refine ⟨11293049563417130345966549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30114798835779014255910797 11293049563417130345966549)
                ·
                  refine ⟨264680849142588992483591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11293049563417130345966549 264680849142588992483591)
                  ·
                    rfl

theorem cell23_4639177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 7].length) (baseStart_4639177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639177 prefixEnd_4639177 := by exact prefixLift 4639177
  have htrace : WordTrace (prefixWord ++ tailWord_4639177) baseStart_4639177 baseEnd_4639177 := by
    simpa [prefixWord, tailWord_4639177, baseEnd_4639177] using wordTrace_append hprefix tailTrace_4639177
  have hstable : (prefixWord ++ tailWord_4639177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639177).length < 2 ^ (prefixWord ++ tailWord_4639177).sum := by decide
  have hdescent : baseEnd_4639177 < baseStart_4639177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639188 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_4639188 : Nat := 118140960795 + 4639188 * 2 ^ 59
def prefixEnd_4639188 : Nat := 4983230072969 + 3 ^ 40 * 4639188 * 2
def baseEnd_4639188 : Nat := 2382133290570500389314769

theorem tailTrace_4639188 : CollatzResearch.WordTrace tailWord_4639188 prefixEnd_4639188 2382133290570500389314769 := by
  unfold tailWord_4639188
  simp only [CollatzResearch.WordTrace]
  refine ⟨84602543558510830538235109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112803391411347774050980145 84602543558510830538235109)
  ·
    refine ⟨15862976917220780725919083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84602543558510830538235109 15862976917220780725919083)
    ·
      refine ⟨23794465375831171088878625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15862976917220780725919083 23794465375831171088878625)
      ·
        refine ⟨17845849031873378316658969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23794465375831171088878625 17845849031873378316658969)
        ·
          refine ⟨13384386773905033737494227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17845849031873378316658969 13384386773905033737494227)
          ·
            refine ⟨20076580160857550606241341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13384386773905033737494227 20076580160857550606241341)
            ·
              refine ⟨7528717560321581477340503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20076580160857550606241341 7528717560321581477340503)
              ·
                refine ⟨11293076340482372216010755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7528717560321581477340503 11293076340482372216010755)
                ·
                  refine ⟨16939614510723558324016133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11293076340482372216010755 16939614510723558324016133)
                  ·
                    refine ⟨3176177720760667185753025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16939614510723558324016133 3176177720760667185753025)
                    ·
                      refine ⟨2382133290570500389314769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176177720760667185753025 2382133290570500389314769)
                      ·
                        rfl

theorem cell23_4639188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_4639188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639188 prefixEnd_4639188 := by exact prefixLift 4639188
  have htrace : WordTrace (prefixWord ++ tailWord_4639188) baseStart_4639188 baseEnd_4639188 := by
    simpa [prefixWord, tailWord_4639188, baseEnd_4639188] using wordTrace_append hprefix tailTrace_4639188
  have hstable : (prefixWord ++ tailWord_4639188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639188).length < 2 ^ (prefixWord ++ tailWord_4639188).sum := by decide
  have hdescent : baseEnd_4639188 < baseStart_4639188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639224 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 2, 5]
def baseStart_4639224 : Nat := 118140960795 + 4639224 * 2 ^ 59
def prefixEnd_4639224 : Nat := 4983230072969 + 3 ^ 40 * 4639224 * 2
def baseEnd_4639224 : Nat := 794050591958020749488201

theorem tailTrace_4639224 : CollatzResearch.WordTrace tailWord_4639224 prefixEnd_4639224 794050591958020749488201 := by
  unfold tailWord_4639224
  simp only [CollatzResearch.WordTrace]
  refine ⟨84603200072445619612390363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112804266763260826149853817 84603200072445619612390363)
  ·
    refine ⟨126904800108668429418585545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84603200072445619612390363 126904800108668429418585545)
    ·
      refine ⟨95178600081501322063939159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126904800108668429418585545 95178600081501322063939159)
      ·
        refine ⟨142767900122251983095908739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95178600081501322063939159 142767900122251983095908739)
        ·
          refine ⟨214151850183377974643863109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142767900122251983095908739 214151850183377974643863109)
          ·
            refine ⟨40153471909383370245724333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214151850183377974643863109 40153471909383370245724333)
            ·
              refine ⟨15057551966018763842146625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40153471909383370245724333 15057551966018763842146625)
              ·
                refine ⟨11293163974514072881609969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15057551966018763842146625 11293163974514072881609969)
                ·
                  refine ⟨8469872980885554661207477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11293163974514072881609969 8469872980885554661207477)
                  ·
                    refine ⟨794050591958020749488201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8469872980885554661207477 794050591958020749488201)
                    ·
                      rfl

theorem cell23_4639224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_4639224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639224 prefixEnd_4639224 := by exact prefixLift 4639224
  have htrace : WordTrace (prefixWord ++ tailWord_4639224) baseStart_4639224 baseEnd_4639224 := by
    simpa [prefixWord, tailWord_4639224, baseEnd_4639224] using wordTrace_append hprefix tailTrace_4639224
  have hstable : (prefixWord ++ tailWord_4639224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639224).length < 2 ^ (prefixWord ++ tailWord_4639224).sum := by decide
  have hdescent : baseEnd_4639224 < baseStart_4639224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639239 : List Nat := [1, 1, 4, 3, 4, 1, 2, 1, 2, 2, 2]
def baseStart_4639239 : Nat := 118140960795 + 4639239 * 2 ^ 59
def prefixEnd_4639239 : Nat := 4983230072969 + 3 ^ 40 * 4639239 * 2
def baseEnd_4639239 : Nat := 2382159478083879689777035

theorem tailTrace_4639239 : CollatzResearch.WordTrace tailWord_4639239 prefixEnd_4639239 2382159478083879689777035 := by
  unfold tailWord_4639239
  simp only [CollatzResearch.WordTrace]
  refine ⟨169206947239836896786576771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112804631493224597857717847 169206947239836896786576771)
  ·
    refine ⟨253810420859755345179865157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169206947239836896786576771 253810420859755345179865157)
    ·
      refine ⟨47589453911204127221224717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 253810420859755345179865157 47589453911204127221224717)
      ·
        refine ⟨17846045216701547707959269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47589453911204127221224717 17846045216701547707959269)
        ·
          refine ⟨3346133478131540195242363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17846045216701547707959269 3346133478131540195242363)
          ·
            refine ⟨5019200217197310292863545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346133478131540195242363 5019200217197310292863545)
            ·
              refine ⟨3764400162897982719647659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5019200217197310292863545 3764400162897982719647659)
              ·
                refine ⟨5646600244346974079471489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3764400162897982719647659 5646600244346974079471489)
                ·
                  refine ⟨4234950183260230559603617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5646600244346974079471489 4234950183260230559603617)
                  ·
                    refine ⟨3176212637445172919702713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4234950183260230559603617 3176212637445172919702713)
                    ·
                      refine ⟨2382159478083879689777035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176212637445172919702713 2382159478083879689777035)
                      ·
                        rfl

theorem cell23_4639239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_4639239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639239 prefixEnd_4639239 := by exact prefixLift 4639239
  have htrace : WordTrace (prefixWord ++ tailWord_4639239) baseStart_4639239 baseEnd_4639239 := by
    simpa [prefixWord, tailWord_4639239, baseEnd_4639239] using wordTrace_append hprefix tailTrace_4639239
  have hstable : (prefixWord ++ tailWord_4639239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639239).length < 2 ^ (prefixWord ++ tailWord_4639239).sum := by decide
  have hdescent : baseEnd_4639239 < baseStart_4639239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639261 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_4639261 : Nat := 118140960795 + 4639261 * 2 ^ 59
def prefixEnd_4639261 : Nat := 4983230072969 + 3 ^ 40 * 4639261 * 2
def baseEnd_4639261 : Nat := 2382170774658278603701933

theorem tailTrace_4639261 : CollatzResearch.WordTrace tailWord_4639261 prefixEnd_4639261 2382170774658278603701933 := by
  unfold tailWord_4639261
  simp only [CollatzResearch.WordTrace]
  refine ⟨169207749645757194543877637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112805166430504796362585091 169207749645757194543877637)
  ·
    refine ⟨31726453058579473976977057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169207749645757194543877637 31726453058579473976977057)
    ·
      refine ⟨23794839793934605482732793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31726453058579473976977057 23794839793934605482732793)
      ·
        refine ⟨17846129845450954112049595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23794839793934605482732793 17846129845450954112049595)
        ·
          refine ⟨26769194768176431168074393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17846129845450954112049595 26769194768176431168074393)
          ·
            refine ⟨20076896076132323376055795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26769194768176431168074393 20076896076132323376055795)
            ·
              refine ⟨30115344114198485064083693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20076896076132323376055795 30115344114198485064083693)
              ·
                refine ⟨11293254042824431899031385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30115344114198485064083693 11293254042824431899031385)
                ·
                  refine ⟨8469940532118323924273539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11293254042824431899031385 8469940532118323924273539)
                  ·
                    refine ⟨12704910798177485886410309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8469940532118323924273539 12704910798177485886410309)
                    ·
                      refine ⟨2382170774658278603701933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12704910798177485886410309 2382170774658278603701933)
                      ·
                        rfl

theorem cell23_4639261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_4639261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639261 prefixEnd_4639261 := by exact prefixLift 4639261
  have htrace : WordTrace (prefixWord ++ tailWord_4639261) baseStart_4639261 baseEnd_4639261 := by
    simpa [prefixWord, tailWord_4639261, baseEnd_4639261] using wordTrace_append hprefix tailTrace_4639261
  have hstable : (prefixWord ++ tailWord_4639261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639261).length < 2 ^ (prefixWord ++ tailWord_4639261).sum := by decide
  have hdescent : baseEnd_4639261 < baseStart_4639261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639281 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 2, 2, 3]
def baseStart_4639281 : Nat := 118140960795 + 4639281 * 2 ^ 59
def prefixEnd_4639281 : Nat := 4983230072969 + 3 ^ 40 * 4639281 * 2
def baseEnd_4639281 : Nat := 2382181044271368525451841

theorem tailTrace_4639281 : CollatzResearch.WordTrace tailWord_4639281 prefixEnd_4639281 2382181044271368525451841 := by
  unfold tailWord_4639281
  simp only [CollatzResearch.WordTrace]
  refine ⟨169208479105684737959605697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112805652737123158639737131 169208479105684737959605697)
  ·
    refine ⟨126906359329263553469704273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169208479105684737959605697 126906359329263553469704273)
    ·
      refine ⟨95179769496947665102278205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126906359329263553469704273 95179769496947665102278205)
      ·
        refine ⟨35692413561355374413354327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95179769496947665102278205 35692413561355374413354327)
        ·
          refine ⟨53538620342033061620031491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35692413561355374413354327 53538620342033061620031491)
          ·
            refine ⟨80307930513049592430047237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53538620342033061620031491 80307930513049592430047237)
            ·
              refine ⟨15057736971196798580633857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80307930513049592430047237 15057736971196798580633857)
              ·
                refine ⟨11293302728397598935475393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15057736971196798580633857 11293302728397598935475393)
                ·
                  refine ⟨8469977046298199201606545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11293302728397598935475393 8469977046298199201606545)
                  ·
                    refine ⟨6352482784723649401204909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8469977046298199201606545 6352482784723649401204909)
                    ·
                      refine ⟨2382181044271368525451841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6352482784723649401204909 2382181044271368525451841)
                      ·
                        rfl

theorem cell23_4639281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_4639281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639281 prefixEnd_4639281 := by exact prefixLift 4639281
  have htrace : WordTrace (prefixWord ++ tailWord_4639281) baseStart_4639281 baseEnd_4639281 := by
    simpa [prefixWord, tailWord_4639281, baseEnd_4639281] using wordTrace_append hprefix tailTrace_4639281
  have hstable : (prefixWord ++ tailWord_4639281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639281).length < 2 ^ (prefixWord ++ tailWord_4639281).sum := by decide
  have hdescent : baseEnd_4639281 < baseStart_4639281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639288 : List Nat := [2, 1, 2, 1, 4, 1, 3, 4, 1, 4]
def baseStart_4639288 : Nat := 118140960795 + 4639288 * 2 ^ 59
def prefixEnd_4639288 : Nat := 4983230072969 + 3 ^ 40 * 4639288 * 2
def baseEnd_4639288 : Nat := 794061546211983332688103

theorem tailTrace_4639288 : CollatzResearch.WordTrace tailWord_4639288 prefixEnd_4639288 794061546211983332688103 := by
  unfold tailWord_4639288
  simp only [CollatzResearch.WordTrace]
  refine ⟨84604367208329689077555259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112805822944439585436740345 84604367208329689077555259)
  ·
    refine ⟨126906550812494533616332889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84604367208329689077555259 126906550812494533616332889)
    ·
      refine ⟨95179913109370900212249667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126906550812494533616332889 95179913109370900212249667)
      ·
        refine ⟨142769869664056350318374501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95179913109370900212249667 142769869664056350318374501)
        ·
          refine ⟨26769350562010565684695219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142769869664056350318374501 26769350562010565684695219)
          ·
            refine ⟨40154025843015848527042829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26769350562010565684695219 40154025843015848527042829)
            ·
              refine ⟨15057759691130943197641061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40154025843015848527042829 15057759691130943197641061)
              ·
                refine ⟨2823329942087051849557699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15057759691130943197641061 2823329942087051849557699)
                ·
                  refine ⟨4234994913130577774336549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823329942087051849557699 4234994913130577774336549)
                  ·
                    refine ⟨794061546211983332688103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4234994913130577774336549 794061546211983332688103)
                    ·
                      rfl

theorem cell23_4639288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_4639288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639288 prefixEnd_4639288 := by exact prefixLift 4639288
  have htrace : WordTrace (prefixWord ++ tailWord_4639288) baseStart_4639288 baseEnd_4639288 := by
    simpa [prefixWord, tailWord_4639288, baseEnd_4639288] using wordTrace_append hprefix tailTrace_4639288
  have hstable : (prefixWord ++ tailWord_4639288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639288).length < 2 ^ (prefixWord ++ tailWord_4639288).sum := by decide
  have hdescent : baseEnd_4639288 < baseStart_4639288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639311 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 5, 1, 3]
def baseStart_4639311 : Nat := 118140960795 + 4639311 * 2 ^ 59
def prefixEnd_4639311 : Nat := 4983230072969 + 3 ^ 40 * 4639311 * 2
def baseEnd_4639311 : Nat := 2382196448691003408076703

theorem tailTrace_4639311 : CollatzResearch.WordTrace tailWord_4639311 prefixEnd_4639311 2382196448691003408076703 := by
  unfold tailWord_4639311
  simp only [CollatzResearch.WordTrace]
  refine ⟨169209573295576053083197787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112806382197050702055465191 169209573295576053083197787)
  ·
    refine ⟨253814359943364079624796681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169209573295576053083197787 253814359943364079624796681)
    ·
      refine ⟨190360769957523059718597511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253814359943364079624796681 190360769957523059718597511)
      ·
        refine ⟨285541154936284589577896267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190360769957523059718597511 285541154936284589577896267)
        ·
          refine ⟨428311732404426884366844401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285541154936284589577896267 428311732404426884366844401)
          ·
            refine ⟨321233799303320163275133301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428311732404426884366844401 321233799303320163275133301)
            ·
              refine ⟨30115668684686265307043747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 321233799303320163275133301 30115668684686265307043747)
              ·
                refine ⟨45173503027029397960565621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30115668684686265307043747 45173503027029397960565621)
                ·
                  refine ⟨4235015908784006058803027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45173503027029397960565621 4235015908784006058803027)
                  ·
                    refine ⟨6352523863176009088204541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4235015908784006058803027 6352523863176009088204541)
                    ·
                      refine ⟨2382196448691003408076703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6352523863176009088204541 2382196448691003408076703)
                      ·
                        rfl

theorem cell23_4639311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 1, 3].length) (baseStart_4639311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639311 prefixEnd_4639311 := by exact prefixLift 4639311
  have htrace : WordTrace (prefixWord ++ tailWord_4639311) baseStart_4639311 baseEnd_4639311 := by
    simpa [prefixWord, tailWord_4639311, baseEnd_4639311] using wordTrace_append hprefix tailTrace_4639311
  have hstable : (prefixWord ++ tailWord_4639311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639311).length < 2 ^ (prefixWord ++ tailWord_4639311).sum := by decide
  have hdescent : baseEnd_4639311 < baseStart_4639311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639331 : List Nat := [1, 1, 1, 5, 1, 2, 3, 3, 1, 5]
def baseStart_4639331 : Nat := 118140960795 + 4639331 * 2 ^ 59
def prefixEnd_4639331 : Nat := 4983230072969 + 3 ^ 40 * 4639331 * 2
def baseEnd_4639331 : Nat := 794068906101364443275537

theorem tailTrace_4639331 : CollatzResearch.WordTrace tailWord_4639331 prefixEnd_4639331 794068906101364443275537 := by
  unfold tailWord_4639331
  simp only [CollatzResearch.WordTrace]
  refine ⟨169210302755503596498925847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112806868503669064332617231 169210302755503596498925847)
  ·
    refine ⟨253815454133255394748388771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169210302755503596498925847 253815454133255394748388771)
    ·
      refine ⟨380723181199883092122583157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253815454133255394748388771 380723181199883092122583157)
      ·
        refine ⟨35692798237489039886492171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 380723181199883092122583157 35692798237489039886492171)
        ·
          refine ⟨53539197356233559829738257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35692798237489039886492171 53539197356233559829738257)
          ·
            refine ⟨40154398017175169872303693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53539197356233559829738257 40154398017175169872303693)
            ·
              refine ⟨15057899256440688702113885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40154398017175169872303693 15057899256440688702113885)
              ·
                refine ⟨5646712221165258263292707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15057899256440688702113885 5646712221165258263292707)
                ·
                  refine ⟨8470068331747887394939061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5646712221165258263292707 8470068331747887394939061)
                  ·
                    refine ⟨794068906101364443275537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8470068331747887394939061 794068906101364443275537)
                    ·
                      rfl

theorem cell23_4639331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 5].length) (baseStart_4639331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639331 prefixEnd_4639331 := by exact prefixLift 4639331
  have htrace : WordTrace (prefixWord ++ tailWord_4639331) baseStart_4639331 baseEnd_4639331 := by
    simpa [prefixWord, tailWord_4639331, baseEnd_4639331] using wordTrace_append hprefix tailTrace_4639331
  have hstable : (prefixWord ++ tailWord_4639331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639331).length < 2 ^ (prefixWord ++ tailWord_4639331).sum := by decide
  have hdescent : baseEnd_4639331 < baseStart_4639331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639338 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_4639338 : Nat := 118140960795 + 4639338 * 2 ^ 59
def prefixEnd_4639338 : Nat := 4983230072969 + 3 ^ 40 * 4639338 * 2
def baseEnd_4639338 : Nat := 2382210312668674802439079

theorem tailTrace_4639338 : CollatzResearch.WordTrace tailWord_4639338 prefixEnd_4639338 2382210312668674802439079 := by
  unfold tailWord_4639338
  simp only [CollatzResearch.WordTrace]
  refine ⟨42302639516619559173607667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112807038710985491129620445 42302639516619559173607667)
  ·
    refine ⟨63453959274929338760411501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42302639516619559173607667 63453959274929338760411501)
    ·
      refine ⟨23795234728098502035154313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63453959274929338760411501 23795234728098502035154313)
      ·
        refine ⟨17846426046073876526365735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23795234728098502035154313 17846426046073876526365735)
        ·
          refine ⟨26769639069110814789548603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17846426046073876526365735 26769639069110814789548603)
          ·
            refine ⟨40154458603666222184322905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26769639069110814789548603 40154458603666222184322905)
            ·
              refine ⟨30115843952749666638242179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40154458603666222184322905 30115843952749666638242179)
              ·
                refine ⟨45173765929124499957363269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30115843952749666638242179 45173765929124499957363269)
                ·
                  refine ⟨8470081111710843742005613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45173765929124499957363269 8470081111710843742005613)
                  ·
                    refine ⟨3176280416891566403252105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8470081111710843742005613 3176280416891566403252105)
                    ·
                      refine ⟨2382210312668674802439079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176280416891566403252105 2382210312668674802439079)
                      ·
                        rfl

theorem cell23_4639338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_4639338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639338 prefixEnd_4639338 := by exact prefixLift 4639338
  have htrace : WordTrace (prefixWord ++ tailWord_4639338) baseStart_4639338 baseEnd_4639338 := by
    simpa [prefixWord, tailWord_4639338, baseEnd_4639338] using wordTrace_append hprefix tailTrace_4639338
  have hstable : (prefixWord ++ tailWord_4639338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639338).length < 2 ^ (prefixWord ++ tailWord_4639338).sum := by decide
  have hdescent : baseEnd_4639338 < baseStart_4639338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639378 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_4639378 : Nat := 118140960795 + 4639378 * 2 ^ 59
def prefixEnd_4639378 : Nat := 4983230072969 + 3 ^ 40 * 4639378 * 2
def baseEnd_4639378 : Nat := 794076950631618215312965

theorem tailTrace_4639378 : CollatzResearch.WordTrace tailWord_4639378 prefixEnd_4639378 794076950631618215312965 := by
  unfold tailWord_4639378
  simp only [CollatzResearch.WordTrace]
  refine ⟨42303004246583330881471697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112808011324222215683924525 42303004246583330881471697)
  ·
    refine ⟨31727253184937498161103773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42303004246583330881471697 31727253184937498161103773)
    ·
      refine ⟨11897719944351561810413915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31727253184937498161103773 11897719944351561810413915)
      ·
        refine ⟨17846579916527342715620873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11897719944351561810413915 17846579916527342715620873)
        ·
          refine ⟨13384934937395507036715655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17846579916527342715620873 13384934937395507036715655)
          ·
            refine ⟨20077402406093260555073483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13384934937395507036715655 20077402406093260555073483)
            ·
              refine ⟨30116103609139890832610225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20077402406093260555073483 30116103609139890832610225)
              ·
                refine ⟨22587077706854918124457669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30116103609139890832610225 22587077706854918124457669)
                ·
                  refine ⟨4235077070035297148335813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22587077706854918124457669 4235077070035297148335813)
                  ·
                    refine ⟨794076950631618215312965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4235077070035297148335813 794076950631618215312965)
                    ·
                      rfl

theorem cell23_4639378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_4639378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639378 prefixEnd_4639378 := by exact prefixLift 4639378
  have htrace : WordTrace (prefixWord ++ tailWord_4639378) baseStart_4639378 baseEnd_4639378 := by
    simpa [prefixWord, tailWord_4639378, baseEnd_4639378] using wordTrace_append hprefix tailTrace_4639378
  have hstable : (prefixWord ++ tailWord_4639378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639378).length < 2 ^ (prefixWord ++ tailWord_4639378).sum := by decide
  have hdescent : baseEnd_4639378 < baseStart_4639378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639388 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_4639388 : Nat := 118140960795 + 4639388 * 2 ^ 59
def prefixEnd_4639388 : Nat := 4983230072969 + 3 ^ 40 * 4639388 * 2
def baseEnd_4639388 : Nat := 2382235986701399606813849

theorem tailTrace_4639388 : CollatzResearch.WordTrace tailWord_4639388 prefixEnd_4639388 2382235986701399606813849 := by
  unfold tailWord_4639388
  simp only [CollatzResearch.WordTrace]
  refine ⟨84606190858148547616875409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112808254477531396822500545 84606190858148547616875409)
  ·
    refine ⟨63454643143611410712656557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84606190858148547616875409 63454643143611410712656557)
    ·
      refine ⟨23795491178854279017246209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63454643143611410712656557 23795491178854279017246209)
      ·
        refine ⟨17846618384140709262934657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23795491178854279017246209 17846618384140709262934657)
        ·
          refine ⟨13384963788105531947200993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17846618384140709262934657 13384963788105531947200993)
          ·
            refine ⟨10038722841079148960400745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13384963788105531947200993 10038722841079148960400745)
            ·
              refine ⟨7529042130809361720300559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10038722841079148960400745 7529042130809361720300559)
              ·
                refine ⟨11293563196214042580450839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7529042130809361720300559 11293563196214042580450839)
                ·
                  refine ⟨16940344794321063870676259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11293563196214042580450839 16940344794321063870676259)
                  ·
                    refine ⟨25410517191481595806014389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16940344794321063870676259 25410517191481595806014389)
                    ·
                      refine ⟨2382235986701399606813849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25410517191481595806014389 2382235986701399606813849)
                      ·
                        rfl

theorem cell23_4639388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_4639388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639388 prefixEnd_4639388 := by exact prefixLift 4639388
  have htrace : WordTrace (prefixWord ++ tailWord_4639388) baseStart_4639388 baseEnd_4639388 := by
    simpa [prefixWord, tailWord_4639388, baseEnd_4639388] using wordTrace_append hprefix tailTrace_4639388
  have hstable : (prefixWord ++ tailWord_4639388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639388).length < 2 ^ (prefixWord ++ tailWord_4639388).sum := by decide
  have hdescent : baseEnd_4639388 < baseStart_4639388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639452 : List Nat := [2, 2, 5, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_4639452 : Nat := 118140960795 + 4639452 * 2 ^ 59
def prefixEnd_4639452 : Nat := 4983230072969 + 3 ^ 40 * 4639452 * 2
def baseEnd_4639452 : Nat := 2382268849463287356413555

theorem tailTrace_4639452 : CollatzResearch.WordTrace tailWord_4639452 prefixEnd_4639452 2382268849463287356413555 := by
  unfold tailWord_4639452
  simp only [CollatzResearch.WordTrace]
  refine ⟨84607357994032617082040305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112809810658710156109387073 84607357994032617082040305)
  ·
    refine ⟨63455518495524462811530229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84607357994032617082040305 63455518495524462811530229)
    ·
      refine ⟨5948954858955418388580959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63455518495524462811530229 5948954858955418388580959)
      ·
        refine ⟨8923432288433127582871439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5948954858955418388580959 8923432288433127582871439)
        ·
          refine ⟨13385148432649691374307159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8923432288433127582871439 13385148432649691374307159)
          ·
            refine ⟨20077722648974537061460739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13385148432649691374307159 20077722648974537061460739)
            ·
              refine ⟨30116583973461805592191109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20077722648974537061460739 30116583973461805592191109)
              ·
                refine ⟨5646859495024088548535833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30116583973461805592191109 5646859495024088548535833)
                ·
                  refine ⟨4235144621268066411401875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5646859495024088548535833 4235144621268066411401875)
                  ·
                    refine ⟨6352716931902099617102813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4235144621268066411401875 6352716931902099617102813)
                    ·
                      refine ⟨2382268849463287356413555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6352716931902099617102813 2382268849463287356413555)
                      ·
                        rfl

theorem cell23_4639452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_4639452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639452 prefixEnd_4639452 := by exact prefixLift 4639452
  have htrace : WordTrace (prefixWord ++ tailWord_4639452) baseStart_4639452 baseEnd_4639452 := by
    simpa [prefixWord, tailWord_4639452, baseEnd_4639452] using wordTrace_append hprefix tailTrace_4639452
  have hstable : (prefixWord ++ tailWord_4639452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639452).length < 2 ^ (prefixWord ++ tailWord_4639452).sum := by decide
  have hdescent : baseEnd_4639452 < baseStart_4639452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639471 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 4]
def baseStart_4639471 : Nat := 118140960795 + 4639471 * 2 ^ 59
def prefixEnd_4639471 : Nat := 4983230072969 + 3 ^ 40 * 4639471 * 2
def baseEnd_4639471 : Nat := 2382278605595722782075967

theorem tailTrace_4639471 : CollatzResearch.WordTrace tailWord_4639471 prefixEnd_4639471 2382278605595722782075967 := by
  unfold tailWord_4639471
  simp only [CollatzResearch.WordTrace]
  refine ⟨169215408974996400409022267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112810272649997600272681511 169215408974996400409022267)
  ·
    refine ⟨253823113462494600613533401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169215408974996400409022267 253823113462494600613533401)
    ·
      refine ⟨190367335096870950460150051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253823113462494600613533401 190367335096870950460150051)
      ·
        refine ⟨285551002645306425690225077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190367335096870950460150051 285551002645306425690225077)
        ·
          refine ⟨26770406497997477408458601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 285551002645306425690225077 26770406497997477408458601)
          ·
            refine ⟨20077804873498108056343951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26770406497997477408458601 20077804873498108056343951)
            ·
              refine ⟨30116707310247162084515927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20077804873498108056343951 30116707310247162084515927)
              ·
                refine ⟨45175060965370743126773891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30116707310247162084515927 45175060965370743126773891)
                ·
                  refine ⟨67762591448056114690160837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45175060965370743126773891 67762591448056114690160837)
                  ·
                    refine ⟨12705485896510521504405157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67762591448056114690160837 12705485896510521504405157)
                    ·
                      refine ⟨2382278605595722782075967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12705485896510521504405157 2382278605595722782075967)
                      ·
                        rfl

theorem cell23_4639471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_4639471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639471 prefixEnd_4639471 := by exact prefixLift 4639471
  have htrace : WordTrace (prefixWord ++ tailWord_4639471) baseStart_4639471 baseEnd_4639471 := by
    simpa [prefixWord, tailWord_4639471, baseEnd_4639471] using wordTrace_append hprefix tailTrace_4639471
  have hstable : (prefixWord ++ tailWord_4639471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639471).length < 2 ^ (prefixWord ++ tailWord_4639471).sum := by decide
  have hdescent : baseEnd_4639471 < baseStart_4639471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639478 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_4639478 : Nat := 118140960795 + 4639478 * 2 ^ 59
def prefixEnd_4639478 : Nat := 4983230072969 + 3 ^ 40 * 4639478 * 2
def baseEnd_4639478 : Nat := 2382282199960304254688435

theorem tailTrace_4639478 : CollatzResearch.WordTrace tailWord_4639478 prefixEnd_4639478 2382282199960304254688435 := by
  unfold tailWord_4639478
  simp only [CollatzResearch.WordTrace]
  refine ⟨10575979017873190037782943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112810442857314027069684725 10575979017873190037782943)
  ·
    refine ⟨15863968526809785056674415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10575979017873190037782943 15863968526809785056674415)
    ·
      refine ⟨23795952790214677585011623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15863968526809785056674415 23795952790214677585011623)
      ·
        refine ⟨35693929185322016377517435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23795952790214677585011623 35693929185322016377517435)
        ·
          refine ⟨53540893777983024566276153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35693929185322016377517435 53540893777983024566276153)
          ·
            refine ⟨40155670333487268424707115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53540893777983024566276153 40155670333487268424707115)
            ·
              refine ⟨60233505500230902637060673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40155670333487268424707115 60233505500230902637060673)
              ·
                refine ⟨45175129125173176977795505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60233505500230902637060673 45175129125173176977795505)
                ·
                  refine ⟨33881346843879882733346629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45175129125173176977795505 33881346843879882733346629)
                  ·
                    refine ⟨6352752533227478012502493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33881346843879882733346629 6352752533227478012502493)
                    ·
                      refine ⟨2382282199960304254688435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6352752533227478012502493 2382282199960304254688435)
                      ·
                        rfl

theorem cell23_4639478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_4639478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639478 prefixEnd_4639478 := by exact prefixLift 4639478
  have htrace : WordTrace (prefixWord ++ tailWord_4639478) baseStart_4639478 baseEnd_4639478 := by
    simpa [prefixWord, tailWord_4639478, baseEnd_4639478] using wordTrace_append hprefix tailTrace_4639478
  have hstable : (prefixWord ++ tailWord_4639478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639478).length < 2 ^ (prefixWord ++ tailWord_4639478).sum := by decide
  have hdescent : baseEnd_4639478 < baseStart_4639478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639491 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 3]
def baseStart_4639491 : Nat := 118140960795 + 4639491 * 2 ^ 59
def prefixEnd_4639491 : Nat := 4983230072969 + 3 ^ 40 * 4639491 * 2
def baseEnd_4639491 : Nat := 2382288875208812703825875

theorem tailTrace_4639491 : CollatzResearch.WordTrace tailWord_4639491 prefixEnd_4639491 2382288875208812703825875 := by
  unfold tailWord_4639491
  simp only [CollatzResearch.WordTrace]
  refine ⟨169216138434923943824750327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112810758956615962549833551 169216138434923943824750327)
  ·
    refine ⟨253824207652385915737125491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169216138434923943824750327 253824207652385915737125491)
    ·
      refine ⟨380736311478578873605688237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253824207652385915737125491 380736311478578873605688237)
      ·
        refine ⟨142776116804467077602133089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 380736311478578873605688237 142776116804467077602133089)
        ·
          refine ⟨107082087603350308201599817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142776116804467077602133089 107082087603350308201599817)
          ·
            refine ⟨80311565702512731151199863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107082087603350308201599817 80311565702512731151199863)
            ·
              refine ⟨120467348553769096726799795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80311565702512731151199863 120467348553769096726799795)
              ·
                refine ⟨180701022830653645090199693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120467348553769096726799795 180701022830653645090199693)
                ·
                  refine ⟨67762883561495116908824885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180701022830653645090199693 67762883561495116908824885)
                  ·
                    refine ⟨6352770333890167210202333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67762883561495116908824885 6352770333890167210202333)
                    ·
                      refine ⟨2382288875208812703825875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6352770333890167210202333 2382288875208812703825875)
                      ·
                        rfl

theorem cell23_4639491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_4639491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639491 prefixEnd_4639491 := by exact prefixLift 4639491
  have htrace : WordTrace (prefixWord ++ tailWord_4639491) baseStart_4639491 baseEnd_4639491 := by
    simpa [prefixWord, tailWord_4639491, baseEnd_4639491] using wordTrace_append hprefix tailTrace_4639491
  have hstable : (prefixWord ++ tailWord_4639491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639491).length < 2 ^ (prefixWord ++ tailWord_4639491).sum := by decide
  have hdescent : baseEnd_4639491 < baseStart_4639491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639521 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_4639521 : Nat := 118140960795 + 4639521 * 2 ^ 59
def prefixEnd_4639521 : Nat := 4983230072969 + 3 ^ 40 * 4639521 * 2
def baseEnd_4639521 : Nat := 2382304279628447586450737

theorem tailTrace_4639521 : CollatzResearch.WordTrace tailWord_4639521 prefixEnd_4639521 2382304279628447586450737 := by
  unfold tailWord_4639521
  simp only [CollatzResearch.WordTrace]
  refine ⟨169217232624815258948342417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112811488416543505965561611 169217232624815258948342417)
  ·
    refine ⟨126912924468611444211256813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169217232624815258948342417 126912924468611444211256813)
    ·
      refine ⟨47592346675729291579221305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126912924468611444211256813 47592346675729291579221305)
      ·
        refine ⟨35694260006796968684415979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47592346675729291579221305 35694260006796968684415979)
        ·
          refine ⟨53541390010195453026623969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35694260006796968684415979 53541390010195453026623969)
          ·
            refine ⟨40156042507646589769967977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53541390010195453026623969 40156042507646589769967977)
            ·
              refine ⟨30117031880734942327475983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40156042507646589769967977 30117031880734942327475983)
              ·
                refine ⟨45175547821102413491213975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30117031880734942327475983 45175547821102413491213975)
                ·
                  refine ⟨67763321731653620236820963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45175547821102413491213975 67763321731653620236820963)
                  ·
                    refine ⟨101644982597480430355231445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67763321731653620236820963 101644982597480430355231445)
                    ·
                      refine ⟨2382304279628447586450737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101644982597480430355231445 2382304279628447586450737)
                      ·
                        rfl

theorem cell23_4639521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_4639521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639521 prefixEnd_4639521 := by exact prefixLift 4639521
  have htrace : WordTrace (prefixWord ++ tailWord_4639521) baseStart_4639521 baseEnd_4639521 := by
    simpa [prefixWord, tailWord_4639521, baseEnd_4639521] using wordTrace_append hprefix tailTrace_4639521
  have hstable : (prefixWord ++ tailWord_4639521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639521).length < 2 ^ (prefixWord ++ tailWord_4639521).sum := by decide
  have hdescent : baseEnd_4639521 < baseStart_4639521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639531 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 4]
def baseStart_4639531 : Nat := 118140960795 + 4639531 * 2 ^ 59
def prefixEnd_4639531 : Nat := 4983230072969 + 3 ^ 40 * 4639531 * 2
def baseEnd_4639531 : Nat := 2382309414434992547325691

theorem tailTrace_4639531 : CollatzResearch.WordTrace tailWord_4639531 prefixEnd_4639531 2382309414434992547325691 := by
  unfold tailWord_4639531
  simp only [CollatzResearch.WordTrace]
  refine ⟨169217597354779030656206447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112811731569852687104137631 169217597354779030656206447)
  ·
    refine ⟨253826396032168545984309671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169217597354779030656206447 253826396032168545984309671)
    ·
      refine ⟨380739594048252818976464507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253826396032168545984309671 380739594048252818976464507)
      ·
        refine ⟨571109391072379228464696761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380739594048252818976464507 571109391072379228464696761)
        ·
          refine ⟨428332043304284421348522571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571109391072379228464696761 428332043304284421348522571)
          ·
            refine ⟨642498064956426632022783857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428332043304284421348522571 642498064956426632022783857)
            ·
              refine ⟨481873548717319974017087893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642498064956426632022783857 481873548717319974017087893)
              ·
                refine ⟨22587822596124373782050995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 481873548717319974017087893 22587822596124373782050995)
                ·
                  refine ⟨33881733894186560673076493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22587822596124373782050995 33881733894186560673076493)
                  ·
                    refine ⟨12705650210319960252403685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33881733894186560673076493 12705650210319960252403685)
                    ·
                      refine ⟨2382309414434992547325691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12705650210319960252403685 2382309414434992547325691)
                      ·
                        rfl

theorem cell23_4639531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 4].length) (baseStart_4639531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639531 prefixEnd_4639531 := by exact prefixLift 4639531
  have htrace : WordTrace (prefixWord ++ tailWord_4639531) baseStart_4639531 baseEnd_4639531 := by
    simpa [prefixWord, tailWord_4639531, baseEnd_4639531] using wordTrace_append hprefix tailTrace_4639531
  have hstable : (prefixWord ++ tailWord_4639531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639531).length < 2 ^ (prefixWord ++ tailWord_4639531).sum := by decide
  have hdescent : baseEnd_4639531 < baseStart_4639531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639548 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_4639548 : Nat := 118140960795 + 4639548 * 2 ^ 59
def prefixEnd_4639548 : Nat := 4983230072969 + 3 ^ 40 * 4639548 * 2
def baseEnd_4639548 : Nat := 2382318143606118980813113

theorem tailTrace_4639548 : CollatzResearch.WordTrace tailWord_4639548 prefixEnd_4639548 2382318143606118980813113 := by
  unfold tailWord_4639548
  simp only [CollatzResearch.WordTrace]
  refine ⟨84609108697858721279787649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112812144930478295039716865 84609108697858721279787649)
  ·
    refine ⟨63456831523394040959840737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84609108697858721279787649 63456831523394040959840737)
    ·
      refine ⟨47592623642545530719880553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63456831523394040959840737 47592623642545530719880553)
      ·
        refine ⟨35694467731909148039910415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47592623642545530719880553 35694467731909148039910415)
        ·
          refine ⟨53541701597863722059865623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35694467731909148039910415 53541701597863722059865623)
          ·
            refine ⟨80312552396795583089798435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53541701597863722059865623 80312552396795583089798435)
            ·
              refine ⟨120468828595193374634697653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80312552396795583089798435 120468828595193374634697653)
              ·
                refine ⟨11293952680799378872002905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120468828595193374634697653 11293952680799378872002905)
                ·
                  refine ⟨8470464510599534154002179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11293952680799378872002905 8470464510599534154002179)
                  ·
                    refine ⟨12705696765899301231003269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8470464510599534154002179 12705696765899301231003269)
                    ·
                      refine ⟨2382318143606118980813113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12705696765899301231003269 2382318143606118980813113)
                      ·
                        rfl

theorem cell23_4639548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_4639548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639548 prefixEnd_4639548 := by exact prefixLift 4639548
  have htrace : WordTrace (prefixWord ++ tailWord_4639548) baseStart_4639548 baseEnd_4639548 := by
    simpa [prefixWord, tailWord_4639548, baseEnd_4639548] using wordTrace_append hprefix tailTrace_4639548
  have hstable : (prefixWord ++ tailWord_4639548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639548).length < 2 ^ (prefixWord ++ tailWord_4639548).sum := by decide
  have hdescent : baseEnd_4639548 < baseStart_4639548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639549 : List Nat := [1, 4, 1, 4, 3, 1, 1, 3, 5]
def baseStart_4639549 : Nat := 118140960795 + 4639549 * 2 ^ 59
def prefixEnd_4639549 : Nat := 4983230072969 + 3 ^ 40 * 4639549 * 2
def baseEnd_4639549 : Nat := 264702073009641497433401

theorem tailTrace_4639549 : CollatzResearch.WordTrace tailWord_4639549 prefixEnd_4639549 264702073009641497433401 := by
  unfold tailWord_4639549
  simp only [CollatzResearch.WordTrace]
  refine ⟨169218253868713819730361701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112812169245809213153574467 169218253868713819730361701)
  ·
    refine ⟨31728422600383841199442819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169218253868713819730361701 31728422600383841199442819)
    ·
      refine ⟨47592633900575761799164229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31728422600383841199442819 47592633900575761799164229)
      ·
        refine ⟨8923618856357955337343293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47592633900575761799164229 8923618856357955337343293)
        ·
          refine ⟨3346357071134233251503735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8923618856357955337343293 3346357071134233251503735)
          ·
            refine ⟨5019535606701349877255603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346357071134233251503735 5019535606701349877255603)
            ·
              refine ⟨7529303410052024815883405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5019535606701349877255603 7529303410052024815883405)
              ·
                refine ⟨2823488778769509305956277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7529303410052024815883405 2823488778769509305956277)
                ·
                  refine ⟨264702073009641497433401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2823488778769509305956277 264702073009641497433401)
                  ·
                    rfl

theorem cell23_4639549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_4639549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639549 prefixEnd_4639549 := by exact prefixLift 4639549
  have htrace : WordTrace (prefixWord ++ tailWord_4639549) baseStart_4639549 baseEnd_4639549 := by
    simpa [prefixWord, tailWord_4639549, baseEnd_4639549] using wordTrace_append hprefix tailTrace_4639549
  have hstable : (prefixWord ++ tailWord_4639549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639549).length < 2 ^ (prefixWord ++ tailWord_4639549).sum := by decide
  have hdescent : baseEnd_4639549 < baseStart_4639549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639568 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 3]
def baseStart_4639568 : Nat := 118140960795 + 4639568 * 2 ^ 59
def prefixEnd_4639568 : Nat := 4983230072969 + 3 ^ 40 * 4639568 * 2
def baseEnd_4639568 : Nat := 2382328413219208902563021

theorem tailTrace_4639568 : CollatzResearch.WordTrace tailWord_4639568 prefixEnd_4639568 2382328413219208902563021 := by
  unfold tailWord_4639568
  simp only [CollatzResearch.WordTrace]
  refine ⟨84609473427822492987651679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112812631237096657316868905 84609473427822492987651679)
  ·
    refine ⟨126914210141733739481477519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84609473427822492987651679 126914210141733739481477519)
    ·
      refine ⟨190371315212600609222216279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126914210141733739481477519 190371315212600609222216279)
      ·
        refine ⟨285556972818900913833324419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190371315212600609222216279 285556972818900913833324419)
        ·
          refine ⟨428335459228351370749986629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285556972818900913833324419 428335459228351370749986629)
          ·
            refine ⟨80312898605315882015622493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 428335459228351370749986629 80312898605315882015622493)
            ·
              refine ⟨30117336976993455755858435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80312898605315882015622493 30117336976993455755858435)
              ·
                refine ⟨45176005465490183633787653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30117336976993455755858435 45176005465490183633787653)
                ·
                  refine ⟨8470501024779409431335185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45176005465490183633787653 8470501024779409431335185)
                  ·
                    refine ⟨6352875768584557073501389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8470501024779409431335185 6352875768584557073501389)
                    ·
                      refine ⟨2382328413219208902563021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6352875768584557073501389 2382328413219208902563021)
                      ·
                        rfl

theorem cell23_4639568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 3].length) (baseStart_4639568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639568 prefixEnd_4639568 := by exact prefixLift 4639568
  have htrace : WordTrace (prefixWord ++ tailWord_4639568) baseStart_4639568 baseEnd_4639568 := by
    simpa [prefixWord, tailWord_4639568, baseEnd_4639568] using wordTrace_append hprefix tailTrace_4639568
  have hstable : (prefixWord ++ tailWord_4639568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639568).length < 2 ^ (prefixWord ++ tailWord_4639568).sum := by decide
  have hdescent : baseEnd_4639568 < baseStart_4639568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639575 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 3, 4]
def baseStart_4639575 : Nat := 118140960795 + 4639575 * 2 ^ 59
def prefixEnd_4639575 : Nat := 4983230072969 + 3 ^ 40 * 4639575 * 2
def baseEnd_4639575 : Nat := 794110669194596791725163

theorem tailTrace_4639575 : CollatzResearch.WordTrace tailWord_4639575 prefixEnd_4639575 794110669194596791725163 := by
  unfold tailWord_4639575
  simp only [CollatzResearch.WordTrace]
  refine ⟨169219202166619626170808179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112812801444413084113872119 169219202166619626170808179)
  ·
    refine ⟨253828803249929439256212269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169219202166619626170808179 253828803249929439256212269)
    ·
      refine ⟨95185801218723539721079601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253828803249929439256212269 95185801218723539721079601)
      ·
        refine ⟨71389350914042654790809701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95185801218723539721079601 71389350914042654790809701)
        ·
          refine ⟨13385503296382997773276819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71389350914042654790809701 13385503296382997773276819)
          ·
            refine ⟨20078254944574496659915229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13385503296382997773276819 20078254944574496659915229)
            ·
              refine ⟨7529345604215436247468211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20078254944574496659915229 7529345604215436247468211)
              ·
                refine ⟨11294018406323154371202317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7529345604215436247468211 11294018406323154371202317)
                ·
                  refine ⟨4235256902371182889200869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11294018406323154371202317 4235256902371182889200869)
                  ·
                    refine ⟨794110669194596791725163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4235256902371182889200869 794110669194596791725163)
                    ·
                      rfl

theorem cell23_4639575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_4639575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639575 prefixEnd_4639575 := by exact prefixLift 4639575
  have htrace : WordTrace (prefixWord ++ tailWord_4639575) baseStart_4639575 baseEnd_4639575 := by
    simpa [prefixWord, tailWord_4639575, baseEnd_4639575] using wordTrace_append hprefix tailTrace_4639575
  have hstable : (prefixWord ++ tailWord_4639575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639575).length < 2 ^ (prefixWord ++ tailWord_4639575).sum := by decide
  have hdescent : baseEnd_4639575 < baseStart_4639575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639626 : List Nat := [3, 1, 2, 4, 1, 3, 2, 2, 1, 4]
def baseStart_4639626 : Nat := 118140960795 + 4639626 * 2 ^ 59
def prefixEnd_4639626 : Nat := 4983230072969 + 3 ^ 40 * 4639626 * 2
def baseEnd_4639626 : Nat := 794119398365723225212585

theorem tailTrace_4639626 : CollatzResearch.WordTrace tailWord_4639626 prefixEnd_4639626 794119398365723225212585 := by
  unfold tailWord_4639626
  simp only [CollatzResearch.WordTrace]
  refine ⟨42305265572358715470228683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112814041526289907920609821 42305265572358715470228683)
  ·
    refine ⟨63457898358538073205343025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42305265572358715470228683 63457898358538073205343025)
    ·
      refine ⟨47593423768903554904007269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63457898358538073205343025 47593423768903554904007269)
      ·
        refine ⟨8923766956669416544501363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47593423768903554904007269 8923766956669416544501363)
        ·
          refine ⟨13385650435004124816752045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8923766956669416544501363 13385650435004124816752045)
          ·
            refine ⟨5019618913126546806282017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13385650435004124816752045 5019618913126546806282017)
            ·
              refine ⟨3764714184844910104711513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5019618913126546806282017 3764714184844910104711513)
              ·
                refine ⟨2823535638633682578533635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3764714184844910104711513 2823535638633682578533635)
                ·
                  refine ⟨4235303457950523867800453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823535638633682578533635 4235303457950523867800453)
                  ·
                    refine ⟨794119398365723225212585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4235303457950523867800453 794119398365723225212585)
                    ·
                      rfl

theorem cell23_4639626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_4639626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639626 prefixEnd_4639626 := by exact prefixLift 4639626
  have htrace : WordTrace (prefixWord ++ tailWord_4639626) baseStart_4639626 baseEnd_4639626 := by
    simpa [prefixWord, tailWord_4639626, baseEnd_4639626] using wordTrace_append hprefix tailTrace_4639626
  have hstable : (prefixWord ++ tailWord_4639626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639626).length < 2 ^ (prefixWord ++ tailWord_4639626).sum := by decide
  have hdescent : baseEnd_4639626 < baseStart_4639626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639648 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 1, 6]
def baseStart_4639648 : Nat := 118140960795 + 4639648 * 2 ^ 59
def prefixEnd_4639648 : Nat := 4983230072969 + 3 ^ 40 * 4639648 * 2
def baseEnd_4639648 : Nat := 794123163890522863187551

theorem tailTrace_4639648 : CollatzResearch.WordTrace tailWord_4639648 prefixEnd_4639648 794123163890522863187551 := by
  unfold tailWord_4639648
  simp only [CollatzResearch.WordTrace]
  refine ⟨84610932347677579819107799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112814576463570106425477065 84610932347677579819107799)
  ·
    refine ⟨126916398521516369728661699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84610932347677579819107799 126916398521516369728661699)
    ·
      refine ⟨190374597782274554592992549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126916398521516369728661699 190374597782274554592992549)
      ·
        refine ⟨35695237084176478986186103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190374597782274554592992549 35695237084176478986186103)
        ·
          refine ⟨53542855626264718479279155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35695237084176478986186103 53542855626264718479279155)
          ·
            refine ⟨80314283439397077718918733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53542855626264718479279155 80314283439397077718918733)
            ·
              refine ⟨30117856289773904144594525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80314283439397077718918733 30117856289773904144594525)
              ·
                refine ⟨11294196108665214054222947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30117856289773904144594525 11294196108665214054222947)
                ·
                  refine ⟨16941294162997821081334421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11294196108665214054222947 16941294162997821081334421)
                  ·
                    refine ⟨794123163890522863187551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16941294162997821081334421 794123163890522863187551)
                    ·
                      rfl

theorem cell23_4639648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 6].length) (baseStart_4639648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639648 prefixEnd_4639648 := by exact prefixLift 4639648
  have htrace : WordTrace (prefixWord ++ tailWord_4639648) baseStart_4639648 baseEnd_4639648 := by
    simpa [prefixWord, tailWord_4639648, baseEnd_4639648] using wordTrace_append hprefix tailTrace_4639648
  have hstable : (prefixWord ++ tailWord_4639648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639648).length < 2 ^ (prefixWord ++ tailWord_4639648).sum := by decide
  have hdescent : baseEnd_4639648 < baseStart_4639648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639672 : List Nat := [2, 1, 2, 1, 2, 4, 4, 1, 1, 1, 4]
def baseStart_4639672 : Nat := 118140960795 + 4639672 * 2 ^ 59
def prefixEnd_4639672 : Nat := 4983230072969 + 3 ^ 40 * 4639672 * 2
def baseEnd_4639672 : Nat := 2382381815207276495662543

theorem tailTrace_4639672 : CollatzResearch.WordTrace tailWord_4639672 prefixEnd_4639672 2382381815207276495662543 := by
  unfold tailWord_4639672
  simp only [CollatzResearch.WordTrace]
  refine ⟨84611370023634105868544635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112815160031512141158059513 84611370023634105868544635)
  ·
    refine ⟨126917055035451158802816953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84611370023634105868544635 126917055035451158802816953)
    ·
      refine ⟨95187791276588369102112715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126917055035451158802816953 95187791276588369102112715)
      ·
        refine ⟨142781686914882553653169073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95187791276588369102112715 142781686914882553653169073)
        ·
          refine ⟨107086265186161915239876805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142781686914882553653169073 107086265186161915239876805)
          ·
            refine ⟨20078674722405359107476901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107086265186161915239876805 20078674722405359107476901)
            ·
              refine ⟨3764751510451004832651919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20078674722405359107476901 3764751510451004832651919)
              ·
                refine ⟨5647127265676507248977879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3764751510451004832651919 5647127265676507248977879)
                ·
                  refine ⟨8470690898514760873466819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5647127265676507248977879 8470690898514760873466819)
                  ·
                    refine ⟨12706036347772141310200229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8470690898514760873466819 12706036347772141310200229)
                    ·
                      refine ⟨2382381815207276495662543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12706036347772141310200229 2382381815207276495662543)
                      ·
                        rfl

theorem cell23_4639672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 1, 1, 4].length) (baseStart_4639672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639672 prefixEnd_4639672 := by exact prefixLift 4639672
  have htrace : WordTrace (prefixWord ++ tailWord_4639672) baseStart_4639672 baseEnd_4639672 := by
    simpa [prefixWord, tailWord_4639672, baseEnd_4639672] using wordTrace_append hprefix tailTrace_4639672
  have hstable : (prefixWord ++ tailWord_4639672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639672).length < 2 ^ (prefixWord ++ tailWord_4639672).sum := by decide
  have hdescent : baseEnd_4639672 < baseStart_4639672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639678 : List Nat := [4, 2, 1, 1, 1, 2, 12]
def baseStart_4639678 : Nat := 118140960795 + 4639678 * 2 ^ 59
def prefixEnd_4639678 : Nat := 4983230072969 + 3 ^ 40 * 4639678 * 2
def baseEnd_4639678 : Nat := 29412159211002512002315

theorem tailTrace_4639678 : CollatzResearch.WordTrace tailWord_4639678 prefixEnd_4639678 29412159211002512002315 := by
  unfold tailWord_4639678
  simp only [CollatzResearch.WordTrace]
  refine ⟨21152869860655809345225961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112815305923497649841205125 21152869860655809345225961)
  ·
    refine ⟨15864652395491857008919471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21152869860655809345225961 15864652395491857008919471)
    ·
      refine ⟨23796978593237785513379207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15864652395491857008919471 23796978593237785513379207)
      ·
        refine ⟨35695467889856678270068811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23796978593237785513379207 35695467889856678270068811)
        ·
          refine ⟨53543201834785017405103217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35695467889856678270068811 53543201834785017405103217)
          ·
            refine ⟨40157401376088763053827413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53543201834785017405103217 40157401376088763053827413)
            ·
              refine ⟨29412159211002512002315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 40157401376088763053827413 29412159211002512002315)
              ·
                rfl

theorem cell23_4639678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 12].length) (baseStart_4639678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639678 prefixEnd_4639678 := by exact prefixLift 4639678
  have htrace : WordTrace (prefixWord ++ tailWord_4639678) baseStart_4639678 baseEnd_4639678 := by
    simpa [prefixWord, tailWord_4639678, baseEnd_4639678] using wordTrace_append hprefix tailTrace_4639678
  have hstable : (prefixWord ++ tailWord_4639678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639678).length < 2 ^ (prefixWord ++ tailWord_4639678).sum := by decide
  have hdescent : baseEnd_4639678 < baseStart_4639678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639702 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_4639702 : Nat := 118140960795 + 4639702 * 2 ^ 59
def prefixEnd_4639702 : Nat := 4983230072969 + 3 ^ 40 * 4639702 * 2
def baseEnd_4639702 : Nat := 2382397219626911378287405

theorem tailTrace_4639702 : CollatzResearch.WordTrace tailWord_4639702 prefixEnd_4639702 2382397219626911378287405 := by
  unfold tailWord_4639702
  simp only [CollatzResearch.WordTrace]
  refine ⟨10576489639822470428792585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112815889491439684573787573 10576489639822470428792585)
  ·
    refine ⟨7932367229866852821594439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10576489639822470428792585 7932367229866852821594439)
    ·
      refine ⟨11898550844800279232391659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7932367229866852821594439 11898550844800279232391659)
      ·
        refine ⟨17847826267200418848587489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11898550844800279232391659 17847826267200418848587489)
        ·
          refine ⟨13385869700400314136440617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17847826267200418848587489 13385869700400314136440617)
          ·
            refine ⟨10039402275300235602330463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13385869700400314136440617 10039402275300235602330463)
            ·
              refine ⟨15059103412950353403495695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10039402275300235602330463 15059103412950353403495695)
              ·
                refine ⟨22588655119425530105243543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15059103412950353403495695 22588655119425530105243543)
                ·
                  refine ⟨33882982679138295157865315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22588655119425530105243543 33882982679138295157865315)
                  ·
                    refine ⟨50824474018707442736797973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33882982679138295157865315 50824474018707442736797973)
                    ·
                      refine ⟨2382397219626911378287405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50824474018707442736797973 2382397219626911378287405)
                      ·
                        rfl

theorem cell23_4639702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_4639702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639702 prefixEnd_4639702 := by exact prefixLift 4639702
  have htrace : WordTrace (prefixWord ++ tailWord_4639702) baseStart_4639702 baseEnd_4639702 := by
    simpa [prefixWord, tailWord_4639702, baseEnd_4639702] using wordTrace_append hprefix tailTrace_4639702
  have hstable : (prefixWord ++ tailWord_4639702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639702).length < 2 ^ (prefixWord ++ tailWord_4639702).sum := by decide
  have hdescent : baseEnd_4639702 < baseStart_4639702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639709 : List Nat := [1, 4, 3, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_4639709 : Nat := 118140960795 + 4639709 * 2 ^ 59
def prefixEnd_4639709 : Nat := 4983230072969 + 3 ^ 40 * 4639709 * 2
def baseEnd_4639709 : Nat := 2382400813991492850899873

theorem tailTrace_4639709 : CollatzResearch.WordTrace tailWord_4639709 prefixEnd_4639709 2382400813991492850899873 := by
  unfold tailWord_4639709
  simp only [CollatzResearch.WordTrace]
  refine ⟨169224089548134167056186181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112816059698756111370790787 169224089548134167056186181)
  ·
    refine ⟨31729516790275156323034909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169224089548134167056186181 31729516790275156323034909)
    ·
      refine ⟨11898568796353183621138091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31729516790275156323034909 11898568796353183621138091)
      ·
        refine ⟨17847853194529775431707137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11898568796353183621138091 17847853194529775431707137)
        ·
          refine ⟨13385889895897331573780353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17847853194529775431707137 13385889895897331573780353)
          ·
            refine ⟨10039417421922998680335265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13385889895897331573780353 10039417421922998680335265)
            ·
              refine ⟨7529563066442249010251449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10039417421922998680335265 7529563066442249010251449)
              ·
                refine ⟨5647172299831686757688587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7529563066442249010251449 5647172299831686757688587)
                ·
                  refine ⟨8470758449747530136532881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5647172299831686757688587 8470758449747530136532881)
                  ·
                    refine ⟨6353068837310647602399661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8470758449747530136532881 6353068837310647602399661)
                    ·
                      refine ⟨2382400813991492850899873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6353068837310647602399661 2382400813991492850899873)
                      ·
                        rfl

theorem cell23_4639709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_4639709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639709 prefixEnd_4639709 := by exact prefixLift 4639709
  have htrace : WordTrace (prefixWord ++ tailWord_4639709) baseStart_4639709 baseEnd_4639709 := by
    simpa [prefixWord, tailWord_4639709, baseEnd_4639709] using wordTrace_append hprefix tailTrace_4639709
  have hstable : (prefixWord ++ tailWord_4639709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639709).length < 2 ^ (prefixWord ++ tailWord_4639709).sum := by decide
  have hdescent : baseEnd_4639709 < baseStart_4639709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639722 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_4639722 : Nat := 118140960795 + 4639722 * 2 ^ 59
def prefixEnd_4639722 : Nat := 4983230072969 + 3 ^ 40 * 4639722 * 2
def baseEnd_4639722 : Nat := 2382407489240001300037313

theorem tailTrace_4639722 : CollatzResearch.WordTrace tailWord_4639722 prefixEnd_4639722 2382407489240001300037313 := by
  unfold tailWord_4639722
  simp only [CollatzResearch.WordTrace]
  refine ⟨42306140924271767569102355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112816375798058046850939613 42306140924271767569102355)
  ·
    refine ⟨63459211386407651353653533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42306140924271767569102355 63459211386407651353653533)
    ·
      refine ⟨23797204269902869257620075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63459211386407651353653533 23797204269902869257620075)
      ·
        refine ⟨35695806404854303886430113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23797204269902869257620075 35695806404854303886430113)
        ·
          refine ⟨26771854803640727914822585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35695806404854303886430113 26771854803640727914822585)
          ·
            refine ⟨20078891102730545936116939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26771854803640727914822585 20078891102730545936116939)
            ·
              refine ⟨30118336654095818904175409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20078891102730545936116939 30118336654095818904175409)
              ·
                refine ⟨22588752490571864178131557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30118336654095818904175409 22588752490571864178131557)
                ·
                  refine ⟨4235391091982224533399667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22588752490571864178131557 4235391091982224533399667)
                  ·
                    refine ⟨6353086637973336800099501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4235391091982224533399667 6353086637973336800099501)
                    ·
                      refine ⟨2382407489240001300037313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6353086637973336800099501 2382407489240001300037313)
                      ·
                        rfl

theorem cell23_4639722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_4639722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639722 prefixEnd_4639722 := by exact prefixLift 4639722
  have htrace : WordTrace (prefixWord ++ tailWord_4639722) baseStart_4639722 baseEnd_4639722 := by
    simpa [prefixWord, tailWord_4639722, baseEnd_4639722] using wordTrace_append hprefix tailTrace_4639722
  have hstable : (prefixWord ++ tailWord_4639722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639722).length < 2 ^ (prefixWord ++ tailWord_4639722).sum := by decide
  have hdescent : baseEnd_4639722 < baseStart_4639722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639728 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 4]
def baseStart_4639728 : Nat := 118140960795 + 4639728 * 2 ^ 59
def prefixEnd_4639728 : Nat := 4983230072969 + 3 ^ 40 * 4639728 * 2
def baseEnd_4639728 : Nat := 2382410570123928276562285

theorem tailTrace_4639728 : CollatzResearch.WordTrace tailWord_4639728 prefixEnd_4639728 2382410570123928276562285 := by
  unfold tailWord_4639728
  simp only [CollatzResearch.WordTrace]
  refine ⟨84612391267532666650563919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112816521690043555534085225 84612391267532666650563919)
  ·
    refine ⟨126918586901298999975845879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84612391267532666650563919 126918586901298999975845879)
    ·
      refine ⟨190377880351948499963768819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126918586901298999975845879 190377880351948499963768819)
      ·
        refine ⟨285566820527922749945653229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190377880351948499963768819 285566820527922749945653229)
        ·
          refine ⟨107087557697971031229619961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285566820527922749945653229 107087557697971031229619961)
          ·
            refine ⟨80315668273478273422214971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107087557697971031229619961 80315668273478273422214971)
            ·
              refine ⟨120473502410217410133322457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80315668273478273422214971 120473502410217410133322457)
              ·
                refine ⟨90355126807663057599991843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120473502410217410133322457 90355126807663057599991843)
                ·
                  refine ⟨135532690211494586399987765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90355126807663057599991843 135532690211494586399987765)
                  ·
                    refine ⟨12706189707327617474998853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 135532690211494586399987765 12706189707327617474998853)
                    ·
                      refine ⟨2382410570123928276562285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12706189707327617474998853 2382410570123928276562285)
                      ·
                        rfl

theorem cell23_4639728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_4639728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639728 prefixEnd_4639728 := by exact prefixLift 4639728
  have htrace : WordTrace (prefixWord ++ tailWord_4639728) baseStart_4639728 baseEnd_4639728 := by
    simpa [prefixWord, tailWord_4639728, baseEnd_4639728] using wordTrace_append hprefix tailTrace_4639728
  have hstable : (prefixWord ++ tailWord_4639728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639728).length < 2 ^ (prefixWord ++ tailWord_4639728).sum := by decide
  have hdescent : baseEnd_4639728 < baseStart_4639728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639738 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 4, 6]
def baseStart_4639738 : Nat := 118140960795 + 4639738 * 2 ^ 59
def prefixEnd_4639738 : Nat := 4983230072969 + 3 ^ 40 * 4639738 * 2
def baseEnd_4639738 : Nat := 794138568310157745812413

theorem tailTrace_4639738 : CollatzResearch.WordTrace tailWord_4639738 prefixEnd_4639738 794138568310157745812413 := by
  unfold tailWord_4639738
  simp only [CollatzResearch.WordTrace]
  refine ⟨42306286816257276252247967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112816764843352736672661245 42306286816257276252247967)
  ·
    refine ⟨63459430224385914378371951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42306286816257276252247967 63459430224385914378371951)
    ·
      refine ⟨95189145336578871567557927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63459430224385914378371951 95189145336578871567557927)
      ·
        refine ⟨142783718004868307351336891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95189145336578871567557927 142783718004868307351336891)
        ·
          refine ⟨214175577007302461027005337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142783718004868307351336891 214175577007302461027005337)
          ·
            refine ⟨160631682755476845770254003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214175577007302461027005337 160631682755476845770254003)
            ·
              refine ⟨240947524133215268655381005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160631682755476845770254003 240947524133215268655381005)
              ·
                refine ⟨90355321549955725745767877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240947524133215268655381005 90355321549955725745767877)
                ·
                  refine ⟨16941622790616698577331477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90355321549955725745767877 16941622790616698577331477)
                  ·
                    refine ⟨794138568310157745812413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16941622790616698577331477 794138568310157745812413)
                    ·
                      rfl

theorem cell23_4639738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_4639738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639738 prefixEnd_4639738 := by exact prefixLift 4639738
  have htrace : WordTrace (prefixWord ++ tailWord_4639738) baseStart_4639738 baseEnd_4639738 := by
    simpa [prefixWord, tailWord_4639738, baseEnd_4639738] using wordTrace_append hprefix tailTrace_4639738
  have hstable : (prefixWord ++ tailWord_4639738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639738).length < 2 ^ (prefixWord ++ tailWord_4639738).sum := by decide
  have hdescent : baseEnd_4639738 < baseStart_4639738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639756 : List Nat := [2, 2, 1, 2, 3, 4, 2, 1, 2, 1, 3]
def baseStart_4639756 : Nat := 118140960795 + 4639756 * 2 ^ 59
def prefixEnd_4639756 : Nat := 4983230072969 + 3 ^ 40 * 4639756 * 2
def baseEnd_4639756 : Nat := 2382424947582254167012157

theorem tailTrace_4639756 : CollatzResearch.WordTrace tailWord_4639756 prefixEnd_4639756 2382424947582254167012157 := by
  unfold tailWord_4639756
  simp only [CollatzResearch.WordTrace]
  refine ⟨84612901889481947041573561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112817202519309262722098081 84612901889481947041573561)
  ·
    refine ⟨63459676417111460281180171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84612901889481947041573561 63459676417111460281180171)
    ·
      refine ⟨95189514625667190421770257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63459676417111460281180171 95189514625667190421770257)
      ·
        refine ⟨71392135969250392816327693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95189514625667190421770257 71392135969250392816327693)
        ·
          refine ⟨26772050988468897306122885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71392135969250392816327693 26772050988468897306122885)
          ·
            refine ⟨5019759560337918244898041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26772050988468897306122885 5019759560337918244898041)
            ·
              refine ⟨3764819670253438683673531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5019759560337918244898041 3764819670253438683673531)
              ·
                refine ⟨5647229505380158025510297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3764819670253438683673531 5647229505380158025510297)
                ·
                  refine ⟨4235422129035118519132723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5647229505380158025510297 4235422129035118519132723)
                  ·
                    refine ⟨6353133193552677778699085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4235422129035118519132723 6353133193552677778699085)
                    ·
                      refine ⟨2382424947582254167012157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6353133193552677778699085 2382424947582254167012157)
                      ·
                        rfl

theorem cell23_4639756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_4639756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639756 prefixEnd_4639756 := by exact prefixLift 4639756
  have htrace : WordTrace (prefixWord ++ tailWord_4639756) baseStart_4639756 baseEnd_4639756 := by
    simpa [prefixWord, tailWord_4639756, baseEnd_4639756] using wordTrace_append hprefix tailTrace_4639756
  have hstable : (prefixWord ++ tailWord_4639756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639756).length < 2 ^ (prefixWord ++ tailWord_4639756).sum := by decide
  have hdescent : baseEnd_4639756 < baseStart_4639756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639765 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_4639765 : Nat := 118140960795 + 4639765 * 2 ^ 59
def prefixEnd_4639765 : Nat := 4983230072969 + 3 ^ 40 * 4639765 * 2
def baseEnd_4639765 : Nat := 2382429568908144631799615

theorem tailTrace_4639765 : CollatzResearch.WordTrace tailWord_4639765 prefixEnd_4639765 2382429568908144631799615 := by
  unfold tailWord_4639765
  simp only [CollatzResearch.WordTrace]
  refine ⟨169226132035931288620224749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112817421357287525746816499 169226132035931288620224749)
  ·
    refine ⟨63459799513474233232584281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169226132035931288620224749 63459799513474233232584281)
    ·
      refine ⟨47594849635105674924438211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63459799513474233232584281 47594849635105674924438211)
      ·
        refine ⟨71392274452658512386657317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47594849635105674924438211 71392274452658512386657317)
        ·
          refine ⟨13386051459873471072498247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71392274452658512386657317 13386051459873471072498247)
          ·
            refine ⟨20079077189810206608747371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13386051459873471072498247 20079077189810206608747371)
            ·
              refine ⟨30118615784715309913121057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20079077189810206608747371 30118615784715309913121057)
              ·
                refine ⟨22588961838536482434840793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30118615784715309913121057 22588961838536482434840793)
                ·
                  refine ⟨16941721378902361826130595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22588961838536482434840793 16941721378902361826130595)
                  ·
                    refine ⟨25412582068353542739195893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16941721378902361826130595 25412582068353542739195893)
                    ·
                      refine ⟨2382429568908144631799615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25412582068353542739195893 2382429568908144631799615)
                      ·
                        rfl

theorem cell23_4639765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_4639765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639765 prefixEnd_4639765 := by exact prefixLift 4639765
  have htrace : WordTrace (prefixWord ++ tailWord_4639765) baseStart_4639765 baseEnd_4639765 := by
    simpa [prefixWord, tailWord_4639765, baseEnd_4639765] using wordTrace_append hprefix tailTrace_4639765
  have hstable : (prefixWord ++ tailWord_4639765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639765).length < 2 ^ (prefixWord ++ tailWord_4639765).sum := by decide
  have hdescent : baseEnd_4639765 < baseStart_4639765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639783 : List Nat := [1, 1, 7, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_4639783 : Nat := 118140960795 + 4639783 * 2 ^ 59
def prefixEnd_4639783 : Nat := 4983230072969 + 3 ^ 40 * 4639783 * 2
def baseEnd_4639783 : Nat := 2382438811559925561374533

theorem tailTrace_4639783 : CollatzResearch.WordTrace tailWord_4639783 prefixEnd_4639783 2382438811559925561374533 := by
  unfold tailWord_4639783
  simp only [CollatzResearch.WordTrace]
  refine ⟨169226788549866077694380003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112817859033244051796253335 169226788549866077694380003)
  ·
    refine ⟨253840182824799116541570005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169226788549866077694380003 253840182824799116541570005)
    ·
      refine ⟨5949379284956229293943047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 253840182824799116541570005 5949379284956229293943047)
      ·
        refine ⟨8924068927434343940914571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5949379284956229293943047 8924068927434343940914571)
        ·
          refine ⟨13386103391151515911371857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8924068927434343940914571 13386103391151515911371857)
          ·
            refine ⟨10039577543363636933528893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13386103391151515911371857 10039577543363636933528893)
            ·
              refine ⟨3764841578761363850073335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10039577543363636933528893 3764841578761363850073335)
              ·
                refine ⟨5647262368142045775110003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3764841578761363850073335 5647262368142045775110003)
                ·
                  refine ⟨8470893552213068662665005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5647262368142045775110003 8470893552213068662665005)
                  ·
                    refine ⟨3176585082079900748499377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8470893552213068662665005 3176585082079900748499377)
                    ·
                      refine ⟨2382438811559925561374533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176585082079900748499377 2382438811559925561374533)
                      ·
                        rfl

theorem cell23_4639783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_4639783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639783 prefixEnd_4639783 := by exact prefixLift 4639783
  have htrace : WordTrace (prefixWord ++ tailWord_4639783) baseStart_4639783 baseEnd_4639783 := by
    simpa [prefixWord, tailWord_4639783, baseEnd_4639783] using wordTrace_append hprefix tailTrace_4639783
  have hstable : (prefixWord ++ tailWord_4639783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639783).length < 2 ^ (prefixWord ++ tailWord_4639783).sum := by decide
  have hdescent : baseEnd_4639783 < baseStart_4639783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639795 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 3]
def baseStart_4639795 : Nat := 118140960795 + 4639795 * 2 ^ 59
def prefixEnd_4639795 : Nat := 4983230072969 + 3 ^ 40 * 4639795 * 2
def baseEnd_4639795 : Nat := 2382444973327779514424477

theorem tailTrace_4639795 : CollatzResearch.WordTrace tailWord_4639795 prefixEnd_4639795 2382444973327779514424477 := by
  unfold tailWord_4639795
  simp only [CollatzResearch.WordTrace]
  refine ⟨169227226225822603743816839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112818150817215069162544559 169227226225822603743816839)
  ·
    refine ⟨253840839338733905615725259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169227226225822603743816839 253840839338733905615725259)
    ·
      refine ⟨380761259008100858423587889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253840839338733905615725259 380761259008100858423587889)
      ·
        refine ⟨285570944256075643817690917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380761259008100858423587889 285570944256075643817690917)
        ·
          refine ⟨53544552048014183215817047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 285570944256075643817690917 53544552048014183215817047)
          ·
            refine ⟨80316828072021274823725571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53544552048014183215817047 80316828072021274823725571)
            ·
              refine ⟨120475242108031912235588357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80316828072021274823725571 120475242108031912235588357)
              ·
                refine ⟨22589107895255983544172817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120475242108031912235588357 22589107895255983544172817)
                ·
                  refine ⟨16941830921441987658129613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22589107895255983544172817 16941830921441987658129613)
                  ·
                    refine ⟨6353186595540745371798605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16941830921441987658129613 6353186595540745371798605)
                    ·
                      refine ⟨2382444973327779514424477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6353186595540745371798605 2382444973327779514424477)
                      ·
                        rfl

theorem cell23_4639795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 3].length) (baseStart_4639795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639795 prefixEnd_4639795 := by exact prefixLift 4639795
  have htrace : WordTrace (prefixWord ++ tailWord_4639795) baseStart_4639795 baseEnd_4639795 := by
    simpa [prefixWord, tailWord_4639795, baseEnd_4639795] using wordTrace_append hprefix tailTrace_4639795
  have hstable : (prefixWord ++ tailWord_4639795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639795).length < 2 ^ (prefixWord ++ tailWord_4639795).sum := by decide
  have hdescent : baseEnd_4639795 < baseStart_4639795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639822 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2]
def baseStart_4639822 : Nat := 118140960795 + 4639822 * 2 ^ 59
def prefixEnd_4639822 : Nat := 4983230072969 + 3 ^ 40 * 4639822 * 2
def baseEnd_4639822 : Nat := 2382458837305450908786853

theorem tailTrace_4639822 : CollatzResearch.WordTrace tailWord_4639822 prefixEnd_4639822 2382458837305450908786853 := by
  unfold tailWord_4639822
  simp only [CollatzResearch.WordTrace]
  refine ⟨21153526374590598419381215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112818807331149858236699813 21153526374590598419381215)
  ·
    refine ⟨31730289561885897629071823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21153526374590598419381215 31730289561885897629071823)
    ·
      refine ⟨47595434342828846443607735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31730289561885897629071823 47595434342828846443607735)
      ·
        refine ⟨71393151514243269665411603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47595434342828846443607735 71393151514243269665411603)
        ·
          refine ⟨107089727271364904498117405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71393151514243269665411603 107089727271364904498117405)
          ·
            refine ⟨40158647726761839186794027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107089727271364904498117405 40158647726761839186794027)
            ·
              refine ⟨60237971590142758780191041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40158647726761839186794027 60237971590142758780191041)
              ·
                refine ⟨45178478692607069085143281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60237971590142758780191041 45178478692607069085143281)
                ·
                  refine ⟨33883859019455301813857461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45178478692607069085143281 33883859019455301813857461)
                  ·
                    refine ⟨3176611783073934545049137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33883859019455301813857461 3176611783073934545049137)
                    ·
                      refine ⟨2382458837305450908786853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176611783073934545049137 2382458837305450908786853)
                      ·
                        rfl

theorem cell23_4639822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_4639822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639822 prefixEnd_4639822 := by exact prefixLift 4639822
  have htrace : WordTrace (prefixWord ++ tailWord_4639822) baseStart_4639822 baseEnd_4639822 := by
    simpa [prefixWord, tailWord_4639822, baseEnd_4639822] using wordTrace_append hprefix tailTrace_4639822
  have hstable : (prefixWord ++ tailWord_4639822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639822).length < 2 ^ (prefixWord ++ tailWord_4639822).sum := by decide
  have hdescent : baseEnd_4639822 < baseStart_4639822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639852 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 4, 4, 2]
def baseStart_4639852 : Nat := 118140960795 + 4639852 * 2 ^ 59
def prefixEnd_4639852 : Nat := 4983230072969 + 3 ^ 40 * 4639852 * 2
def baseEnd_4639852 : Nat := 2382474241725085791411715

theorem tailTrace_4639852 : CollatzResearch.WordTrace tailWord_4639852 prefixEnd_4639852 2382474241725085791411715 := by
  unfold tailWord_4639852
  simp only [CollatzResearch.WordTrace]
  refine ⟨84614652593308051239320905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112819536791077401652427873 84614652593308051239320905)
  ·
    refine ⟨63460989444981038429490679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84614652593308051239320905 63460989444981038429490679)
    ·
      refine ⟨95191484167471557644236019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63460989444981038429490679 95191484167471557644236019)
      ·
        refine ⟨142787226251207336466354029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95191484167471557644236019 142787226251207336466354029)
        ·
          refine ⟨53545209844202751174882761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142787226251207336466354029 53545209844202751174882761)
          ·
            refine ⟨40158907383152063381162071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53545209844202751174882761 40158907383152063381162071)
            ·
              refine ⟨60238361074728095071743107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40158907383152063381162071 60238361074728095071743107)
              ·
                refine ⟨90357541612092142607614661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60238361074728095071743107 90357541612092142607614661)
                ·
                  refine ⟨16942039052267276738927749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90357541612092142607614661 16942039052267276738927749)
                  ·
                    refine ⟨3176632322300114388548953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16942039052267276738927749 3176632322300114388548953)
                    ·
                      refine ⟨2382474241725085791411715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176632322300114388548953 2382474241725085791411715)
                      ·
                        rfl

theorem cell23_4639852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 4, 2].length) (baseStart_4639852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639852 prefixEnd_4639852 := by exact prefixLift 4639852
  have htrace : WordTrace (prefixWord ++ tailWord_4639852) baseStart_4639852 baseEnd_4639852 := by
    simpa [prefixWord, tailWord_4639852, baseEnd_4639852] using wordTrace_append hprefix tailTrace_4639852
  have hstable : (prefixWord ++ tailWord_4639852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639852).length < 2 ^ (prefixWord ++ tailWord_4639852).sum := by decide
  have hdescent : baseEnd_4639852 < baseStart_4639852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639896 : List Nat := [2, 1, 2, 4, 2, 1, 3, 3, 1, 4]
def baseStart_4639896 : Nat := 118140960795 + 4639896 * 2 ^ 59
def prefixEnd_4639896 : Nat := 4983230072969 + 3 ^ 40 * 4639896 * 2
def baseEnd_4639896 : Nat := 794165611624627873087171

theorem tailTrace_4639896 : CollatzResearch.WordTrace tailWord_4639896 prefixEnd_4639896 794165611624627873087171 := by
  unfold tailWord_4639896
  simp only [CollatzResearch.WordTrace]
  refine ⟨84615454999228348996621771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112820606665637798662162361 84615454999228348996621771)
  ·
    refine ⟨126923182498842523494932657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84615454999228348996621771 126923182498842523494932657)
    ·
      refine ⟨95192386874131892621199493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126923182498842523494932657 95192386874131892621199493)
      ·
        refine ⟨17848572538899729866474905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95192386874131892621199493 17848572538899729866474905)
        ·
          refine ⟨13386429404174797399856179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17848572538899729866474905 13386429404174797399856179)
          ·
            refine ⟨20079644106262196099784269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13386429404174797399856179 20079644106262196099784269)
            ·
              refine ⟨7529866539848323537419101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20079644106262196099784269 7529866539848323537419101)
              ·
                refine ⟨2823699952443121326532163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7529866539848323537419101 2823699952443121326532163)
                ·
                  refine ⟨4235549928664681989798245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823699952443121326532163 4235549928664681989798245)
                  ·
                    refine ⟨794165611624627873087171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4235549928664681989798245 794165611624627873087171)
                    ·
                      rfl

theorem cell23_4639896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_4639896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639896 prefixEnd_4639896 := by exact prefixLift 4639896
  have htrace : WordTrace (prefixWord ++ tailWord_4639896) baseStart_4639896 baseEnd_4639896 := by
    simpa [prefixWord, tailWord_4639896, baseEnd_4639896] using wordTrace_append hprefix tailTrace_4639896
  have hstable : (prefixWord ++ tailWord_4639896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639896).length < 2 ^ (prefixWord ++ tailWord_4639896).sum := by decide
  have hdescent : baseEnd_4639896 < baseStart_4639896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639906 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_4639906 : Nat := 118140960795 + 4639906 * 2 ^ 59
def prefixEnd_4639906 : Nat := 4983230072969 + 3 ^ 40 * 4639906 * 2
def baseEnd_4639906 : Nat := 2382501969680428580136467

theorem tailTrace_4639906 : CollatzResearch.WordTrace tailWord_4639906 prefixEnd_4639906 2382501969680428580136467 := by
  unfold tailWord_4639906
  simp only [CollatzResearch.WordTrace]
  refine ⟨42307818682105117425276893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112820849818946979800738381 42307818682105117425276893)
  ·
    refine ⟨15865432005789419034478835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42307818682105117425276893 15865432005789419034478835)
    ·
      refine ⟨23798148008684128551718253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15865432005789419034478835 23798148008684128551718253)
      ·
        refine ⟨8924305503256548206894345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23798148008684128551718253 8924305503256548206894345)
        ·
          refine ⟨6693229127442411155170759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8924305503256548206894345 6693229127442411155170759)
          ·
            refine ⟨10039843691163616732756139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6693229127442411155170759 10039843691163616732756139)
            ·
              refine ⟨15059765536745425099134209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10039843691163616732756139 15059765536745425099134209)
              ·
                refine ⟨11294824152559068824350657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15059765536745425099134209 11294824152559068824350657)
                ·
                  refine ⟨8471118114419301618262993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11294824152559068824350657 8471118114419301618262993)
                  ·
                    refine ⟨6353338585814476213697245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8471118114419301618262993 6353338585814476213697245)
                    ·
                      refine ⟨2382501969680428580136467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6353338585814476213697245 2382501969680428580136467)
                      ·
                        rfl

theorem cell23_4639906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_4639906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639906 prefixEnd_4639906 := by exact prefixLift 4639906
  have htrace : WordTrace (prefixWord ++ tailWord_4639906) baseStart_4639906 baseEnd_4639906 := by
    simpa [prefixWord, tailWord_4639906, baseEnd_4639906] using wordTrace_append hprefix tailTrace_4639906
  have hstable : (prefixWord ++ tailWord_4639906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639906).length < 2 ^ (prefixWord ++ tailWord_4639906).sum := by decide
  have hdescent : baseEnd_4639906 < baseStart_4639906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639919 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 3, 1, 3]
def baseStart_4639919 : Nat := 118140960795 + 4639919 * 2 ^ 59
def prefixEnd_4639919 : Nat := 4983230072969 + 3 ^ 40 * 4639919 * 2
def baseEnd_4639919 : Nat := 2382508644928937029273907

theorem tailTrace_4639919 : CollatzResearch.WordTrace tailWord_4639919 prefixEnd_4639919 2382508644928937029273907 := by
  unfold tailWord_4639919
  simp only [CollatzResearch.WordTrace]
  refine ⟨169231748877373372921330811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112821165918248915280887207 169231748877373372921330811)
  ·
    refine ⟨253847623316060059381996217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169231748877373372921330811 253847623316060059381996217)
    ·
      refine ⟨190385717487045044536497163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253847623316060059381996217 190385717487045044536497163)
      ·
        refine ⟨285578576230567566804745745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190385717487045044536497163 285578576230567566804745745)
        ·
          refine ⟨214183932172925675103559309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285578576230567566804745745 214183932172925675103559309)
          ·
            refine ⟨80318974564847128163834741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214183932172925675103559309 80318974564847128163834741)
            ·
              refine ⟨7529903865454418265359507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80318974564847128163834741 7529903865454418265359507)
              ·
                refine ⟨11294855798181627398039261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7529903865454418265359507 11294855798181627398039261)
                ·
                  refine ⟨4235570924318110274264723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11294855798181627398039261 4235570924318110274264723)
                  ·
                    refine ⟨6353356386477165411397085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4235570924318110274264723 6353356386477165411397085)
                    ·
                      refine ⟨2382508644928937029273907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6353356386477165411397085 2382508644928937029273907)
                      ·
                        rfl

theorem cell23_4639919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 1, 3].length) (baseStart_4639919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639919 prefixEnd_4639919 := by exact prefixLift 4639919
  have htrace : WordTrace (prefixWord ++ tailWord_4639919) baseStart_4639919 baseEnd_4639919 := by
    simpa [prefixWord, tailWord_4639919, baseEnd_4639919] using wordTrace_append hprefix tailTrace_4639919
  have hstable : (prefixWord ++ tailWord_4639919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639919).length < 2 ^ (prefixWord ++ tailWord_4639919).sum := by decide
  have hdescent : baseEnd_4639919 < baseStart_4639919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639946 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 2, 3, 2]
def baseStart_4639946 : Nat := 118140960795 + 4639946 * 2 ^ 59
def prefixEnd_4639946 : Nat := 4983230072969 + 3 ^ 40 * 4639946 * 2
def baseEnd_4639946 : Nat := 2382522508906608423636283

theorem tailTrace_4639946 : CollatzResearch.WordTrace tailWord_4639946 prefixEnd_4639946 2382522508906608423636283 := by
  unfold tailWord_4639946
  simp only [CollatzResearch.WordTrace]
  refine ⟨42308183412068889133140923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112821822432183704355042461 42308183412068889133140923)
  ·
    refine ⟨63462275118103333699711385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42308183412068889133140923 63462275118103333699711385)
    ·
      refine ⟨47596706338577500274783539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63462275118103333699711385 47596706338577500274783539)
      ·
        refine ⟨71395059507866250412175309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47596706338577500274783539 71395059507866250412175309)
        ·
          refine ⟨26773147315449843904565741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71395059507866250412175309 26773147315449843904565741)
          ·
            refine ⟨10039930243293691464212153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26773147315449843904565741 10039930243293691464212153)
            ·
              refine ⟨7529947682470268598159115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10039930243293691464212153 7529947682470268598159115)
              ·
                refine ⟨11294921523705402897238673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7529947682470268598159115 11294921523705402897238673)
                ·
                  refine ⟨8471191142779052172929005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11294921523705402897238673 8471191142779052172929005)
                  ·
                    refine ⟨3176696678542144564848377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8471191142779052172929005 3176696678542144564848377)
                    ·
                      refine ⟨2382522508906608423636283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176696678542144564848377 2382522508906608423636283)
                      ·
                        rfl

theorem cell23_4639946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_4639946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639946 prefixEnd_4639946 := by exact prefixLift 4639946
  have htrace : WordTrace (prefixWord ++ tailWord_4639946) baseStart_4639946 baseEnd_4639946 := by
    simpa [prefixWord, tailWord_4639946, baseEnd_4639946] using wordTrace_append hprefix tailTrace_4639946
  have hstable : (prefixWord ++ tailWord_4639946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639946).length < 2 ^ (prefixWord ++ tailWord_4639946).sum := by decide
  have hdescent : baseEnd_4639946 < baseStart_4639946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639969 : List Nat := [1, 2, 3, 1, 3, 2, 1, 4, 2, 4]
def baseStart_4639969 : Nat := 118140960795 + 4639969 * 2 ^ 59
def prefixEnd_4639969 : Nat := 4983230072969 + 3 ^ 40 * 4639969 * 2
def baseEnd_4639969 : Nat := 794178106320553944549559

theorem tailTrace_4639969 : CollatzResearch.WordTrace tailWord_4639969 prefixEnd_4639969 794178106320553944549559 := by
  unfold tailWord_4639969
  simp only [CollatzResearch.WordTrace]
  refine ⟨169233572527192231460650961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112822381684794820973767307 169233572527192231460650961)
  ·
    refine ⟨126925179395394173595488221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169233572527192231460650961 126925179395394173595488221)
    ·
      refine ⟨47596942273272815098308083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126925179395394173595488221 47596942273272815098308083)
      ·
        refine ⟨71395413409909222647462125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47596942273272815098308083 71395413409909222647462125)
        ·
          refine ⟨26773280028715958492798297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71395413409909222647462125 26773280028715958492798297)
          ·
            refine ⟨20079960021536968869598723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26773280028715958492798297 20079960021536968869598723)
            ·
              refine ⟨30119940032305453304398085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20079960021536968869598723 30119940032305453304398085)
              ·
                refine ⟨5647488756057272494574641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30119940032305453304398085 5647488756057272494574641)
                ·
                  refine ⟨4235616567042954370930981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5647488756057272494574641 4235616567042954370930981)
                  ·
                    refine ⟨794178106320553944549559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4235616567042954370930981 794178106320553944549559)
                    ·
                      rfl

theorem cell23_4639969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_4639969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639969 prefixEnd_4639969 := by exact prefixLift 4639969
  have htrace : WordTrace (prefixWord ++ tailWord_4639969) baseStart_4639969 baseEnd_4639969 := by
    simpa [prefixWord, tailWord_4639969, baseEnd_4639969] using wordTrace_append hprefix tailTrace_4639969
  have hstable : (prefixWord ++ tailWord_4639969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639969).length < 2 ^ (prefixWord ++ tailWord_4639969).sum := by decide
  have hdescent : baseEnd_4639969 < baseStart_4639969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639976 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_4639976 : Nat := 118140960795 + 4639976 * 2 ^ 59
def prefixEnd_4639976 : Nat := 4983230072969 + 3 ^ 40 * 4639976 * 2
def baseEnd_4639976 : Nat := 2382537913326243306261145

theorem tailTrace_4639976 : CollatzResearch.WordTrace tailWord_4639976 prefixEnd_4639976 2382537913326243306261145 := by
  unfold tailWord_4639976
  simp only [CollatzResearch.WordTrace]
  refine ⟨84616913919083435828077891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112822551892111247770770521 84616913919083435828077891)
  ·
    refine ⟨126925370878625153742116837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84616913919083435828077891 126925370878625153742116837)
    ·
      refine ⟨23798507039742216326646907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126925370878625153742116837 23798507039742216326646907)
      ·
        refine ⟨35697760559613324489970361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23798507039742216326646907 35697760559613324489970361)
        ·
          refine ⟨26773320419709993367477771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35697760559613324489970361 26773320419709993367477771)
          ·
            refine ⟨40159980629564990051216657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26773320419709993367477771 40159980629564990051216657)
            ·
              refine ⟨30119985472173742538412493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40159980629564990051216657 30119985472173742538412493)
              ·
                refine ⟨11294994552065153451904685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30119985472173742538412493 11294994552065153451904685)
                ·
                  refine ⟨4235622957024432544464257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11294994552065153451904685 4235622957024432544464257)
                  ·
                    refine ⟨3176717217768324408348193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4235622957024432544464257 3176717217768324408348193)
                    ·
                      refine ⟨2382537913326243306261145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176717217768324408348193 2382537913326243306261145)
                      ·
                        rfl

theorem cell23_4639976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_4639976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639976 prefixEnd_4639976 := by exact prefixLift 4639976
  have htrace : WordTrace (prefixWord ++ tailWord_4639976) baseStart_4639976 baseEnd_4639976 := by
    simpa [prefixWord, tailWord_4639976, baseEnd_4639976] using wordTrace_append hprefix tailTrace_4639976
  have hstable : (prefixWord ++ tailWord_4639976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639976).length < 2 ^ (prefixWord ++ tailWord_4639976).sum := by decide
  have hdescent : baseEnd_4639976 < baseStart_4639976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4639982 : List Nat := [4, 1, 2, 1, 1, 1, 5, 8]
def baseStart_4639982 : Nat := 118140960795 + 4639982 * 2 ^ 59
def prefixEnd_4639982 : Nat := 4983230072969 + 3 ^ 40 * 4639982 * 2
def baseEnd_4639982 : Nat := 88242259044821121584671

theorem tailTrace_4639982 : CollatzResearch.WordTrace tailWord_4639982 prefixEnd_4639982 88242259044821121584671 := by
  unfold tailWord_4639982
  simp only [CollatzResearch.WordTrace]
  refine ⟨21154255834518141835109275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112822697784096756453916133 21154255834518141835109275)
  ·
    refine ⟨31731383751777212752663913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21154255834518141835109275 31731383751777212752663913)
    ·
      refine ⟨23798537813832909564497935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31731383751777212752663913 23798537813832909564497935)
      ·
        refine ⟨35697806720749364346746903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23798537813832909564497935 35697806720749364346746903)
        ·
          refine ⟨53546710081124046520120355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35697806720749364346746903 53546710081124046520120355)
          ·
            refine ⟨80320065121686069780180533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53546710081124046520120355 80320065121686069780180533)
            ·
              refine ⟨7530006105158069041891925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80320065121686069780180533 7530006105158069041891925)
              ·
                refine ⟨88242259044821121584671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7530006105158069041891925 88242259044821121584671)
                ·
                  rfl

theorem cell23_4639982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_4639982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4639982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4639982 prefixEnd_4639982 := by exact prefixLift 4639982
  have htrace : WordTrace (prefixWord ++ tailWord_4639982) baseStart_4639982 baseEnd_4639982 := by
    simpa [prefixWord, tailWord_4639982, baseEnd_4639982] using wordTrace_append hprefix tailTrace_4639982
  have hstable : (prefixWord ++ tailWord_4639982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4639982).length < 2 ^ (prefixWord ++ tailWord_4639982).sum := by decide
  have hdescent : baseEnd_4639982 < baseStart_4639982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4639982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640009 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 4, 1, 3]
def baseStart_4640009 : Nat := 118140960795 + 4640009 * 2 ^ 59
def prefixEnd_4640009 : Nat := 4983230072969 + 3 ^ 40 * 4640009 * 2
def baseEnd_4640009 : Nat := 2382554858187841677148493

theorem tailTrace_4640009 : CollatzResearch.WordTrace tailWord_4640009 prefixEnd_4640009 2382554858187841677148493 := by
  unfold tailWord_4640009
  simp only [CollatzResearch.WordTrace]
  refine ⟨169235031447047318292107081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112823354298031545528071387 169235031447047318292107081)
  ·
    refine ⟨126926273585285488719080311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169235031447047318292107081 126926273585285488719080311)
    ·
      refine ⟨190389410377928233078620467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126926273585285488719080311 190389410377928233078620467)
      ·
        refine ⟨285584115566892349617930701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190389410377928233078620467 285584115566892349617930701)
        ·
          refine ⟨107094043337584631106724013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285584115566892349617930701 107094043337584631106724013)
          ·
            refine ⟨40160266251594236665021505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107094043337584631106724013 40160266251594236665021505)
            ·
              refine ⟨30120199688695677498766129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40160266251594236665021505 30120199688695677498766129)
              ·
                refine ⟨22590149766521758124074597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30120199688695677498766129 22590149766521758124074597)
                ·
                  refine ⟨4235653081222829648263987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22590149766521758124074597 4235653081222829648263987)
                  ·
                    refine ⟨6353479621834244472395981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4235653081222829648263987 6353479621834244472395981)
                    ·
                      refine ⟨2382554858187841677148493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6353479621834244472395981 2382554858187841677148493)
                      ·
                        rfl

theorem cell23_4640009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 1, 3].length) (baseStart_4640009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640009 prefixEnd_4640009 := by exact prefixLift 4640009
  have htrace : WordTrace (prefixWord ++ tailWord_4640009) baseStart_4640009 baseEnd_4640009 := by
    simpa [prefixWord, tailWord_4640009, baseEnd_4640009] using wordTrace_append hprefix tailTrace_4640009
  have hstable : (prefixWord ++ tailWord_4640009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640009).length < 2 ^ (prefixWord ++ tailWord_4640009).sum := by decide
  have hdescent : baseEnd_4640009 < baseStart_4640009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640026 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3]
def baseStart_4640026 : Nat := 118140960795 + 4640026 * 2 ^ 59
def prefixEnd_4640026 : Nat := 4983230072969 + 3 ^ 40 * 4640026 * 2
def baseEnd_4640026 : Nat := 2382563587358968110635915

theorem tailTrace_4640026 : CollatzResearch.WordTrace tailWord_4640026 prefixEnd_4640026 2382563587358968110635915 := by
  unfold tailWord_4640026
  simp only [CollatzResearch.WordTrace]
  refine ⟨42308912871996432548868983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112823767658657153463650621 42308912871996432548868983)
  ·
    refine ⟨63463369307994648823303475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42308912871996432548868983 63463369307994648823303475)
    ·
      refine ⟨95195053961991973234955213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63463369307994648823303475 95195053961991973234955213)
      ·
        refine ⟨35698145235746989963108205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95195053961991973234955213 35698145235746989963108205)
        ·
          refine ⟨13386804463405121236165577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35698145235746989963108205 13386804463405121236165577)
          ·
            refine ⟨10040103347553840927124183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13386804463405121236165577 10040103347553840927124183)
            ·
              refine ⟨15060155021330761390686275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10040103347553840927124183 15060155021330761390686275)
              ·
                refine ⟨22590232531996142086029413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15060155021330761390686275 22590232531996142086029413)
                ·
                  refine ⟨4235668599749276641130515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22590232531996142086029413 4235668599749276641130515)
                  ·
                    refine ⟨6353502899623914961695773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4235668599749276641130515 6353502899623914961695773)
                    ·
                      refine ⟨2382563587358968110635915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6353502899623914961695773 2382563587358968110635915)
                      ·
                        rfl

theorem cell23_4640026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_4640026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640026 prefixEnd_4640026 := by exact prefixLift 4640026
  have htrace : WordTrace (prefixWord ++ tailWord_4640026) baseStart_4640026 baseEnd_4640026 := by
    simpa [prefixWord, tailWord_4640026, baseEnd_4640026] using wordTrace_append hprefix tailTrace_4640026
  have hstable : (prefixWord ++ tailWord_4640026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640026).length < 2 ^ (prefixWord ++ tailWord_4640026).sum := by decide
  have hdescent : baseEnd_4640026 < baseStart_4640026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640053 : List Nat := [1, 3, 3, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_4640053 : Nat := 118140960795 + 4640053 * 2 ^ 59
def prefixEnd_4640053 : Nat := 4983230072969 + 3 ^ 40 * 4640053 * 2
def baseEnd_4640053 : Nat := 2382577451336639504998291

theorem tailTrace_4640053 : CollatzResearch.WordTrace tailWord_4640053 prefixEnd_4640053 2382577451336639504998291 := by
  unfold tailWord_4640053
  simp only [CollatzResearch.WordTrace]
  refine ⟨169236636258887913806708813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112824424172591942537805875 169236636258887913806708813)
  ·
    refine ⟨63463738597082967677515805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169236636258887913806708813 63463738597082967677515805)
    ·
      refine ⟨23798901973906112879068427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63463738597082967677515805 23798901973906112879068427)
      ·
        refine ⟨35698352960859169318602641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23798901973906112879068427 35698352960859169318602641)
        ·
          refine ⟨26773764720644376988951981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35698352960859169318602641 26773764720644376988951981)
          ·
            refine ⟨10040161770241641370856993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26773764720644376988951981 10040161770241641370856993)
            ·
              refine ⟨7530121327681231028142745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10040161770241641370856993 7530121327681231028142745)
              ·
                refine ⟨5647590995760923271107059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7530121327681231028142745 5647590995760923271107059)
                ·
                  refine ⟨8471386493641384906660589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5647590995760923271107059 8471386493641384906660589)
                  ·
                    refine ⟨3176769935115519339997721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8471386493641384906660589 3176769935115519339997721)
                    ·
                      refine ⟨2382577451336639504998291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176769935115519339997721 2382577451336639504998291)
                      ·
                        rfl

theorem cell23_4640053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_4640053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640053 prefixEnd_4640053 := by exact prefixLift 4640053
  have htrace : WordTrace (prefixWord ++ tailWord_4640053) baseStart_4640053 baseEnd_4640053 := by
    simpa [prefixWord, tailWord_4640053, baseEnd_4640053] using wordTrace_append hprefix tailTrace_4640053
  have hstable : (prefixWord ++ tailWord_4640053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640053).length < 2 ^ (prefixWord ++ tailWord_4640053).sum := by decide
  have hdescent : baseEnd_4640053 < baseStart_4640053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640082 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_4640082 : Nat := 118140960795 + 4640082 * 2 ^ 59
def prefixEnd_4640082 : Nat := 4983230072969 + 3 ^ 40 * 4640082 * 2
def baseEnd_4640082 : Nat := 2382592342275619891535657

theorem tailTrace_4640082 : CollatzResearch.WordTrace tailWord_4640082 prefixEnd_4640082 2382592342275619891535657 := by
  unfold tailWord_4640082
  simp only [CollatzResearch.WordTrace]
  refine ⟨42309423493945712939878625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112825129317188567839676333 42309423493945712939878625)
  ·
    refine ⟨31732067620459284704908969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42309423493945712939878625 31732067620459284704908969)
    ·
      refine ⟨23799050715344463528681727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31732067620459284704908969 23799050715344463528681727)
      ·
        refine ⟨35698576073016695293022591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23799050715344463528681727 35698576073016695293022591)
        ·
          refine ⟨53547864109525042939533887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35698576073016695293022591 53547864109525042939533887)
          ·
            refine ⟨80321796164287564409300831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53547864109525042939533887 80321796164287564409300831)
            ·
              refine ⟨120482694246431346613951247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80321796164287564409300831 120482694246431346613951247)
              ·
                refine ⟨180724041369647019920926871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120482694246431346613951247 180724041369647019920926871)
                ·
                  refine ⟨271086062054470529881390307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180724041369647019920926871 271086062054470529881390307)
                  ·
                    refine ⟨406629093081705794822085461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 271086062054470529881390307 406629093081705794822085461)
                    ·
                      refine ⟨2382592342275619891535657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 406629093081705794822085461 2382592342275619891535657)
                      ·
                        rfl

theorem cell23_4640082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_4640082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640082 prefixEnd_4640082 := by exact prefixLift 4640082
  have htrace : WordTrace (prefixWord ++ tailWord_4640082) baseStart_4640082 baseEnd_4640082 := by
    simpa [prefixWord, tailWord_4640082, baseEnd_4640082] using wordTrace_append hprefix tailTrace_4640082
  have hstable : (prefixWord ++ tailWord_4640082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640082).length < 2 ^ (prefixWord ++ tailWord_4640082).sum := by decide
  have hdescent : baseEnd_4640082 < baseStart_4640082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640089 : List Nat := [1, 2, 1, 2, 2, 2, 2, 6, 5]
def baseStart_4640089 : Nat := 118140960795 + 4640089 * 2 ^ 59
def prefixEnd_4640089 : Nat := 4983230072969 + 3 ^ 40 * 4640089 * 2
def baseEnd_4640089 : Nat := 264732881848911262683125

theorem tailTrace_4640089 : CollatzResearch.WordTrace tailWord_4640089 prefixEnd_4640089 264732881848911262683125 := by
  unfold tailWord_4640089
  simp only [CollatzResearch.WordTrace]
  refine ⟨169237949286757491955019321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112825299524504994636679547 169237949286757491955019321)
  ·
    refine ⟨126928461965068118966264491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169237949286757491955019321 126928461965068118966264491)
    ·
      refine ⟨190392692947602178449396737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126928461965068118966264491 190392692947602178449396737)
      ·
        refine ⟨142794519710701633837047553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190392692947602178449396737 142794519710701633837047553)
        ·
          refine ⟨107095889783026225377785665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142794519710701633837047553 107095889783026225377785665)
          ·
            refine ⟨80321917337269669033339249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107095889783026225377785665 80321917337269669033339249)
            ·
              refine ⟨60241438002952251775004437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80321917337269669033339249 60241438002952251775004437)
              ·
                refine ⟨2823817406388386801953333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60241438002952251775004437 2823817406388386801953333)
                ·
                  refine ⟨264732881848911262683125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2823817406388386801953333 264732881848911262683125)
                  ·
                    rfl

theorem cell23_4640089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 5].length) (baseStart_4640089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640089 prefixEnd_4640089 := by exact prefixLift 4640089
  have htrace : WordTrace (prefixWord ++ tailWord_4640089) baseStart_4640089 baseEnd_4640089 := by
    simpa [prefixWord, tailWord_4640089, baseEnd_4640089] using wordTrace_append hprefix tailTrace_4640089
  have hstable : (prefixWord ++ tailWord_4640089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640089).length < 2 ^ (prefixWord ++ tailWord_4640089).sum := by decide
  have hdescent : baseEnd_4640089 < baseStart_4640089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640100 : List Nat := [2, 3, 1, 1, 3, 2, 4, 1, 2, 2, 2]
def baseStart_4640100 : Nat := 118140960795 + 4640100 * 2 ^ 59
def prefixEnd_4640100 : Nat := 4983230072969 + 3 ^ 40 * 4640100 * 2
def baseEnd_4640100 : Nat := 2382601584927400821110575

theorem tailTrace_4640100 : CollatzResearch.WordTrace tailWord_4640100 prefixEnd_4640100 2382601584927400821110575 := by
  unfold tailWord_4640100
  simp only [CollatzResearch.WordTrace]
  refine ⟨84619175244858820416834877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112825566993145093889113169 84619175244858820416834877)
  ·
    refine ⟨31732190716822057656313079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84619175244858820416834877 31732190716822057656313079)
    ·
      refine ⟨47598286075233086484469619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31732190716822057656313079 47598286075233086484469619)
      ·
        refine ⟨71397429112849629726704429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47598286075233086484469619 71397429112849629726704429)
        ·
          refine ⟨26774035917318611147514161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71397429112849629726704429 26774035917318611147514161)
          ·
            refine ⟨20080526937988958360635621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26774035917318611147514161 20080526937988958360635621)
            ·
              refine ⟨3765098800872929692619179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20080526937988958360635621 3765098800872929692619179)
              ·
                refine ⟨5647648201309394538928769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3765098800872929692619179 5647648201309394538928769)
                ·
                  refine ⟨4235736150982045904196577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5647648201309394538928769 4235736150982045904196577)
                  ·
                    refine ⟨3176802113236534428147433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4235736150982045904196577 3176802113236534428147433)
                    ·
                      refine ⟨2382601584927400821110575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176802113236534428147433 2382601584927400821110575)
                      ·
                        rfl

theorem cell23_4640100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_4640100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640100 prefixEnd_4640100 := by exact prefixLift 4640100
  have htrace : WordTrace (prefixWord ++ tailWord_4640100) baseStart_4640100 baseEnd_4640100 := by
    simpa [prefixWord, tailWord_4640100, baseEnd_4640100] using wordTrace_append hprefix tailTrace_4640100
  have hstable : (prefixWord ++ tailWord_4640100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640100).length < 2 ^ (prefixWord ++ tailWord_4640100).sum := by decide
  have hdescent : baseEnd_4640100 < baseStart_4640100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640112 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 7]
def baseStart_4640112 : Nat := 118140960795 + 4640112 * 2 ^ 59
def prefixEnd_4640112 : Nat := 4983230072969 + 3 ^ 40 * 4640112 * 2
def baseEnd_4640112 : Nat := 2382607746695254774160519

theorem tailTrace_4640112 : CollatzResearch.WordTrace tailWord_4640112 prefixEnd_4640112 2382607746695254774160519 := by
  unfold tailWord_4640112
  simp only [CollatzResearch.WordTrace]
  refine ⟨84619394082837083441553295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112825858777116111255404393 84619394082837083441553295)
  ·
    refine ⟨126929091124255625162329943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84619394082837083441553295 126929091124255625162329943)
    ·
      refine ⟨190393636686383437743494915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126929091124255625162329943 190393636686383437743494915)
      ·
        refine ⟨285590455029575156615242373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190393636686383437743494915 285590455029575156615242373)
        ·
          refine ⟨53548210318045341865357945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 285590455029575156615242373 53548210318045341865357945)
          ·
            refine ⟨40161157738534006399018459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53548210318045341865357945 40161157738534006399018459)
            ·
              refine ⟨60241736607801009598527689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40161157738534006399018459 60241736607801009598527689)
              ·
                refine ⟨45181302455850757198895767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60241736607801009598527689 45181302455850757198895767)
                ·
                  refine ⟨67771953683776135798343651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45181302455850757198895767 67771953683776135798343651)
                  ·
                    refine ⟨101657930525664203697515477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67771953683776135798343651 101657930525664203697515477)
                    ·
                      refine ⟨2382607746695254774160519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101657930525664203697515477 2382607746695254774160519)
                      ·
                        rfl

theorem cell23_4640112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_4640112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640112 prefixEnd_4640112 := by exact prefixLift 4640112
  have htrace : WordTrace (prefixWord ++ tailWord_4640112) baseStart_4640112 baseEnd_4640112 := by
    simpa [prefixWord, tailWord_4640112, baseEnd_4640112] using wordTrace_append hprefix tailTrace_4640112
  have hstable : (prefixWord ++ tailWord_4640112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640112).length < 2 ^ (prefixWord ++ tailWord_4640112).sum := by decide
  have hdescent : baseEnd_4640112 < baseStart_4640112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640119 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 2, 5]
def baseStart_4640119 : Nat := 118140960795 + 4640119 * 2 ^ 59
def prefixEnd_4640119 : Nat := 4983230072969 + 3 ^ 40 * 4640119 * 2
def baseEnd_4640119 : Nat := 794203780353278748924329

theorem tailTrace_4640119 : CollatzResearch.WordTrace tailWord_4640119 prefixEnd_4640119 794203780353278748924329 := by
  unfold tailWord_4640119
  simp only [CollatzResearch.WordTrace]
  refine ⟨169239043476648807078611411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112826028984432538052407607 169239043476648807078611411)
  ·
    refine ⟨253858565214973210617917117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169239043476648807078611411 253858565214973210617917117)
    ·
      refine ⟨95196961955614953981718919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253858565214973210617917117 95196961955614953981718919)
      ·
        refine ⟨142795442933422430972578379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95196961955614953981718919 142795442933422430972578379)
        ·
          refine ⟨214193164400133646458867569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142795442933422430972578379 214193164400133646458867569)
          ·
            refine ⟨160644873300100234844150677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214193164400133646458867569 160644873300100234844150677)
            ·
              refine ⟨7530228435942198508319563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 160644873300100234844150677 7530228435942198508319563)
              ·
                refine ⟨11295342653913297762479345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7530228435942198508319563 11295342653913297762479345)
                ·
                  refine ⟨8471506990434973321859509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11295342653913297762479345 8471506990434973321859509)
                  ·
                    refine ⟨794203780353278748924329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8471506990434973321859509 794203780353278748924329)
                    ·
                      rfl

theorem cell23_4640119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_4640119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640119 prefixEnd_4640119 := by exact prefixLift 4640119
  have htrace : WordTrace (prefixWord ++ tailWord_4640119) baseStart_4640119 baseEnd_4640119 := by
    simpa [prefixWord, tailWord_4640119, baseEnd_4640119] using wordTrace_append hprefix tailTrace_4640119
  have hstable : (prefixWord ++ tailWord_4640119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640119).length < 2 ^ (prefixWord ++ tailWord_4640119).sum := by decide
  have hdescent : baseEnd_4640119 < baseStart_4640119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640139 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 4]
def baseStart_4640139 : Nat := 118140960795 + 4640139 * 2 ^ 59
def prefixEnd_4640139 : Nat := 4983230072969 + 3 ^ 40 * 4640139 * 2
def baseEnd_4640139 : Nat := 2382621610672926168522895

theorem tailTrace_4640139 : CollatzResearch.WordTrace tailWord_4640139 prefixEnd_4640139 2382621610672926168522895 := by
  unfold tailWord_4640139
  simp only [CollatzResearch.WordTrace]
  refine ⟨169239772936576350494339471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112826515291050900329559647 169239772936576350494339471)
  ·
    refine ⟨253859659404864525741509207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169239772936576350494339471 253859659404864525741509207)
    ·
      refine ⟨380789489107296788612263811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253859659404864525741509207 380789489107296788612263811)
      ·
        refine ⟨571184233660945182918395717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380789489107296788612263811 571184233660945182918395717)
        ·
          refine ⟨107097043811427221797199197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 571184233660945182918395717 107097043811427221797199197)
          ·
            refine ⟨40161391429285208173949699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107097043811427221797199197 40161391429285208173949699)
            ·
              refine ⟨60242087143927812260924549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40161391429285208173949699 60242087143927812260924549)
              ·
                refine ⟨11295391339486464798923353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60242087143927812260924549 11295391339486464798923353)
                ·
                  refine ⟨8471543504614848599192515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11295391339486464798923353 8471543504614848599192515)
                  ·
                    refine ⟨12707315256922272898788773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8471543504614848599192515 12707315256922272898788773)
                    ·
                      refine ⟨2382621610672926168522895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12707315256922272898788773 2382621610672926168522895)
                      ·
                        rfl

theorem cell23_4640139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 4].length) (baseStart_4640139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640139 prefixEnd_4640139 := by exact prefixLift 4640139
  have htrace : WordTrace (prefixWord ++ tailWord_4640139) baseStart_4640139 baseEnd_4640139 := by
    simpa [prefixWord, tailWord_4640139, baseEnd_4640139] using wordTrace_append hprefix tailTrace_4640139
  have hstable : (prefixWord ++ tailWord_4640139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640139).length < 2 ^ (prefixWord ++ tailWord_4640139).sum := by decide
  have hdescent : baseEnd_4640139 < baseStart_4640139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640173 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_4640173 : Nat := 118140960795 + 4640173 * 2 ^ 59
def prefixEnd_4640173 : Nat := 4983230072969 + 3 ^ 40 * 4640173 * 2
def baseEnd_4640173 : Nat := 2382639069015179035497739

theorem tailTrace_4640173 : CollatzResearch.WordTrace tailWord_4640173 prefixEnd_4640173 2382639069015179035497739 := by
  unfold tailWord_4640173
  simp only [CollatzResearch.WordTrace]
  refine ⟨169241013018453174301077173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112827342012302116200718115 169241013018453174301077173)
  ·
    refine ⟨15866344970479985090725985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 169241013018453174301077173 15866344970479985090725985)
    ·
      refine ⟨11899758727859988818044489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15866344970479985090725985 11899758727859988818044489)
      ·
        refine ⟨8924819045894991613533367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11899758727859988818044489 8924819045894991613533367)
        ·
          refine ⟨13387228568842487420300051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8924819045894991613533367 13387228568842487420300051)
          ·
            refine ⟨20080842853263731130450077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13387228568842487420300051 20080842853263731130450077)
            ·
              refine ⟨7530316069973899173918779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20080842853263731130450077 7530316069973899173918779)
              ·
                refine ⟨11295474104960848760878169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7530316069973899173918779 11295474104960848760878169)
                ·
                  refine ⟨8471605578720636570658627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11295474104960848760878169 8471605578720636570658627)
                  ·
                    refine ⟨12707408368080954855987941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8471605578720636570658627 12707408368080954855987941)
                    ·
                      refine ⟨2382639069015179035497739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12707408368080954855987941 2382639069015179035497739)
                      ·
                        rfl

theorem cell23_4640173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_4640173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640173 prefixEnd_4640173 := by exact prefixLift 4640173
  have htrace : WordTrace (prefixWord ++ tailWord_4640173) baseStart_4640173 baseEnd_4640173 := by
    simpa [prefixWord, tailWord_4640173, baseEnd_4640173] using wordTrace_append hprefix tailTrace_4640173
  have hstable : (prefixWord ++ tailWord_4640173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640173).length < 2 ^ (prefixWord ++ tailWord_4640173).sum := by decide
  have hdescent : baseEnd_4640173 < baseStart_4640173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640183 : List Nat := [1, 1, 3, 1, 3, 2, 4, 3, 1, 4]
def baseStart_4640183 : Nat := 118140960795 + 4640183 * 2 ^ 59
def prefixEnd_4640183 : Nat := 4983230072969 + 3 ^ 40 * 4640183 * 2
def baseEnd_4640183 : Nat := 794214734607241332124231

theorem tailTrace_4640183 : CollatzResearch.WordTrace tailWord_4640183 prefixEnd_4640183 794214734607241332124231 := by
  unfold tailWord_4640183
  simp only [CollatzResearch.WordTrace]
  refine ⟨169241377748416946008941203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112827585165611297339294135 169241377748416946008941203)
  ·
    refine ⟨253862066622625419013411805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169241377748416946008941203 253862066622625419013411805)
    ·
      refine ⟨95198274983484532130029427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253862066622625419013411805 95198274983484532130029427)
      ·
        refine ⟨142797412475226798195044141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95198274983484532130029427 142797412475226798195044141)
        ·
          refine ⟨53549029678210049323141553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142797412475226798195044141 53549029678210049323141553)
          ·
            refine ⟨40161772258657536992356165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53549029678210049323141553 40161772258657536992356165)
            ·
              refine ⟨7530332298498288186066781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40161772258657536992356165 7530332298498288186066781)
              ·
                refine ⟨2823874611936858069775043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7530332298498288186066781 2823874611936858069775043)
                ·
                  refine ⟨4235811917905287104662565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823874611936858069775043 4235811917905287104662565)
                  ·
                    refine ⟨794214734607241332124231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4235811917905287104662565 794214734607241332124231)
                    ·
                      rfl

theorem cell23_4640183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_4640183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640183 prefixEnd_4640183 := by exact prefixLift 4640183
  have htrace : WordTrace (prefixWord ++ tailWord_4640183) baseStart_4640183 baseEnd_4640183 := by
    simpa [prefixWord, tailWord_4640183, baseEnd_4640183] using wordTrace_append hprefix tailTrace_4640183
  have hstable : (prefixWord ++ tailWord_4640183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640183).length < 2 ^ (prefixWord ++ tailWord_4640183).sum := by decide
  have hdescent : baseEnd_4640183 < baseStart_4640183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640196 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 8]
def baseStart_4640196 : Nat := 118140960795 + 4640196 * 2 ^ 59
def prefixEnd_4640196 : Nat := 4983230072969 + 3 ^ 40 * 4640196 * 2
def baseEnd_4640196 : Nat := 264738986563359160612237

theorem tailTrace_4640196 : CollatzResearch.WordTrace tailWord_4640196 prefixEnd_4640196 264738986563359160612237 := by
  unfold tailWord_4640196
  simp only [CollatzResearch.WordTrace]
  refine ⟨84620925948684924614582221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112827901264913232819442961 84620925948684924614582221)
  ·
    refine ⟨31732847230756846730468333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84620925948684924614582221 31732847230756846730468333)
    ·
      refine ⟨11899817711533817523925625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31732847230756846730468333 11899817711533817523925625)
      ·
        refine ⟨8924863283650363142944219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11899817711533817523925625 8924863283650363142944219)
        ·
          refine ⟨13387294925475544714416329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8924863283650363142944219 13387294925475544714416329)
          ·
            refine ⟨10040471194106658535812247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13387294925475544714416329 10040471194106658535812247)
            ·
              refine ⟨15060706791159987803718371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10040471194106658535812247 15060706791159987803718371)
              ·
                refine ⟨22591060186739981705577557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15060706791159987803718371 22591060186739981705577557)
                ·
                  refine ⟨264738986563359160612237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22591060186739981705577557 264738986563359160612237)
                  ·
                    rfl

theorem cell23_4640196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_4640196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640196 prefixEnd_4640196 := by exact prefixLift 4640196
  have htrace : WordTrace (prefixWord ++ tailWord_4640196) baseStart_4640196 baseEnd_4640196 := by
    simpa [prefixWord, tailWord_4640196, baseEnd_4640196] using wordTrace_append hprefix tailTrace_4640196
  have hstable : (prefixWord ++ tailWord_4640196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640196).length < 2 ^ (prefixWord ++ tailWord_4640196).sum := by decide
  have hdescent : baseEnd_4640196 < baseStart_4640196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640216 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 1, 5, 2]
def baseStart_4640216 : Nat := 118140960795 + 4640216 * 2 ^ 59
def prefixEnd_4640216 : Nat := 4983230072969 + 3 ^ 40 * 4640216 * 2
def baseEnd_4640216 : Nat := 2382661148683322367260041

theorem tailTrace_4640216 : CollatzResearch.WordTrace tailWord_4640216 prefixEnd_4640216 2382661148683322367260041 := by
  unfold tailWord_4640216
  simp only [CollatzResearch.WordTrace]
  refine ⟨84621290678648696322446251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112828387571531595096595001 84621290678648696322446251)
  ·
    refine ⟨126931936017973044483669377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84621290678648696322446251 126931936017973044483669377)
    ·
      refine ⟨95198952013479783362752033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126931936017973044483669377 95198952013479783362752033)
      ·
        refine ⟨71399214010109837522064025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95198952013479783362752033 71399214010109837522064025)
        ·
          refine ⟨53549410507582378141548019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71399214010109837522064025 53549410507582378141548019)
          ·
            refine ⟨80324115761373567212322029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53549410507582378141548019 80324115761373567212322029)
            ·
              refine ⟨30121543410515087704620761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80324115761373567212322029 30121543410515087704620761)
              ·
                refine ⟨22591157557886315778465571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30121543410515087704620761 22591157557886315778465571)
                ·
                  refine ⟨33886736336829473667698357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22591157557886315778465571 33886736336829473667698357)
                  ·
                    refine ⟨3176881531577763156346721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33886736336829473667698357 3176881531577763156346721)
                    ·
                      refine ⟨2382661148683322367260041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176881531577763156346721 2382661148683322367260041)
                      ·
                        rfl

theorem cell23_4640216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_4640216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640216 prefixEnd_4640216 := by exact prefixLift 4640216
  have htrace : WordTrace (prefixWord ++ tailWord_4640216) baseStart_4640216 baseEnd_4640216 := by
    simpa [prefixWord, tailWord_4640216, baseEnd_4640216] using wordTrace_append hprefix tailTrace_4640216
  have hstable : (prefixWord ++ tailWord_4640216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640216).length < 2 ^ (prefixWord ++ tailWord_4640216).sum := by decide
  have hdescent : baseEnd_4640216 < baseStart_4640216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640239 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 1, 6]
def baseStart_4640239 : Nat := 118140960795 + 4640239 * 2 ^ 59
def prefixEnd_4640239 : Nat := 4983230072969 + 3 ^ 40 * 4640239 * 2
def baseEnd_4640239 : Nat := 794224319579458592424145

theorem tailTrace_4640239 : CollatzResearch.WordTrace tailWord_4640239 prefixEnd_4640239 794224319579458592424145 := by
  unfold tailWord_4640239
  simp only [CollatzResearch.WordTrace]
  refine ⟨169243420236214067572979771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112828946824142711715319847 169243420236214067572979771)
  ·
    refine ⟨253865130354321101359469657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169243420236214067572979771 253865130354321101359469657)
    ·
      refine ⟨190398847765740826019602243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253865130354321101359469657 190398847765740826019602243)
      ·
        refine ⟨285598271648611239029403365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190398847765740826019602243 285598271648611239029403365)
        ·
          refine ⟨53549675934114607318013131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 285598271648611239029403365 53549675934114607318013131)
          ·
            refine ⟨80324513901171910977019697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53549675934114607318013131 80324513901171910977019697)
            ·
              refine ⟨60243385425878933232764773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80324513901171910977019697 60243385425878933232764773)
              ·
                refine ⟨11295634767352299981143395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60243385425878933232764773 11295634767352299981143395)
                ·
                  refine ⟨16943452151028449971715093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11295634767352299981143395 16943452151028449971715093)
                  ·
                    refine ⟨794224319579458592424145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16943452151028449971715093 794224319579458592424145)
                    ·
                      rfl

theorem cell23_4640239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 6].length) (baseStart_4640239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640239 prefixEnd_4640239 := by exact prefixLift 4640239
  have htrace : WordTrace (prefixWord ++ tailWord_4640239) baseStart_4640239 baseEnd_4640239 := by
    simpa [prefixWord, tailWord_4640239, baseEnd_4640239] using wordTrace_append hprefix tailTrace_4640239
  have hstable : (prefixWord ++ tailWord_4640239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640239).length < 2 ^ (prefixWord ++ tailWord_4640239).sum := by decide
  have hdescent : baseEnd_4640239 < baseStart_4640239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640240 : List Nat := [2, 1, 1, 1, 3, 4, 3, 3, 1, 1, 3]
def baseStart_4640240 : Nat := 118140960795 + 4640240 * 2 ^ 59
def prefixEnd_4640240 : Nat := 4983230072969 + 3 ^ 40 * 4640240 * 2
def baseEnd_4640240 : Nat := 2382673472219030273359931

theorem tailTrace_4640240 : CollatzResearch.WordTrace tailWord_4640240 prefixEnd_4640240 2382673472219030273359931 := by
  unfold tailWord_4640240
  simp only [CollatzResearch.WordTrace]
  refine ⟨84621728354605222371883087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112828971139473629829177449 84621728354605222371883087)
  ·
    refine ⟨126932592531907833557824631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84621728354605222371883087 126932592531907833557824631)
    ·
      refine ⟨190398888797861750336736947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126932592531907833557824631 190398888797861750336736947)
      ·
        refine ⟨285598333196792625505105421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190398888797861750336736947 285598333196792625505105421)
        ·
          refine ⟨107099374948797234564414533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285598333196792625505105421 107099374948797234564414533)
          ·
            refine ⟨20081132802899481480827725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107099374948797234564414533 20081132802899481480827725)
            ·
              refine ⟨7530424801087305555310397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20081132802899481480827725 7530424801087305555310397)
              ·
                refine ⟨2823909300407739583241399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7530424801087305555310397 2823909300407739583241399)
                ·
                  refine ⟨4235863950611609374862099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823909300407739583241399 4235863950611609374862099)
                  ·
                    refine ⟨6353795925917414062293149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4235863950611609374862099 6353795925917414062293149)
                    ·
                      refine ⟨2382673472219030273359931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6353795925917414062293149 2382673472219030273359931)
                      ·
                        rfl

theorem cell23_4640240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 1, 1, 3].length) (baseStart_4640240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640240 prefixEnd_4640240 := by exact prefixLift 4640240
  have htrace : WordTrace (prefixWord ++ tailWord_4640240) baseStart_4640240 baseEnd_4640240 := by
    simpa [prefixWord, tailWord_4640240, baseEnd_4640240] using wordTrace_append hprefix tailTrace_4640240
  have hstable : (prefixWord ++ tailWord_4640240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640240).length < 2 ^ (prefixWord ++ tailWord_4640240).sum := by decide
  have hdescent : baseEnd_4640240 < baseStart_4640240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640257 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_4640257 : Nat := 118140960795 + 4640257 * 2 ^ 59
def prefixEnd_4640257 : Nat := 4983230072969 + 3 ^ 40 * 4640257 * 2
def baseEnd_4640257 : Nat := 2382682201390156706847353

theorem tailTrace_4640257 : CollatzResearch.WordTrace tailWord_4640257 prefixEnd_4640257 2382682201390156706847353 := by
  unfold tailWord_4640257
  simp only [CollatzResearch.WordTrace]
  refine ⟨169244076750148856647135025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112829384500099237764756683 169244076750148856647135025)
  ·
    refine ⟨126933057562611642485351269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169244076750148856647135025 126933057562611642485351269)
    ·
      refine ⟨23799948292989682966003363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126933057562611642485351269 23799948292989682966003363)
      ·
        refine ⟨35699922439484524449005045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23799948292989682966003363 35699922439484524449005045)
        ·
          refine ⟨3346867728701674167094223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35699922439484524449005045 3346867728701674167094223)
          ·
            refine ⟨5020301593052511250641335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346867728701674167094223 5020301593052511250641335)
            ·
              refine ⟨7530452389578766875962003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5020301593052511250641335 7530452389578766875962003)
              ·
                refine ⟨11295678584368150313943005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7530452389578766875962003 11295678584368150313943005)
                ·
                  refine ⟨4235879469138056367728627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11295678584368150313943005 4235879469138056367728627)
                  ·
                    refine ⟨6353819203707084551592941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4235879469138056367728627 6353819203707084551592941)
                    ·
                      refine ⟨2382682201390156706847353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6353819203707084551592941 2382682201390156706847353)
                      ·
                        rfl

theorem cell23_4640257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_4640257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640257 prefixEnd_4640257 := by exact prefixLift 4640257
  have htrace : WordTrace (prefixWord ++ tailWord_4640257) baseStart_4640257 baseEnd_4640257 := by
    simpa [prefixWord, tailWord_4640257, baseEnd_4640257] using wordTrace_append hprefix tailTrace_4640257
  have hstable : (prefixWord ++ tailWord_4640257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640257).length < 2 ^ (prefixWord ++ tailWord_4640257).sum := by decide
  have hdescent : baseEnd_4640257 < baseStart_4640257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640259 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 4]
def baseStart_4640259 : Nat := 118140960795 + 4640259 * 2 ^ 59
def prefixEnd_4640259 : Nat := 4983230072969 + 3 ^ 40 * 4640259 * 2
def baseEnd_4640259 : Nat := 2382683228351465699022343

theorem tailTrace_4640259 : CollatzResearch.WordTrace tailWord_4640259 prefixEnd_4640259 2382683228351465699022343 := by
  unfold tailWord_4640259
  simp only [CollatzResearch.WordTrace]
  refine ⟨169244149696141610988707831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112829433130761073992471887 169244149696141610988707831)
  ·
    refine ⟨253866224544212416483061747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169244149696141610988707831 253866224544212416483061747)
    ·
      refine ⟨380799336816318624724592621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253866224544212416483061747 380799336816318624724592621)
      ·
        refine ⟨142799751306119484271722233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 380799336816318624724592621 142799751306119484271722233)
        ·
          refine ⟨107099813479589613203791675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142799751306119484271722233 107099813479589613203791675)
          ·
            refine ⟨160649720219384419805687513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107099813479589613203791675 160649720219384419805687513)
            ·
              refine ⟨120487290164538314854265635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160649720219384419805687513 120487290164538314854265635)
              ·
                refine ⟨180730935246807472281398453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120487290164538314854265635 180730935246807472281398453)
                ·
                  refine ⟨16943525179388200526381105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 180730935246807472281398453 16943525179388200526381105)
                  ·
                    refine ⟨12707643884541150394785829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16943525179388200526381105 12707643884541150394785829)
                    ·
                      refine ⟨2382683228351465699022343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12707643884541150394785829 2382683228351465699022343)
                      ·
                        rfl

theorem cell23_4640259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_4640259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640259 prefixEnd_4640259 := by exact prefixLift 4640259
  have htrace : WordTrace (prefixWord ++ tailWord_4640259) baseStart_4640259 baseEnd_4640259 := by
    simpa [prefixWord, tailWord_4640259, baseEnd_4640259] using wordTrace_append hprefix tailTrace_4640259
  have hstable : (prefixWord ++ tailWord_4640259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640259).length < 2 ^ (prefixWord ++ tailWord_4640259).sum := by decide
  have hdescent : baseEnd_4640259 < baseStart_4640259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640266 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_4640266 : Nat := 118140960795 + 4640266 * 2 ^ 59
def prefixEnd_4640266 : Nat := 4983230072969 + 3 ^ 40 * 4640266 * 2
def baseEnd_4640266 : Nat := 2382686822716047171634811

theorem tailTrace_4640266 : CollatzResearch.WordTrace tailWord_4640266 prefixEnd_4640266 2382686822716047171634811 := by
  unfold tailWord_4640266
  simp only [CollatzResearch.WordTrace]
  refine ⟨42311101251779062796053163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112829603338077500789475101 42311101251779062796053163)
  ·
    refine ⟨63466651877668594194079745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42311101251779062796053163 63466651877668594194079745)
    ·
      refine ⟨47599988908251445645559809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63466651877668594194079745 47599988908251445645559809)
      ·
        refine ⟨35699991681188584234169857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47599988908251445645559809 35699991681188584234169857)
        ·
          refine ⟨26774993760891438175627393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35699991681188584234169857 26774993760891438175627393)
          ·
            refine ⟨20081245320668578631720545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26774993760891438175627393 20081245320668578631720545)
            ·
              refine ⟨15060933990501433973790409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20081245320668578631720545 15060933990501433973790409)
              ·
                refine ⟨11295700492876075480342807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15060933990501433973790409 11295700492876075480342807)
                ·
                  refine ⟨16943550739314113220514211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11295700492876075480342807 16943550739314113220514211)
                  ·
                    refine ⟨25415326108971169830771317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16943550739314113220514211 25415326108971169830771317)
                    ·
                      refine ⟨2382686822716047171634811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25415326108971169830771317 2382686822716047171634811)
                      ·
                        rfl

theorem cell23_4640266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_4640266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640266 prefixEnd_4640266 := by exact prefixLift 4640266
  have htrace : WordTrace (prefixWord ++ tailWord_4640266) baseStart_4640266 baseEnd_4640266 := by
    simpa [prefixWord, tailWord_4640266, baseEnd_4640266] using wordTrace_append hprefix tailTrace_4640266
  have hstable : (prefixWord ++ tailWord_4640266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640266).length < 2 ^ (prefixWord ++ tailWord_4640266).sum := by decide
  have hdescent : baseEnd_4640266 < baseStart_4640266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640280 : List Nat := [2, 1, 2, 3, 4, 2, 1, 2, 1, 1, 4]
def baseStart_4640280 : Nat := 118140960795 + 4640280 * 2 ^ 59
def prefixEnd_4640280 : Nat := 4983230072969 + 3 ^ 40 * 4640280 * 2
def baseEnd_4640280 : Nat := 2382694011445210116859747

theorem tailTrace_4640280 : CollatzResearch.WordTrace tailWord_4640280 prefixEnd_4640280 2382694011445210116859747 := by
  unfold tailWord_4640280
  simp only [CollatzResearch.WordTrace]
  refine ⟨84622457814532765787611147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112829943752710354383481529 84622457814532765787611147)
  ·
    refine ⟨126933686721799148681416721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84622457814532765787611147 126933686721799148681416721)
    ·
      refine ⟨95200265041349361511062541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126933686721799148681416721 95200265041349361511062541)
      ·
        refine ⟨35700099390506010566648453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95200265041349361511062541 35700099390506010566648453)
        ·
          refine ⟨6693768635719876981246585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35700099390506010566648453 6693768635719876981246585)
          ·
            refine ⟨5020326476789907735934939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6693768635719876981246585 5020326476789907735934939)
            ·
              refine ⟨7530489715184861603902409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5020326476789907735934939 7530489715184861603902409)
              ·
                refine ⟨5647867286388646202926807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7530489715184861603902409 5647867286388646202926807)
                ·
                  refine ⟨8471800929582969304390211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5647867286388646202926807 8471800929582969304390211)
                  ·
                    refine ⟨12707701394374453956585317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8471800929582969304390211 12707701394374453956585317)
                    ·
                      refine ⟨2382694011445210116859747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12707701394374453956585317 2382694011445210116859747)
                      ·
                        rfl

theorem cell23_4640280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_4640280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640280 prefixEnd_4640280 := by exact prefixLift 4640280
  have htrace : WordTrace (prefixWord ++ tailWord_4640280) baseStart_4640280 baseEnd_4640280 := by
    simpa [prefixWord, tailWord_4640280, baseEnd_4640280] using wordTrace_append hprefix tailTrace_4640280
  have hstable : (prefixWord ++ tailWord_4640280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640280).length < 2 ^ (prefixWord ++ tailWord_4640280).sum := by decide
  have hdescent : baseEnd_4640280 < baseStart_4640280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640339 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 5]
def baseStart_4640339 : Nat := 118140960795 + 4640339 * 2 ^ 59
def prefixEnd_4640339 : Nat := 4983230072969 + 3 ^ 40 * 4640339 * 2
def baseEnd_4640339 : Nat := 2382724306803825386021975

theorem tailTrace_4640339 : CollatzResearch.WordTrace tailWord_4640339 prefixEnd_4640339 2382724306803825386021975 := by
  unfold tailWord_4640339
  simp only [CollatzResearch.WordTrace]
  refine ⟨169247067535851784651620071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112831378357234523101080047 169247067535851784651620071)
  ·
    refine ⟨253870601303777676977430107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169247067535851784651620071 253870601303777676977430107)
    ·
      refine ⟨380805901955666515466145161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253870601303777676977430107 380805901955666515466145161)
      ·
        refine ⟨285604426466749886599608871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380805901955666515466145161 285604426466749886599608871)
        ·
          refine ⟨428406639700124829899413307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285604426466749886599608871 428406639700124829899413307)
          ·
            refine ⟨642609959550187244849119961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428406639700124829899413307 642609959550187244849119961)
            ·
              refine ⟨481957469662640433636839971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642609959550187244849119961 481957469662640433636839971)
              ·
                refine ⟨722936204493960650455259957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481957469662640433636839971 722936204493960650455259957)
                ·
                  refine ⟨67775269171308810980180621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 722936204493960650455259957 67775269171308810980180621)
                  ·
                    refine ⟨25415725939240804117567733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67775269171308810980180621 25415725939240804117567733)
                    ·
                      refine ⟨2382724306803825386021975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25415725939240804117567733 2382724306803825386021975)
                      ·
                        rfl

theorem cell23_4640339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_4640339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640339 prefixEnd_4640339 := by exact prefixLift 4640339
  have htrace : WordTrace (prefixWord ++ tailWord_4640339) baseStart_4640339 baseEnd_4640339 := by
    simpa [prefixWord, tailWord_4640339, baseEnd_4640339] using wordTrace_append hprefix tailTrace_4640339
  have hstable : (prefixWord ++ tailWord_4640339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640339).length < 2 ^ (prefixWord ++ tailWord_4640339).sum := by decide
  have hdescent : baseEnd_4640339 < baseStart_4640339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640340 : List Nat := [2, 4, 1, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_4640340 : Nat := 118140960795 + 4640340 * 2 ^ 59
def prefixEnd_4640340 : Nat := 4983230072969 + 3 ^ 40 * 4640340 * 2
def baseEnd_4640340 : Nat := 2382724820284479882109471

theorem tailTrace_4640340 : CollatzResearch.WordTrace tailWord_4640340 prefixEnd_4640340 2382724820284479882109471 := by
  unfold tailWord_4640340
  simp only [CollatzResearch.WordTrace]
  refine ⟨84623552004424080911203237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112831402672565441214937649 84623552004424080911203237)
  ·
    refine ⟨15866916000829515170850607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84623552004424080911203237 15866916000829515170850607)
    ·
      refine ⟨23800374001244272756275911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15866916000829515170850607 23800374001244272756275911)
      ·
        refine ⟨35700561001866409134413867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23800374001244272756275911 35700561001866409134413867)
        ·
          refine ⟨53550841502799613701620801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35700561001866409134413867 53550841502799613701620801)
          ·
            refine ⟨40163131127099710276215601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53550841502799613701620801 40163131127099710276215601)
            ·
              refine ⟨30122348345324782707161701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40163131127099710276215601 30122348345324782707161701)
              ·
                refine ⟨5647940314748396757592819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30122348345324782707161701 5647940314748396757592819)
                ·
                  refine ⟨8471910472122595136389229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5647940314748396757592819 8471910472122595136389229)
                  ·
                    refine ⟨3176966427045973176145961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8471910472122595136389229 3176966427045973176145961)
                    ·
                      refine ⟨2382724820284479882109471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176966427045973176145961 2382724820284479882109471)
                      ·
                        rfl

theorem cell23_4640340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_4640340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640340 prefixEnd_4640340 := by exact prefixLift 4640340
  have htrace : WordTrace (prefixWord ++ tailWord_4640340) baseStart_4640340 baseEnd_4640340 := by
    simpa [prefixWord, tailWord_4640340, baseEnd_4640340] using wordTrace_append hprefix tailTrace_4640340
  have hstable : (prefixWord ++ tailWord_4640340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640340).length < 2 ^ (prefixWord ++ tailWord_4640340).sum := by decide
  have hdescent : baseEnd_4640340 < baseStart_4640340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640353 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 1, 4, 2]
def baseStart_4640353 : Nat := 118140960795 + 4640353 * 2 ^ 59
def prefixEnd_4640353 : Nat := 4983230072969 + 3 ^ 40 * 4640353 * 2
def baseEnd_4640353 : Nat := 2382731495532988331246911

theorem tailTrace_4640353 : CollatzResearch.WordTrace tailWord_4640353 prefixEnd_4640353 2382731495532988331246911 := by
  unfold tailWord_4640353
  simp only [CollatzResearch.WordTrace]
  refine ⟨169247578157801065042629713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112831718771867376695086475 169247578157801065042629713)
  ·
    refine ⟨126935683618350798781972285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169247578157801065042629713 126935683618350798781972285)
    ·
      refine ⟨47600881356881549543239607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126935683618350798781972285 47600881356881549543239607)
      ·
        refine ⟨71401322035322324314859411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47600881356881549543239607 71401322035322324314859411)
        ·
          refine ⟨107101983052983486472289117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71401322035322324314859411 107101983052983486472289117)
          ·
            refine ⟨40163243644868807427108419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107101983052983486472289117 40163243644868807427108419)
            ·
              refine ⟨60244865467303211140662629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40163243644868807427108419 60244865467303211140662629)
              ·
                refine ⟨11295912275119352088874243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60244865467303211140662629 11295912275119352088874243)
                ·
                  refine ⟨16943868412679028133311365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11295912275119352088874243 16943868412679028133311365)
                  ·
                    refine ⟨3176975327377317774995881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16943868412679028133311365 3176975327377317774995881)
                    ·
                      refine ⟨2382731495532988331246911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176975327377317774995881 2382731495532988331246911)
                      ·
                        rfl

theorem cell23_4640353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_4640353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640353 prefixEnd_4640353 := by exact prefixLift 4640353
  have htrace : WordTrace (prefixWord ++ tailWord_4640353) baseStart_4640353 baseEnd_4640353 := by
    simpa [prefixWord, tailWord_4640353, baseEnd_4640353] using wordTrace_append hprefix tailTrace_4640353
  have hstable : (prefixWord ++ tailWord_4640353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640353).length < 2 ^ (prefixWord ++ tailWord_4640353).sum := by decide
  have hdescent : baseEnd_4640353 < baseStart_4640353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640357 : List Nat := [1, 3, 1, 3, 3, 1, 4, 1, 1, 3, 2]
def baseStart_4640357 : Nat := 118140960795 + 4640357 * 2 ^ 59
def prefixEnd_4640357 : Nat := 4983230072969 + 3 ^ 40 * 4640357 * 2
def baseEnd_4640357 : Nat := 2382733549455606315596893

theorem tailTrace_4640357 : CollatzResearch.WordTrace tailWord_4640357 prefixEnd_4640357 2382733549455606315596893 := by
  unfold tailWord_4640357
  simp only [CollatzResearch.WordTrace]
  refine ⟨169247724049786573725775325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112831816033191049150516883 169247724049786573725775325)
  ·
    refine ⟨63467896518669965147165747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169247724049786573725775325 63467896518669965147165747)
    ·
      refine ⟨95201844778004947720748621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63467896518669965147165747 95201844778004947720748621)
      ·
        refine ⟨35700691791751855395280733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95201844778004947720748621 35700691791751855395280733)
        ·
          refine ⟨13387759421906945773230275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35700691791751855395280733 13387759421906945773230275)
          ·
            refine ⟨20081639132860418659845413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13387759421906945773230275 20081639132860418659845413)
            ·
              refine ⟨3765307337411328498721015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20081639132860418659845413 3765307337411328498721015)
              ·
                refine ⟨5647961006116992748081523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3765307337411328498721015 5647961006116992748081523)
                ·
                  refine ⟨8471941509175489122122285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5647961006116992748081523 8471941509175489122122285)
                  ·
                    refine ⟨3176978065940808420795857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8471941509175489122122285 3176978065940808420795857)
                    ·
                      refine ⟨2382733549455606315596893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3176978065940808420795857 2382733549455606315596893)
                      ·
                        rfl

theorem cell23_4640357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_4640357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640357 prefixEnd_4640357 := by exact prefixLift 4640357
  have htrace : WordTrace (prefixWord ++ tailWord_4640357) baseStart_4640357 baseEnd_4640357 := by
    simpa [prefixWord, tailWord_4640357, baseEnd_4640357] using wordTrace_append hprefix tailTrace_4640357
  have hstable : (prefixWord ++ tailWord_4640357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640357).length < 2 ^ (prefixWord ++ tailWord_4640357).sum := by decide
  have hdescent : baseEnd_4640357 < baseStart_4640357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640413 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_4640413 : Nat := 118140960795 + 4640413 * 2 ^ 59
def prefixEnd_4640413 : Nat := 4983230072969 + 3 ^ 40 * 4640413 * 2
def baseEnd_4640413 : Nat := 2382762304372258096496635

theorem tailTrace_4640413 : CollatzResearch.WordTrace tailWord_4640413 prefixEnd_4640413 2382762304372258096496635 := by
  unfold tailWord_4640413
  simp only [CollatzResearch.WordTrace]
  refine ⟨169249766537583695289813893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112833177691722463526542595 169249766537583695289813893)
  ·
    refine ⟨31734331225796942866840105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169249766537583695289813893 31734331225796942866840105)
    ·
      refine ⟨23800748419347707150130079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31734331225796942866840105 23800748419347707150130079)
      ·
        refine ⟨35701122629021560725195119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23800748419347707150130079 35701122629021560725195119)
        ·
          refine ⟨53551683943532341087792679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35701122629021560725195119 53551683943532341087792679)
          ·
            refine ⟨80327525915298511631689019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53551683943532341087792679 80327525915298511631689019)
            ·
              refine ⟨120491288872947767447533529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80327525915298511631689019 120491288872947767447533529)
              ·
                refine ⟨90368466654710825585650147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120491288872947767447533529 90368466654710825585650147)
                ·
                  refine ⟨135552699982066238378475221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90368466654710825585650147 135552699982066238378475221)
                  ·
                    refine ⟨3177016405829677461995513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 135552699982066238378475221 3177016405829677461995513)
                    ·
                      refine ⟨2382762304372258096496635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177016405829677461995513 2382762304372258096496635)
                      ·
                        rfl

theorem cell23_4640413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_4640413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640413 prefixEnd_4640413 := by exact prefixLift 4640413
  have htrace : WordTrace (prefixWord ++ tailWord_4640413) baseStart_4640413 baseEnd_4640413 := by
    simpa [prefixWord, tailWord_4640413, baseEnd_4640413] using wordTrace_append hprefix tailTrace_4640413
  have hstable : (prefixWord ++ tailWord_4640413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640413).length < 2 ^ (prefixWord ++ tailWord_4640413).sum := by decide
  have hdescent : baseEnd_4640413 < baseStart_4640413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640438 : List Nat := [5, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_4640438 : Nat := 118140960795 + 4640438 * 2 ^ 59
def prefixEnd_4640438 : Nat := 4983230072969 + 3 ^ 40 * 4640438 * 2
def baseEnd_4640438 : Nat := 2382775141388620498684021

theorem tailTrace_4640438 : CollatzResearch.WordTrace tailWord_4640438 prefixEnd_4640438 2382775141388620498684021 := by
  unfold tailWord_4640438
  simp only [CollatzResearch.WordTrace]
  refine ⟨10578167397655820284967123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112833785574995416372982645 10578167397655820284967123)
  ·
    refine ⟨15867251096483730427450685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10578167397655820284967123 15867251096483730427450685)
    ·
      refine ⟨5950219161181398910294007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15867251096483730427450685 5950219161181398910294007)
      ·
        refine ⟨8925328741772098365441011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5950219161181398910294007 8925328741772098365441011)
        ·
          refine ⟨13387993112658147548161517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8925328741772098365441011 13387993112658147548161517)
          ·
            refine ⟨5020497417246805330560569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13387993112658147548161517 5020497417246805330560569)
            ·
              refine ⟨3765373062935103997920427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5020497417246805330560569 3765373062935103997920427)
              ·
                refine ⟨5648059594402655996880641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3765373062935103997920427 5648059594402655996880641)
                ·
                  refine ⟨4236044695801991997660481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5648059594402655996880641 4236044695801991997660481)
                  ·
                    refine ⟨3177033521851493998245361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4236044695801991997660481 3177033521851493998245361)
                    ·
                      refine ⟨2382775141388620498684021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177033521851493998245361 2382775141388620498684021)
                      ·
                        rfl

theorem cell23_4640438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_4640438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640438 prefixEnd_4640438 := by exact prefixLift 4640438
  have htrace : WordTrace (prefixWord ++ tailWord_4640438) baseStart_4640438 baseEnd_4640438 := by
    simpa [prefixWord, tailWord_4640438, baseEnd_4640438] using wordTrace_append hprefix tailTrace_4640438
  have hstable : (prefixWord ++ tailWord_4640438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640438).length < 2 ^ (prefixWord ++ tailWord_4640438).sum := by decide
  have hdescent : baseEnd_4640438 < baseStart_4640438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640443 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 2, 4, 2]
def baseStart_4640443 : Nat := 118140960795 + 4640443 * 2 ^ 59
def prefixEnd_4640443 : Nat := 4983230072969 + 3 ^ 40 * 4640443 * 2
def baseEnd_4640443 : Nat := 2382777708791892979121497

theorem tailTrace_4640443 : CollatzResearch.WordTrace tailWord_4640443 prefixEnd_4640443 2382777708791892979121497 := by
  unfold tailWord_4640443
  simp only [CollatzResearch.WordTrace]
  refine ⟨169250860727475010413405983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112833907151650006942270655 169250860727475010413405983)
  ·
    refine ⟨253876291091212515620108975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169250860727475010413405983 253876291091212515620108975)
    ·
      refine ⟨380814436636818773430163463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253876291091212515620108975 380814436636818773430163463)
      ·
        refine ⟨571221654955228160145245195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380814436636818773430163463 571221654955228160145245195)
        ·
          refine ⟨856832482432842240217867793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571221654955228160145245195 856832482432842240217867793)
          ·
            refine ⟨642624361824631680163400845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 856832482432842240217867793 642624361824631680163400845)
            ·
              refine ⟨240984135684236880061275317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 642624361824631680163400845 240984135684236880061275317)
              ·
                refine ⟨22592262720397207505744561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 240984135684236880061275317 22592262720397207505744561)
                ·
                  refine ⟨16944197040297905629308421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22592262720397207505744561 16944197040297905629308421)
                  ·
                    refine ⟨3177036945055857305495329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16944197040297905629308421 3177036945055857305495329)
                    ·
                      refine ⟨2382777708791892979121497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177036945055857305495329 2382777708791892979121497)
                      ·
                        rfl

theorem cell23_4640443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 4, 2].length) (baseStart_4640443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640443 prefixEnd_4640443 := by exact prefixLift 4640443
  have htrace : WordTrace (prefixWord ++ tailWord_4640443) baseStart_4640443 baseEnd_4640443 := by
    simpa [prefixWord, tailWord_4640443, baseEnd_4640443] using wordTrace_append hprefix tailTrace_4640443
  have hstable : (prefixWord ++ tailWord_4640443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640443).length < 2 ^ (prefixWord ++ tailWord_4640443).sum := by decide
  have hdescent : baseEnd_4640443 < baseStart_4640443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640506 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_4640506 : Nat := 118140960795 + 4640506 * 2 ^ 59
def prefixEnd_4640506 : Nat := 4983230072969 + 3 ^ 40 * 4640506 * 2
def baseEnd_4640506 : Nat := 2382810058073126232633707

theorem tailTrace_4640506 : CollatzResearch.WordTrace tailWord_4640506 prefixEnd_4640506 2382810058073126232633707 := by
  unfold tailWord_4640506
  simp only [CollatzResearch.WordTrace]
  refine ⟨42313289631561693043237343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112835439017497848115299581 42313289631561693043237343)
  ·
    refine ⟨63469934447342539564856015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42313289631561693043237343 63469934447342539564856015)
    ·
      refine ⟨95204901671013809347284023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63469934447342539564856015 95204901671013809347284023)
      ·
        refine ⟨142807352506520714020926035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95204901671013809347284023 142807352506520714020926035)
        ·
          refine ⟨214211028759781071031389053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142807352506520714020926035 214211028759781071031389053)
          ·
            refine ⟨80329135784917901636770895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214211028759781071031389053 80329135784917901636770895)
            ·
              refine ⟨120493703677376852455156343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80329135784917901636770895 120493703677376852455156343)
              ·
                refine ⟨180740555516065278682734515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120493703677376852455156343 180740555516065278682734515)
                ·
                  refine ⟨271110833274097918024101773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180740555516065278682734515 271110833274097918024101773)
                  ·
                    refine ⟨101666562477786719259038165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 271110833274097918024101773 101666562477786719259038165)
                    ·
                      refine ⟨2382810058073126232633707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101666562477786719259038165 2382810058073126232633707)
                      ·
                        rfl

theorem cell23_4640506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_4640506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640506 prefixEnd_4640506 := by exact prefixLift 4640506
  have htrace : WordTrace (prefixWord ++ tailWord_4640506) baseStart_4640506 baseEnd_4640506 := by
    simpa [prefixWord, tailWord_4640506, baseEnd_4640506] using wordTrace_append hprefix tailTrace_4640506
  have hstable : (prefixWord ++ tailWord_4640506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640506).length < 2 ^ (prefixWord ++ tailWord_4640506).sum := by decide
  have hdescent : baseEnd_4640506 < baseStart_4640506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640513 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 3, 5]
def baseStart_4640513 : Nat := 118140960795 + 4640513 * 2 ^ 59
def prefixEnd_4640513 : Nat := 4983230072969 + 3 ^ 40 * 4640513 * 2
def baseEnd_4640513 : Nat := 794271217479235901748725

theorem tailTrace_4640513 : CollatzResearch.WordTrace tailWord_4640513 prefixEnd_4640513 794271217479235901748725 := by
  unfold tailWord_4640513
  simp only [CollatzResearch.WordTrace]
  refine ⟨169253413837221412368454193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112835609224814274912302795 169253413837221412368454193)
  ·
    refine ⟨126940060377916059276340645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169253413837221412368454193 126940060377916059276340645)
    ·
      refine ⟨23801261320859261114313871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126940060377916059276340645 23801261320859261114313871)
      ·
        refine ⟨35701891981288891671470807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23801261320859261114313871 35701891981288891671470807)
        ·
          refine ⟨53552837971933337507206211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35701891981288891671470807 53552837971933337507206211)
          ·
            refine ⟨80329256957900006260809317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53552837971933337507206211 80329256957900006260809317)
            ·
              refine ⟨15061735679606251173901747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80329256957900006260809317 15061735679606251173901747)
              ·
                refine ⟨22592603519409376760852621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15061735679606251173901747 22592603519409376760852621)
                ·
                  refine ⟨8472226319778516285319733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22592603519409376760852621 8472226319778516285319733)
                  ·
                    refine ⟨794271217479235901748725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8472226319778516285319733 794271217479235901748725)
                    ·
                      rfl

theorem cell23_4640513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_4640513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640513 prefixEnd_4640513 := by exact prefixLift 4640513
  have htrace : WordTrace (prefixWord ++ tailWord_4640513) baseStart_4640513 baseEnd_4640513 := by
    simpa [prefixWord, tailWord_4640513, baseEnd_4640513] using wordTrace_append hprefix tailTrace_4640513
  have hstable : (prefixWord ++ tailWord_4640513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640513).length < 2 ^ (prefixWord ++ tailWord_4640513).sum := by decide
  have hdescent : baseEnd_4640513 < baseStart_4640513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640520 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 1, 5, 2]
def baseStart_4640520 : Nat := 118140960795 + 4640520 * 2 ^ 59
def prefixEnd_4640520 : Nat := 4983230072969 + 3 ^ 40 * 4640520 * 2
def baseEnd_4640520 : Nat := 2382817246802289177858643

theorem tailTrace_4640520 : CollatzResearch.WordTrace tailWord_4640520 prefixEnd_4640520 2382817246802289177858643 := by
  unfold tailWord_4640520
  simp only [CollatzResearch.WordTrace]
  refine ⟨84626834574098026281979507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112835779432130701709306009 84626834574098026281979507)
  ·
    refine ⟨126940251861147039422969261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84626834574098026281979507 126940251861147039422969261)
    ·
      refine ⟨47602594447930139783613473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126940251861147039422969261 47602594447930139783613473)
      ·
        refine ⟨35701945835947604837710105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47602594447930139783613473 35701945835947604837710105)
        ·
          refine ⟨26776459376960703628282579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35701945835947604837710105 26776459376960703628282579)
          ·
            refine ⟨40164689065441055442423869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26776459376960703628282579 40164689065441055442423869)
            ·
              refine ⟨15061758399540395790908951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40164689065441055442423869 15061758399540395790908951)
              ·
                refine ⟨22592637599310593686363427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15061758399540395790908951 22592637599310593686363427)
                ·
                  refine ⟨33888956398965890529545141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22592637599310593686363427 33888956398965890529545141)
                  ·
                    refine ⟨3177089662403052237144857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33888956398965890529545141 3177089662403052237144857)
                    ·
                      refine ⟨2382817246802289177858643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177089662403052237144857 2382817246802289177858643)
                      ·
                        rfl

theorem cell23_4640520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_4640520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640520 prefixEnd_4640520 := by exact prefixLift 4640520
  have htrace : WordTrace (prefixWord ++ tailWord_4640520) baseStart_4640520 baseEnd_4640520 := by
    simpa [prefixWord, tailWord_4640520, baseEnd_4640520] using wordTrace_append hprefix tailTrace_4640520
  have hstable : (prefixWord ++ tailWord_4640520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640520).length < 2 ^ (prefixWord ++ tailWord_4640520).sum := by decide
  have hdescent : baseEnd_4640520 < baseStart_4640520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640601 : List Nat := [1, 2, 1, 2, 2, 3, 5, 2, 1, 2, 2]
def baseStart_4640601 : Nat := 118140960795 + 4640601 * 2 ^ 59
def prefixEnd_4640601 : Nat := 4983230072969 + 3 ^ 40 * 4640601 * 2
def baseEnd_4640601 : Nat := 2382858838735303360945771

theorem tailTrace_4640601 : CollatzResearch.WordTrace tailWord_4640601 prefixEnd_4640601 2382858838735303360945771 := by
  unfold tailWord_4640601
  simp only [CollatzResearch.WordTrace]
  refine ⟨169256623460902603397657657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112837748973935068931771771 169256623460902603397657657)
  ·
    refine ⟨126942467595676952548243243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169256623460902603397657657 126942467595676952548243243)
    ·
      refine ⟨190413701393515428822364865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126942467595676952548243243 190413701393515428822364865)
      ·
        refine ⟨142810276045136571616773649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190413701393515428822364865 142810276045136571616773649)
        ·
          refine ⟨107107707033852428712580237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142810276045136571616773649 107107707033852428712580237)
          ·
            refine ⟨40165390137694660767217589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107107707033852428712580237 40165390137694660767217589)
            ·
              refine ⟨3765505325408874446926649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40165390137694660767217589 3765505325408874446926649)
              ·
                refine ⟨2824128994056655835194987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3765505325408874446926649 2824128994056655835194987)
                ·
                  refine ⟨4236193491084983752792481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2824128994056655835194987 4236193491084983752792481)
                  ·
                    refine ⟨3177145118313737814594361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4236193491084983752792481 3177145118313737814594361)
                    ·
                      refine ⟨2382858838735303360945771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177145118313737814594361 2382858838735303360945771)
                      ·
                        rfl

theorem cell23_4640601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 1, 2, 2].length) (baseStart_4640601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640601 prefixEnd_4640601 := by exact prefixLift 4640601
  have htrace : WordTrace (prefixWord ++ tailWord_4640601) baseStart_4640601 baseEnd_4640601 := by
    simpa [prefixWord, tailWord_4640601, baseEnd_4640601] using wordTrace_append hprefix tailTrace_4640601
  have hstable : (prefixWord ++ tailWord_4640601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640601).length < 2 ^ (prefixWord ++ tailWord_4640601).sum := by decide
  have hdescent : baseEnd_4640601 < baseStart_4640601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640611 : List Nat := [1, 1, 1, 5, 5, 1, 2, 1, 2, 4]
def baseStart_4640611 : Nat := 118140960795 + 4640611 * 2 ^ 59
def prefixEnd_4640611 : Nat := 4983230072969 + 3 ^ 40 * 4640611 * 2
def baseEnd_4640611 : Nat := 794287991180616107273575

theorem tailTrace_4640611 : CollatzResearch.WordTrace tailWord_4640611 prefixEnd_4640611 794287991180616107273575 := by
  unfold tailWord_4640611
  simp only [CollatzResearch.WordTrace]
  refine ⟨169256988190866375105521687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112837992127244250070347791 169256988190866375105521687)
  ·
    refine ⟨253885482286299562658282531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169256988190866375105521687 253885482286299562658282531)
    ·
      refine ⟨380828223429449343987423797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253885482286299562658282531 380828223429449343987423797)
      ·
        refine ⟨35702645946510875998820981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 380828223429449343987423797 35702645946510875998820981)
        ·
          refine ⟨3347123057485394624889467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35702645946510875998820981 3347123057485394624889467)
          ·
            refine ⟨5020684586228091937334201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347123057485394624889467 5020684586228091937334201)
            ·
              refine ⟨3765513439671068953000651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5020684586228091937334201 3765513439671068953000651)
              ·
                refine ⟨5648270159506603429500977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3765513439671068953000651 5648270159506603429500977)
                ·
                  refine ⟨4236202619629952572125733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5648270159506603429500977 4236202619629952572125733)
                  ·
                    refine ⟨794287991180616107273575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4236202619629952572125733 794287991180616107273575)
                    ·
                      rfl

theorem cell23_4640611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 2, 4].length) (baseStart_4640611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640611 prefixEnd_4640611 := by exact prefixLift 4640611
  have htrace : WordTrace (prefixWord ++ tailWord_4640611) baseStart_4640611 baseEnd_4640611 := by
    simpa [prefixWord, tailWord_4640611, baseEnd_4640611] using wordTrace_append hprefix tailTrace_4640611
  have hstable : (prefixWord ++ tailWord_4640611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640611).length < 2 ^ (prefixWord ++ tailWord_4640611).sum := by decide
  have hdescent : baseEnd_4640611 < baseStart_4640611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640657 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 4, 2, 2]
def baseStart_4640657 : Nat := 118140960795 + 4640657 * 2 ^ 59
def prefixEnd_4640657 : Nat := 4983230072969 + 3 ^ 40 * 4640657 * 2
def baseEnd_4640657 : Nat := 2382887593651955141845513

theorem tailTrace_4640657 : CollatzResearch.WordTrace tailWord_4640657 prefixEnd_4640657 2382887593651955141845513 := by
  unfold tailWord_4640657
  simp only [CollatzResearch.WordTrace]
  refine ⟨169258665948699724961696225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112839110632466483307797483 169258665948699724961696225)
  ·
    refine ⟨126943999461524793721272169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169258665948699724961696225 126943999461524793721272169)
    ·
      refine ⟨95207999596143595290954127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126943999461524793721272169 95207999596143595290954127)
      ·
        refine ⟨142811999394215392936431191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95207999596143595290954127 142811999394215392936431191)
        ·
          refine ⟨214217999091323089404646787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142811999394215392936431191 214217999091323089404646787)
          ·
            refine ⟨321326998636984634106970181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214217999091323089404646787 321326998636984634106970181)
            ·
              refine ⟨60248812244434618895056909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 321326998636984634106970181 60248812244434618895056909)
              ·
                refine ⟨22593304591662982085646341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60248812244434618895056909 22593304591662982085646341)
                ·
                  refine ⟨4236244610936809141058689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22593304591662982085646341 4236244610936809141058689)
                  ·
                    refine ⟨3177183458202606855794017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4236244610936809141058689 3177183458202606855794017)
                    ·
                      refine ⟨2382887593651955141845513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177183458202606855794017 2382887593651955141845513)
                      ·
                        rfl

theorem cell23_4640657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 2, 2].length) (baseStart_4640657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640657 prefixEnd_4640657 := by exact prefixLift 4640657
  have htrace : WordTrace (prefixWord ++ tailWord_4640657) baseStart_4640657 baseEnd_4640657 := by
    simpa [prefixWord, tailWord_4640657, baseEnd_4640657] using wordTrace_append hprefix tailTrace_4640657
  have hstable : (prefixWord ++ tailWord_4640657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640657).length < 2 ^ (prefixWord ++ tailWord_4640657).sum := by decide
  have hdescent : baseEnd_4640657 < baseStart_4640657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640697 : List Nat := [1, 2, 1, 4, 2, 1, 4, 3, 5]
def baseStart_4640697 : Nat := 118140960795 + 4640697 * 2 ^ 59
def prefixEnd_4640697 : Nat := 4983230072969 + 3 ^ 40 * 4640697 * 2
def baseEnd_4640697 : Nat := 264767570319792776149481

theorem tailTrace_4640697 : CollatzResearch.WordTrace tailWord_4640697 prefixEnd_4640697 264767570319792776149481 := by
  unfold tailWord_4640697
  simp only [CollatzResearch.WordTrace]
  refine ⟨169260124868554811793152345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112840083245703207862101563 169260124868554811793152345)
  ·
    refine ⟨126945093651416108844864259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169260124868554811793152345 126945093651416108844864259)
    ·
      refine ⟨190417640477124163267296389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126945093651416108844864259 190417640477124163267296389)
      ·
        refine ⟨35703307589460780612618073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190417640477124163267296389 35703307589460780612618073)
        ·
          refine ⟨26777480692095585459463555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35703307589460780612618073 26777480692095585459463555)
          ·
            refine ⟨40166221038143378189195333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26777480692095585459463555 40166221038143378189195333)
            ·
              refine ⟨7531166444651883410474125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40166221038143378189195333 7531166444651883410474125)
              ·
                refine ⟨2824187416744456278927797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7531166444651883410474125 2824187416744456278927797)
                ·
                  refine ⟨264767570319792776149481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2824187416744456278927797 264767570319792776149481)
                  ·
                    rfl

theorem cell23_4640697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 5].length) (baseStart_4640697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640697 prefixEnd_4640697 := by exact prefixLift 4640697
  have htrace : WordTrace (prefixWord ++ tailWord_4640697) baseStart_4640697 baseEnd_4640697 := by
    simpa [prefixWord, tailWord_4640697, baseEnd_4640697] using wordTrace_append hprefix tailTrace_4640697
  have hstable : (prefixWord ++ tailWord_4640697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640697).length < 2 ^ (prefixWord ++ tailWord_4640697).sum := by decide
  have hdescent : baseEnd_4640697 < baseStart_4640697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640787 : List Nat := [1, 1, 1, 2, 1, 4, 6, 1, 6]
def baseStart_4640787 : Nat := 118140960795 + 4640787 * 2 ^ 59
def prefixEnd_4640787 : Nat := 4983230072969 + 3 ^ 40 * 4640787 * 2
def baseEnd_4640787 : Nat := 264772705126337737024435

theorem tailTrace_4640787 : CollatzResearch.WordTrace tailWord_4640787 prefixEnd_4640787 264772705126337737024435 := by
  unfold tailWord_4640787
  simp only [CollatzResearch.WordTrace]
  refine ⟨169263407438228757163928615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112842271625485838109285743 169263407438228757163928615)
  ·
    refine ⟨253895111157343135745892923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169263407438228757163928615 253895111157343135745892923)
    ·
      refine ⟨380842666736014703618839385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253895111157343135745892923 380842666736014703618839385)
      ·
        refine ⟨285632000052011027714129539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380842666736014703618839385 285632000052011027714129539)
        ·
          refine ⟨428448000078016541571194309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285632000052011027714129539 428448000078016541571194309)
          ·
            refine ⟨80334000014628101544598933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 428448000078016541571194309 80334000014628101544598933)
            ·
              refine ⟨3765656250685692259903075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80334000014628101544598933 3765656250685692259903075)
              ·
                refine ⟨5648484376028538389854613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3765656250685692259903075 5648484376028538389854613)
                ·
                  refine ⟨264772705126337737024435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5648484376028538389854613 264772705126337737024435)
                  ·
                    rfl

theorem cell23_4640787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 6].length) (baseStart_4640787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640787 prefixEnd_4640787 := by exact prefixLift 4640787
  have htrace : WordTrace (prefixWord ++ tailWord_4640787) baseStart_4640787 baseEnd_4640787 := by
    simpa [prefixWord, tailWord_4640787, baseEnd_4640787] using wordTrace_append hprefix tailTrace_4640787
  have hstable : (prefixWord ++ tailWord_4640787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640787).length < 2 ^ (prefixWord ++ tailWord_4640787).sum := by decide
  have hdescent : baseEnd_4640787 < baseStart_4640787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640825 : List Nat := [1, 2, 1, 5, 4, 1, 2, 2, 1, 4]
def baseStart_4640825 : Nat := 118140960795 + 4640825 * 2 ^ 59
def prefixEnd_4640825 : Nat := 4983230072969 + 3 ^ 40 * 4640825 * 2
def baseEnd_4640825 : Nat := 794324619467303494848247

theorem tailTrace_4640825 : CollatzResearch.WordTrace tailWord_4640825 prefixEnd_4640825 794324619467303494848247 := by
  unfold tailWord_4640825
  simp only [CollatzResearch.WordTrace]
  refine ⟨169264793412091089653811929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112843195608060726435874619 169264793412091089653811929)
  ·
    refine ⟨126948595059068317240358947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169264793412091089653811929 126948595059068317240358947)
    ·
      refine ⟨190422892588602475860538421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126948595059068317240358947 190422892588602475860538421)
      ·
        refine ⟨17852146180181482111925477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 190422892588602475860538421 17852146180181482111925477)
        ·
          refine ⟨3347277408784027895986027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17852146180181482111925477 3347277408784027895986027)
          ·
            refine ⟨5020916113176041843979041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347277408784027895986027 5020916113176041843979041)
            ·
              refine ⟨3765687084882031382984281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5020916113176041843979041 3765687084882031382984281)
              ·
                refine ⟨2824265313661523537238211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3765687084882031382984281 2824265313661523537238211)
                ·
                  refine ⟨4236397970492285305857317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2824265313661523537238211 4236397970492285305857317)
                  ·
                    refine ⟨794324619467303494848247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4236397970492285305857317 794324619467303494848247)
                    ·
                      rfl

theorem cell23_4640825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 1, 4].length) (baseStart_4640825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640825 prefixEnd_4640825 := by exact prefixLift 4640825
  have htrace : WordTrace (prefixWord ++ tailWord_4640825) baseStart_4640825 baseEnd_4640825 := by
    simpa [prefixWord, tailWord_4640825, baseEnd_4640825] using wordTrace_append hprefix tailTrace_4640825
  have hstable : (prefixWord ++ tailWord_4640825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640825).length < 2 ^ (prefixWord ++ tailWord_4640825).sum := by decide
  have hdescent : baseEnd_4640825 < baseStart_4640825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640837 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 2, 6, 2]
def baseStart_4640837 : Nat := 118140960795 + 4640837 * 2 ^ 59
def prefixEnd_4640837 : Nat := 4983230072969 + 3 ^ 40 * 4640837 * 2
def baseEnd_4640837 : Nat := 2382980020169764437594685

theorem tailTrace_4640837 : CollatzResearch.WordTrace tailWord_4640837 prefixEnd_4640837 2382980020169764437594685 := by
  unfold tailWord_4640837
  simp only [CollatzResearch.WordTrace]
  refine ⟨169265231088047615703248765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112843487392031743802165843 169265231088047615703248765)
  ·
    refine ⟨63474461658017855888718287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169265231088047615703248765 63474461658017855888718287)
    ·
      refine ⟨95211692487026783833077431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63474461658017855888718287 95211692487026783833077431)
      ·
        refine ⟨142817538730540175749616147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95211692487026783833077431 142817538730540175749616147)
        ·
          refine ⟨214226308095810263624424221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142817538730540175749616147 214226308095810263624424221)
          ·
            refine ⟨80334865535928848859159083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214226308095810263624424221 80334865535928848859159083)
            ·
              refine ⟨120502298303893273288738625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80334865535928848859159083 120502298303893273288738625)
              ·
                refine ⟨90376723727919954966553969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120502298303893273288738625 90376723727919954966553969)
                ·
                  refine ⟨67782542795939966224915477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90376723727919954966553969 67782542795939966224915477)
                  ·
                    refine ⟨3177306693559685916792913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67782542795939966224915477 3177306693559685916792913)
                    ·
                      refine ⟨2382980020169764437594685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177306693559685916792913 2382980020169764437594685)
                      ·
                        rfl

theorem cell23_4640837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 6, 2].length) (baseStart_4640837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640837 prefixEnd_4640837 := by exact prefixLift 4640837
  have htrace : WordTrace (prefixWord ++ tailWord_4640837) baseStart_4640837 baseEnd_4640837 := by
    simpa [prefixWord, tailWord_4640837, baseEnd_4640837] using wordTrace_append hprefix tailTrace_4640837
  have hstable : (prefixWord ++ tailWord_4640837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640837).length < 2 ^ (prefixWord ++ tailWord_4640837).sum := by decide
  have hdescent : baseEnd_4640837 < baseStart_4640837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640857 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 3, 2, 3]
def baseStart_4640857 : Nat := 118140960795 + 4640857 * 2 ^ 59
def prefixEnd_4640857 : Nat := 4983230072969 + 3 ^ 40 * 4640857 * 2
def baseEnd_4640857 : Nat := 2382990289782854359344593

theorem tailTrace_4640857 : CollatzResearch.WordTrace tailWord_4640857 prefixEnd_4640857 2382990289782854359344593 := by
  unfold tailWord_4640857
  simp only [CollatzResearch.WordTrace]
  refine ⟨169265960547975159118976825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112843973698650106079317883 169265960547975159118976825)
  ·
    refine ⟨126949470410981369339232619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169265960547975159118976825 126949470410981369339232619)
    ·
      refine ⟨190424205616472054008848929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126949470410981369339232619 190424205616472054008848929)
      ·
        refine ⟨142818154212354040506636697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190424205616472054008848929 142818154212354040506636697)
        ·
          refine ⟨107113615659265530379977523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142818154212354040506636697 107113615659265530379977523)
          ·
            refine ⟨160670423488898295569966285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107113615659265530379977523 160670423488898295569966285)
            ·
              refine ⟨60251408808336860838737357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160670423488898295569966285 60251408808336860838737357)
              ·
                refine ⟨22594278303126322814526509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60251408808336860838737357 22594278303126322814526509)
                ·
                  refine ⟨8472854363672371055447441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22594278303126322814526509 8472854363672371055447441)
                  ·
                    refine ⟨6354640772754278291585581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8472854363672371055447441 6354640772754278291585581)
                    ·
                      refine ⟨2382990289782854359344593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6354640772754278291585581 2382990289782854359344593)
                      ·
                        rfl

theorem cell23_4640857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_4640857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640857 prefixEnd_4640857 := by exact prefixLift 4640857
  have htrace : WordTrace (prefixWord ++ tailWord_4640857) baseStart_4640857 baseEnd_4640857 := by
    simpa [prefixWord, tailWord_4640857, baseEnd_4640857] using wordTrace_append hprefix tailTrace_4640857
  have hstable : (prefixWord ++ tailWord_4640857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640857).length < 2 ^ (prefixWord ++ tailWord_4640857).sum := by decide
  have hdescent : baseEnd_4640857 < baseStart_4640857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640867 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 4]
def baseStart_4640867 : Nat := 118140960795 + 4640867 * 2 ^ 59
def prefixEnd_4640867 : Nat := 4983230072969 + 3 ^ 40 * 4640867 * 2
def baseEnd_4640867 : Nat := 2382995424589399320219547

theorem tailTrace_4640867 : CollatzResearch.WordTrace tailWord_4640867 prefixEnd_4640867 2382995424589399320219547 := by
  unfold tailWord_4640867
  simp only [CollatzResearch.WordTrace]
  refine ⟨169266325277938930826840855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112844216851959287217893903 169266325277938930826840855)
  ·
    refine ⟨253899487916908396240261283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169266325277938930826840855 253899487916908396240261283)
    ·
      refine ⟨380849231875362594360391925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253899487916908396240261283 380849231875362594360391925)
      ·
        refine ⟨35704615488315243221286743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 380849231875362594360391925 35704615488315243221286743)
        ·
          refine ⟨53556923232472864831930115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35704615488315243221286743 53556923232472864831930115)
          ·
            refine ⟨80335384848709297247895173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53556923232472864831930115 80335384848709297247895173)
            ·
              refine ⟨15062884659132993233980345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80335384848709297247895173 15062884659132993233980345)
              ·
                refine ⟨11297163494349744925485259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15062884659132993233980345 11297163494349744925485259)
                ·
                  refine ⟨16945745241524617388227889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11297163494349744925485259 16945745241524617388227889)
                  ·
                    refine ⟨12709308931143463041170917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16945745241524617388227889 12709308931143463041170917)
                    ·
                      refine ⟨2382995424589399320219547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12709308931143463041170917 2382995424589399320219547)
                      ·
                        rfl

theorem cell23_4640867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_4640867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640867 prefixEnd_4640867 := by exact prefixLift 4640867
  have htrace : WordTrace (prefixWord ++ tailWord_4640867) baseStart_4640867 baseEnd_4640867 := by
    simpa [prefixWord, tailWord_4640867, baseEnd_4640867] using wordTrace_append hprefix tailTrace_4640867
  have hstable : (prefixWord ++ tailWord_4640867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640867).length < 2 ^ (prefixWord ++ tailWord_4640867).sum := by decide
  have hdescent : baseEnd_4640867 < baseStart_4640867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640922 : List Nat := [3, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2]
def baseStart_4640922 : Nat := 118140960795 + 4640922 * 2 ^ 59
def prefixEnd_4640922 : Nat := 4983230072969 + 3 ^ 40 * 4640922 * 2
def baseEnd_4640922 : Nat := 2383023666025396605031795

theorem tailTrace_4640922 : CollatzResearch.WordTrace tailWord_4640922 prefixEnd_4640922 2383023666025396605031795 := by
  unfold tailWord_4640922
  simp only [CollatzResearch.WordTrace]
  refine ⟨42317082823184918805023255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112845554195159783480062013 42317082823184918805023255)
  ·
    refine ⟨63475624234777378207534883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42317082823184918805023255 63475624234777378207534883)
    ·
      refine ⟨95213436352166067311302325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63475624234777378207534883 95213436352166067311302325)
      ·
        refine ⟨8926259658015568810434593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95213436352166067311302325 8926259658015568810434593)
        ·
          refine ⟨6694694743511676607825945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8926259658015568810434593 6694694743511676607825945)
          ·
            refine ⟨5021021057633757455869459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6694694743511676607825945 5021021057633757455869459)
            ·
              refine ⟨7531531586450636183804189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5021021057633757455869459 7531531586450636183804189)
              ·
                refine ⟨2824324344918988568926571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7531531586450636183804189 2824324344918988568926571)
                ·
                  refine ⟨4236486517378482853389857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2824324344918988568926571 4236486517378482853389857)
                  ·
                    refine ⟨3177364888033862140042393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4236486517378482853389857 3177364888033862140042393)
                    ·
                      refine ⟨2383023666025396605031795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177364888033862140042393 2383023666025396605031795)
                      ·
                        rfl

theorem cell23_4640922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_4640922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640922 prefixEnd_4640922 := by exact prefixLift 4640922
  have htrace : WordTrace (prefixWord ++ tailWord_4640922) baseStart_4640922 baseEnd_4640922 := by
    simpa [prefixWord, tailWord_4640922, baseEnd_4640922] using wordTrace_append hprefix tailTrace_4640922
  have hstable : (prefixWord ++ tailWord_4640922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640922).length < 2 ^ (prefixWord ++ tailWord_4640922).sum := by decide
  have hdescent : baseEnd_4640922 < baseStart_4640922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640947 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 3]
def baseStart_4640947 : Nat := 118140960795 + 4640947 * 2 ^ 59
def prefixEnd_4640947 : Nat := 4983230072969 + 3 ^ 40 * 4640947 * 2
def baseEnd_4640947 : Nat := 2383036503041759007219179

theorem tailTrace_4640947 : CollatzResearch.WordTrace tailWord_4640947 prefixEnd_4640947 2383036503041759007219179 := by
  unfold tailWord_4640947
  simp only [CollatzResearch.WordTrace]
  refine ⟨169269243117649104489753095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112846162078432736326502063 169269243117649104489753095)
  ·
    refine ⟨253903864676473656734629643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169269243117649104489753095 253903864676473656734629643)
    ·
      refine ⟨380855797014710485101944465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253903864676473656734629643 380855797014710485101944465)
      ·
        refine ⟨285641847761032863826458349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380855797014710485101944465 285641847761032863826458349)
        ·
          refine ⟨107115692910387323934921881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285641847761032863826458349 107115692910387323934921881)
          ·
            refine ⟨80336769682790492951191411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107115692910387323934921881 80336769682790492951191411)
            ·
              refine ⟨120505154524185739426787117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80336769682790492951191411 120505154524185739426787117)
              ·
                refine ⟨45189432946569652285045169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120505154524185739426787117 45189432946569652285045169)
                ·
                  refine ⟨33892074709927239213783877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45189432946569652285045169 33892074709927239213783877)
                  ·
                    refine ⟨6354764008111357352584477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33892074709927239213783877 6354764008111357352584477)
                    ·
                      refine ⟨2383036503041759007219179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6354764008111357352584477 2383036503041759007219179)
                      ·
                        rfl

theorem cell23_4640947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 3].length) (baseStart_4640947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640947 prefixEnd_4640947 := by exact prefixLift 4640947
  have htrace : WordTrace (prefixWord ++ tailWord_4640947) baseStart_4640947 baseEnd_4640947 := by
    simpa [prefixWord, tailWord_4640947, baseEnd_4640947] using wordTrace_append hprefix tailTrace_4640947
  have hstable : (prefixWord ++ tailWord_4640947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640947).length < 2 ^ (prefixWord ++ tailWord_4640947).sum := by decide
  have hdescent : baseEnd_4640947 < baseStart_4640947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640957 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_4640957 : Nat := 118140960795 + 4640957 * 2 ^ 59
def prefixEnd_4640957 : Nat := 4983230072969 + 3 ^ 40 * 4640957 * 2
def baseEnd_4640957 : Nat := 2383041637848303968094133

theorem tailTrace_4640957 : CollatzResearch.WordTrace tailWord_4640957 prefixEnd_4640957 2383041637848303968094133 := by
  unfold tailWord_4640957
  simp only [CollatzResearch.WordTrace]
  refine ⟨169269607847612876197617125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112846405231741917465078083 169269607847612876197617125)
  ·
    refine ⟨31738051471427414287053211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169269607847612876197617125 31738051471427414287053211)
    ·
      refine ⟨47607077207141121430579817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31738051471427414287053211 47607077207141121430579817)
      ·
        refine ⟨35705307905355841072934863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47607077207141121430579817 35705307905355841072934863)
        ·
          refine ⟨53557961858033761609402295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35705307905355841072934863 53557961858033761609402295)
          ·
            refine ⟨80336942787050642414103443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53557961858033761609402295 80336942787050642414103443)
            ·
              refine ⟨120505414180575963621155165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80336942787050642414103443 120505414180575963621155165)
              ·
                refine ⟨45189530317715986357933187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120505414180575963621155165 45189530317715986357933187)
                ·
                  refine ⟨67784295476573979536899781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45189530317715986357933187 67784295476573979536899781)
                  ·
                    refine ⟨12709555401857621163168709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67784295476573979536899781 12709555401857621163168709)
                    ·
                      refine ⟨2383041637848303968094133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12709555401857621163168709 2383041637848303968094133)
                      ·
                        rfl

theorem cell23_4640957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_4640957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640957 prefixEnd_4640957 := by exact prefixLift 4640957
  have htrace : WordTrace (prefixWord ++ tailWord_4640957) baseStart_4640957 baseEnd_4640957 := by
    simpa [prefixWord, tailWord_4640957, baseEnd_4640957] using wordTrace_append hprefix tailTrace_4640957
  have hstable : (prefixWord ++ tailWord_4640957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640957).length < 2 ^ (prefixWord ++ tailWord_4640957).sum := by decide
  have hdescent : baseEnd_4640957 < baseStart_4640957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640964 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_4640964 : Nat := 118140960795 + 4640964 * 2 ^ 59
def prefixEnd_4640964 : Nat := 4983230072969 + 3 ^ 40 * 4640964 * 2
def baseEnd_4640964 : Nat := 2383045232212885440706601

theorem tailTrace_4640964 : CollatzResearch.WordTrace tailWord_4640964 prefixEnd_4640964 2383045232212885440706601 := by
  unfold tailWord_4640964
  simp only [CollatzResearch.WordTrace]
  refine ⟨84634931579293758196560973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112846575439058344262081297 84634931579293758196560973)
  ·
    refine ⟨31738099342235159323710365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84634931579293758196560973 31738099342235159323710365)
    ·
      refine ⟨11901787253338184746391387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31738099342235159323710365 11901787253338184746391387)
      ·
        refine ⟨17852680880007277119587081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11901787253338184746391387 17852680880007277119587081)
        ·
          refine ⟨13389510660005457839690311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17852680880007277119587081 13389510660005457839690311)
          ·
            refine ⟨20084265990008186759535467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13389510660005457839690311 20084265990008186759535467)
            ·
              refine ⟨30126398985012280139303201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20084265990008186759535467 30126398985012280139303201)
              ·
                refine ⟨22594799238759210104477401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30126398985012280139303201 22594799238759210104477401)
                ·
                  refine ⟨16946099429069407578358051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22594799238759210104477401 16946099429069407578358051)
                  ·
                    refine ⟨25419149143604111367537077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16946099429069407578358051 25419149143604111367537077)
                    ·
                      refine ⟨2383045232212885440706601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25419149143604111367537077 2383045232212885440706601)
                      ·
                        rfl

theorem cell23_4640964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_4640964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640964 prefixEnd_4640964 := by exact prefixLift 4640964
  have htrace : WordTrace (prefixWord ++ tailWord_4640964) baseStart_4640964 baseEnd_4640964 := by
    simpa [prefixWord, tailWord_4640964, baseEnd_4640964] using wordTrace_append hprefix tailTrace_4640964
  have hstable : (prefixWord ++ tailWord_4640964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640964).length < 2 ^ (prefixWord ++ tailWord_4640964).sum := by decide
  have hdescent : baseEnd_4640964 < baseStart_4640964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4640982 : List Nat := [5, 2, 1, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_4640982 : Nat := 118140960795 + 4640982 * 2 ^ 59
def prefixEnd_4640982 : Nat := 4983230072969 + 3 ^ 40 * 4640982 * 2
def baseEnd_4640982 : Nat := 2383054474864666370281519

theorem tailTrace_4640982 : CollatzResearch.WordTrace tailWord_4640982 prefixEnd_4640982 2383054474864666370281519 := by
  unfold tailWord_4640982
  simp only [CollatzResearch.WordTrace]
  refine ⟨10579407479532644091704825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112847013115014870311518133 10579407479532644091704825)
  ·
    refine ⟨7934555609649483068778619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10579407479532644091704825 7934555609649483068778619)
    ·
      refine ⟨11901833414474224603167929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7934555609649483068778619 11901833414474224603167929)
      ·
        refine ⟨8926375060855668452375947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11901833414474224603167929 8926375060855668452375947)
        ·
          refine ⟨13389562591283502678563921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8926375060855668452375947 13389562591283502678563921)
          ·
            refine ⟨10042171943462627008922941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13389562591283502678563921 10042171943462627008922941)
            ·
              refine ⟨3765814478798485128346103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10042171943462627008922941 3765814478798485128346103)
              ·
                refine ⟨5648721718197727692519155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3765814478798485128346103 5648721718197727692519155)
                ·
                  refine ⟨8473082577296591538778733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5648721718197727692519155 8473082577296591538778733)
                  ·
                    refine ⟨3177405966486221827042025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8473082577296591538778733 3177405966486221827042025)
                    ·
                      refine ⟨2383054474864666370281519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177405966486221827042025 2383054474864666370281519)
                      ·
                        rfl

theorem cell23_4640982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_4640982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4640982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4640982 prefixEnd_4640982 := by exact prefixLift 4640982
  have htrace : WordTrace (prefixWord ++ tailWord_4640982) baseStart_4640982 baseEnd_4640982 := by
    simpa [prefixWord, tailWord_4640982, baseEnd_4640982] using wordTrace_append hprefix tailTrace_4640982
  have hstable : (prefixWord ++ tailWord_4640982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4640982).length < 2 ^ (prefixWord ++ tailWord_4640982).sum := by decide
  have hdescent : baseEnd_4640982 < baseStart_4640982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4640982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641004 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 1, 7, 2]
def baseStart_4641004 : Nat := 118140960795 + 4641004 * 2 ^ 59
def prefixEnd_4641004 : Nat := 4983230072969 + 3 ^ 40 * 4641004 * 2
def baseEnd_4641004 : Nat := 2383065771439065284206417

theorem tailTrace_4641004 : CollatzResearch.WordTrace tailWord_4641004 prefixEnd_4641004 2383065771439065284206417 := by
  unfold tailWord_4641004
  simp only [CollatzResearch.WordTrace]
  refine ⟨84635661039221301612289033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112847548052295068816385377 84635661039221301612289033)
  ·
    refine ⟨63476745779415976209216775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84635661039221301612289033 63476745779415976209216775)
    ·
      refine ⟨95215118669123964313825163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63476745779415976209216775 95215118669123964313825163)
      ·
        refine ⟨142822678003685946470737745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95215118669123964313825163 142822678003685946470737745)
        ·
          refine ⟨107117008502764459853053309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142822678003685946470737745 107117008502764459853053309)
          ·
            refine ⟨40168878188536672444894991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107117008502764459853053309 40168878188536672444894991)
            ·
              refine ⟨60253317282805008667342487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40168878188536672444894991 60253317282805008667342487)
              ·
                refine ⟨90379975924207513001013731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60253317282805008667342487 90379975924207513001013731)
                ·
                  refine ⟨135569963886311269501520597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90379975924207513001013731 135569963886311269501520597)
                  ·
                    refine ⟨3177421028585420378941889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 135569963886311269501520597 3177421028585420378941889)
                    ·
                      refine ⟨2383065771439065284206417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177421028585420378941889 2383065771439065284206417)
                      ·
                        rfl

theorem cell23_4641004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 7, 2].length) (baseStart_4641004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641004 prefixEnd_4641004 := by exact prefixLift 4641004
  have htrace : WordTrace (prefixWord ++ tailWord_4641004) baseStart_4641004 baseEnd_4641004 := by
    simpa [prefixWord, tailWord_4641004, baseEnd_4641004] using wordTrace_append hprefix tailTrace_4641004
  have hstable : (prefixWord ++ tailWord_4641004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641004).length < 2 ^ (prefixWord ++ tailWord_4641004).sum := by decide
  have hdescent : baseEnd_4641004 < baseStart_4641004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641014 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_4641014 : Nat := 118140960795 + 4641014 * 2 ^ 59
def prefixEnd_4641014 : Nat := 4983230072969 + 3 ^ 40 * 4641014 * 2
def baseEnd_4641014 : Nat := 794356968748536748360457

theorem tailTrace_4641014 : CollatzResearch.WordTrace tailWord_4641014 prefixEnd_4641014 794356968748536748360457 := by
  unfold tailWord_4641014
  simp only [CollatzResearch.WordTrace]
  refine ⟨10579480425525398433277631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112847791205604249954961397 10579480425525398433277631)
  ·
    refine ⟨15869220638288097649916447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10579480425525398433277631 15869220638288097649916447)
    ·
      refine ⟨23803830957432146474874671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15869220638288097649916447 23803830957432146474874671)
      ·
        refine ⟨35705746436148219712312007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23803830957432146474874671 35705746436148219712312007)
        ·
          refine ⟨53558619654222329568468011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35705746436148219712312007 53558619654222329568468011)
          ·
            refine ⟨80337929481333494352702017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53558619654222329568468011 80337929481333494352702017)
            ·
              refine ⟨60253447111000120764526513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80337929481333494352702017 60253447111000120764526513)
              ·
                refine ⟨45190085333250090573394885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60253447111000120764526513 45190085333250090573394885)
                ·
                  refine ⟨8473140999984391982511541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45190085333250090573394885 8473140999984391982511541)
                  ·
                    refine ⟨794356968748536748360457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8473140999984391982511541 794356968748536748360457)
                    ·
                      rfl

theorem cell23_4641014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_4641014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641014 prefixEnd_4641014 := by exact prefixLift 4641014
  have htrace : WordTrace (prefixWord ++ tailWord_4641014) baseStart_4641014 baseEnd_4641014 := by
    simpa [prefixWord, tailWord_4641014, baseEnd_4641014] using wordTrace_append hprefix tailTrace_4641014
  have hstable : (prefixWord ++ tailWord_4641014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641014).length < 2 ^ (prefixWord ++ tailWord_4641014).sum := by decide
  have hdescent : baseEnd_4641014 < baseStart_4641014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641031 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 1, 7]
def baseStart_4641031 : Nat := 118140960795 + 4641031 * 2 ^ 59
def prefixEnd_4641031 : Nat := 4983230072969 + 3 ^ 40 * 4641031 * 2
def baseEnd_4641031 : Nat := 794359878472245559522931

theorem tailTrace_4641031 : CollatzResearch.WordTrace tailWord_4641031 prefixEnd_4641031 794359878472245559522931 := by
  unfold tailWord_4641031
  simp only [CollatzResearch.WordTrace]
  refine ⟨169272306849344786835810947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112848204566229857890540631 169272306849344786835810947)
  ·
    refine ⟨253908460274017180253716421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169272306849344786835810947 253908460274017180253716421)
    ·
      refine ⟨47607836301378221297571829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 253908460274017180253716421 47607836301378221297571829)
      ·
        refine ⟨4463234653254208246647359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47607836301378221297571829 4463234653254208246647359)
        ·
          refine ⟨6694851979881312369971039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4463234653254208246647359 6694851979881312369971039)
          ·
            refine ⟨10042277969821968554956559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6694851979881312369971039 10042277969821968554956559)
            ·
              refine ⟨15063416954732952832434839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10042277969821968554956559 15063416954732952832434839)
              ·
                refine ⟨22595125432099429248652259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15063416954732952832434839 22595125432099429248652259)
                ·
                  refine ⟨33892688148149143872978389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22595125432099429248652259 33892688148149143872978389)
                  ·
                    refine ⟨794359878472245559522931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33892688148149143872978389 794359878472245559522931)
                    ·
                      rfl

theorem cell23_4641031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_4641031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641031 prefixEnd_4641031 := by exact prefixLift 4641031
  have htrace : WordTrace (prefixWord ++ tailWord_4641031) baseStart_4641031 baseEnd_4641031 := by
    simpa [prefixWord, tailWord_4641031, baseEnd_4641031] using wordTrace_append hprefix tailTrace_4641031
  have hstable : (prefixWord ++ tailWord_4641031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641031).length < 2 ^ (prefixWord ++ tailWord_4641031).sum := by decide
  have hdescent : baseEnd_4641031 < baseStart_4641031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641084 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_4641084 : Nat := 118140960795 + 4641084 * 2 ^ 59
def prefixEnd_4641084 : Nat := 4983230072969 + 3 ^ 40 * 4641084 * 2
def baseEnd_4641084 : Nat := 2383106849891424971206049

theorem tailTrace_4641084 : CollatzResearch.WordTrace tailWord_4641084 prefixEnd_4641084 2383106849891424971206049 := by
  unfold tailWord_4641084
  simp only [CollatzResearch.WordTrace]
  refine ⟨84637119959076388443745153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112849493278768517924993537 84637119959076388443745153)
  ·
    refine ⟨63477839969307291332808865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84637119959076388443745153 63477839969307291332808865)
    ·
      refine ⟨47608379976980468499606649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63477839969307291332808865 47608379976980468499606649)
      ·
        refine ⟨35706284982735351374704987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47608379976980468499606649 35706284982735351374704987)
        ·
          refine ⟨53559427474103027062057481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35706284982735351374704987 53559427474103027062057481)
          ·
            refine ⟨40169570605577270296543111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53559427474103027062057481 40169570605577270296543111)
            ·
              refine ⟨60254355908365905444814667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40169570605577270296543111 60254355908365905444814667)
              ·
                refine ⟨90381533862548858167222001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60254355908365905444814667 90381533862548858167222001)
                ·
                  refine ⟨67786150396911643625416501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90381533862548858167222001 67786150396911643625416501)
                  ·
                    refine ⟨6354951599710466589882797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67786150396911643625416501 6354951599710466589882797)
                    ·
                      refine ⟨2383106849891424971206049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6354951599710466589882797 2383106849891424971206049)
                      ·
                        rfl

theorem cell23_4641084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_4641084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641084 prefixEnd_4641084 := by exact prefixLift 4641084
  have htrace : WordTrace (prefixWord ++ tailWord_4641084) baseStart_4641084 baseEnd_4641084 := by
    simpa [prefixWord, tailWord_4641084, baseEnd_4641084] using wordTrace_append hprefix tailTrace_4641084
  have hstable : (prefixWord ++ tailWord_4641084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641084).length < 2 ^ (prefixWord ++ tailWord_4641084).sum := by decide
  have hdescent : baseEnd_4641084 < baseStart_4641084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641138 : List Nat := [3, 2, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_4641138 : Nat := 118140960795 + 4641138 * 2 ^ 59
def prefixEnd_4641138 : Nat := 4983230072969 + 3 ^ 40 * 4641138 * 2
def baseEnd_4641138 : Nat := 794378192615589253310267

theorem tailTrace_4641138 : CollatzResearch.WordTrace tailWord_4641138 prefixEnd_4641138 794378192615589253310267 := by
  unfold tailWord_4641138
  simp only [CollatzResearch.WordTrace]
  refine ⟨42319052364989286027489017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112850806306638096073304045 42319052364989286027489017)
  ·
    refine ⟨31739289273741964520616763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42319052364989286027489017 31739289273741964520616763)
    ·
      refine ⟨47608933910612946780925145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31739289273741964520616763 47608933910612946780925145)
      ·
        refine ⟨35706700432959710085693859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47608933910612946780925145 35706700432959710085693859)
        ·
          refine ⟨53560050649439565128540789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35706700432959710085693859 53560050649439565128540789)
          ·
            refine ⟨5021254748384959230800699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53560050649439565128540789 5021254748384959230800699)
            ·
              refine ⟨7531882122577438846201049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5021254748384959230800699 7531882122577438846201049)
              ·
                refine ⟨5648911591933079134650787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7531882122577438846201049 5648911591933079134650787)
                ·
                  refine ⟨8473367387899618701976181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5648911591933079134650787 8473367387899618701976181)
                  ·
                    refine ⟨794378192615589253310267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8473367387899618701976181 794378192615589253310267)
                    ·
                      rfl

theorem cell23_4641138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_4641138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641138 prefixEnd_4641138 := by exact prefixLift 4641138
  have htrace : WordTrace (prefixWord ++ tailWord_4641138) baseStart_4641138 baseEnd_4641138 := by
    simpa [prefixWord, tailWord_4641138, baseEnd_4641138] using wordTrace_append hprefix tailTrace_4641138
  have hstable : (prefixWord ++ tailWord_4641138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641138).length < 2 ^ (prefixWord ++ tailWord_4641138).sum := by decide
  have hdescent : baseEnd_4641138 < baseStart_4641138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641161 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 5]
def baseStart_4641161 : Nat := 118140960795 + 4641161 * 2 ^ 59
def prefixEnd_4641161 : Nat := 4983230072969 + 3 ^ 40 * 4641161 * 2
def baseEnd_4641161 : Nat := 2383146387901821169943195

theorem tailTrace_4641161 : CollatzResearch.WordTrace tailWord_4641161 prefixEnd_4641161 2383146387901821169943195 := by
  unfold tailWord_4641161
  simp only [CollatzResearch.WordTrace]
  refine ⟨169277048338873819038043337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112851365559249212692028891 169277048338873819038043337)
  ·
    refine ⟨126957786254155364278532503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169277048338873819038043337 126957786254155364278532503)
    ·
      refine ⟨190436679381233046417798755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126957786254155364278532503 190436679381233046417798755)
      ·
        refine ⟨285655019071849569626698133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190436679381233046417798755 285655019071849569626698133)
        ·
          refine ⟨13390079018992948576251475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 285655019071849569626698133 13390079018992948576251475)
          ·
            refine ⟨20085118528489422864377213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13390079018992948576251475 20085118528489422864377213)
            ·
              refine ⟨7531919448183533574141455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20085118528489422864377213 7531919448183533574141455)
              ·
                refine ⟨11297879172275300361212183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7531919448183533574141455 11297879172275300361212183)
                ·
                  refine ⟨16946818758412950541818275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11297879172275300361212183 16946818758412950541818275)
                  ·
                    refine ⟨25420228137619425812727413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16946818758412950541818275 25420228137619425812727413)
                    ·
                      refine ⟨2383146387901821169943195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25420228137619425812727413 2383146387901821169943195)
                      ·
                        rfl

theorem cell23_4641161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 5].length) (baseStart_4641161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641161 prefixEnd_4641161 := by exact prefixLift 4641161
  have htrace : WordTrace (prefixWord ++ tailWord_4641161) baseStart_4641161 baseEnd_4641161 := by
    simpa [prefixWord, tailWord_4641161, baseEnd_4641161] using wordTrace_append hprefix tailTrace_4641161
  have hstable : (prefixWord ++ tailWord_4641161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641161).length < 2 ^ (prefixWord ++ tailWord_4641161).sum := by decide
  have hdescent : baseEnd_4641161 < baseStart_4641161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641192 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_4641192 : Nat := 118140960795 + 4641192 * 2 ^ 59
def prefixEnd_4641192 : Nat := 4983230072969 + 3 ^ 40 * 4641192 * 2
def baseEnd_4641192 : Nat := 2383162305802110548655553

theorem tailTrace_4641192 : CollatzResearch.WordTrace tailWord_4641192 prefixEnd_4641192 2383162305802110548655553 := by
  unfold tailWord_4641192
  simp only [CollatzResearch.WordTrace]
  refine ⟨84639089500880755666210915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112852119334507674221614553 84639089500880755666210915)
  ·
    refine ⟨126958634251321133499316373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84639089500880755666210915 126958634251321133499316373)
    ·
      refine ⟨5951185980530678132780455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 126958634251321133499316373 5951185980530678132780455)
      ·
        refine ⟨8926778970796017199170683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5951185980530678132780455 8926778970796017199170683)
        ·
          refine ⟨13390168456194025798756025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8926778970796017199170683 13390168456194025798756025)
          ·
            refine ⟨10042626342145519349067019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13390168456194025798756025 10042626342145519349067019)
            ·
              refine ⟨15063939513218279023600529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10042626342145519349067019 15063939513218279023600529)
              ·
                refine ⟨11297954634913709267700397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15063939513218279023600529 11297954634913709267700397)
                ·
                  refine ⟨4236732988092640975387649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11297954634913709267700397 4236732988092640975387649)
                  ·
                    refine ⟨3177549741069480731540737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4236732988092640975387649 3177549741069480731540737)
                    ·
                      refine ⟨2383162305802110548655553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177549741069480731540737 2383162305802110548655553)
                      ·
                        rfl

theorem cell23_4641192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_4641192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641192 prefixEnd_4641192 := by exact prefixLift 4641192
  have htrace : WordTrace (prefixWord ++ tailWord_4641192) baseStart_4641192 baseEnd_4641192 := by
    simpa [prefixWord, tailWord_4641192, baseEnd_4641192] using wordTrace_append hprefix tailTrace_4641192
  have hstable : (prefixWord ++ tailWord_4641192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641192).length < 2 ^ (prefixWord ++ tailWord_4641192).sum := by decide
  have hdescent : baseEnd_4641192 < baseStart_4641192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641212 : List Nat := [2, 2, 2, 4, 1, 3, 2, 1, 1, 2, 3]
def baseStart_4641212 : Nat := 118140960795 + 4641212 * 2 ^ 59
def prefixEnd_4641212 : Nat := 4983230072969 + 3 ^ 40 * 4641212 * 2
def baseEnd_4641212 : Nat := 2383172575415200470405461

theorem tailTrace_4641212 : CollatzResearch.WordTrace tailWord_4641212 prefixEnd_4641212 2383172575415200470405461 := by
  unfold tailWord_4641212
  simp only [CollatzResearch.WordTrace]
  refine ⟨84639454230844527374074945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112852605641126036498766593 84639454230844527374074945)
  ·
    refine ⟨63479590673133395530556209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84639454230844527374074945 63479590673133395530556209)
    ·
      refine ⟨47609693004850046647917157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63479590673133395530556209 47609693004850046647917157)
      ·
        refine ⟨8926817438409383746484467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47609693004850046647917157 8926817438409383746484467)
        ·
          refine ⟨13390226157614075619726701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8926817438409383746484467 13390226157614075619726701)
          ·
            refine ⟨5021334809105278357397513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13390226157614075619726701 5021334809105278357397513)
            ·
              refine ⟨3766001106828958768048135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5021334809105278357397513 3766001106828958768048135)
              ·
                refine ⟨5649001660243438152072203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766001106828958768048135 5649001660243438152072203)
                ·
                  refine ⟨8473502490365157228108305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5649001660243438152072203 8473502490365157228108305)
                  ·
                    refine ⟨6355126867773867921081229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8473502490365157228108305 6355126867773867921081229)
                    ·
                      refine ⟨2383172575415200470405461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6355126867773867921081229 2383172575415200470405461)
                      ·
                        rfl

theorem cell23_4641212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_4641212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641212 prefixEnd_4641212 := by exact prefixLift 4641212
  have htrace : WordTrace (prefixWord ++ tailWord_4641212) baseStart_4641212 baseEnd_4641212 := by
    simpa [prefixWord, tailWord_4641212, baseEnd_4641212] using wordTrace_append hprefix tailTrace_4641212
  have hstable : (prefixWord ++ tailWord_4641212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641212).length < 2 ^ (prefixWord ++ tailWord_4641212).sum := by decide
  have hdescent : baseEnd_4641212 < baseStart_4641212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641301 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 4, 5]
def baseStart_4641301 : Nat := 118140960795 + 4641301 * 2 ^ 59
def prefixEnd_4641301 : Nat := 4983230072969 + 3 ^ 40 * 4641301 * 2
def baseEnd_4641301 : Nat := 794406091731150207397517

theorem tailTrace_4641301 : CollatzResearch.WordTrace tailWord_4641301 prefixEnd_4641301 794406091731150207397517 := by
  unfold tailWord_4641301
  simp only [CollatzResearch.WordTrace]
  refine ⟨169282154558366622948139757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112854769705577748632093171 169282154558366622948139757)
  ·
    refine ⟨63480807959387483605552409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169282154558366622948139757 63480807959387483605552409)
    ·
      refine ⟨47610605969540612704164307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63480807959387483605552409 47610605969540612704164307)
      ·
        refine ⟨71415908954310919056246461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47610605969540612704164307 71415908954310919056246461)
        ·
          refine ⟨26780965857866594646092423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71415908954310919056246461 26780965857866594646092423)
          ·
            refine ⟨40171448786799891969138635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26780965857866594646092423 40171448786799891969138635)
            ·
              refine ⟨60257173180199837953707953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40171448786799891969138635 60257173180199837953707953)
              ·
                refine ⟨45192879885149878465280965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60257173180199837953707953 45192879885149878465280965)
                ·
                  refine ⟨8473664978465602212240181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45192879885149878465280965 8473664978465602212240181)
                  ·
                    refine ⟨794406091731150207397517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8473664978465602212240181 794406091731150207397517)
                    ·
                      rfl

theorem cell23_4641301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_4641301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641301 prefixEnd_4641301 := by exact prefixLift 4641301
  have htrace : WordTrace (prefixWord ++ tailWord_4641301) baseStart_4641301 baseEnd_4641301 := by
    simpa [prefixWord, tailWord_4641301, baseEnd_4641301] using wordTrace_append hprefix tailTrace_4641301
  have hstable : (prefixWord ++ tailWord_4641301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641301).length < 2 ^ (prefixWord ++ tailWord_4641301).sum := by decide
  have hdescent : baseEnd_4641301 < baseStart_4641301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641338 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_4641338 : Nat := 118140960795 + 4641338 * 2 ^ 59
def prefixEnd_4641338 : Nat := 4983230072969 + 3 ^ 40 * 4641338 * 2
def baseEnd_4641338 : Nat := 2383237273977666977429881

theorem tailTrace_4641338 : CollatzResearch.WordTrace tailWord_4641338 prefixEnd_4641338 2383237273977666977429881 := by
  unfold tailWord_4641338
  simp only [CollatzResearch.WordTrace]
  refine ⟨42320876014808144566809167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112855669372821718844824445 42320876014808144566809167)
  ·
    refine ⟨63481314022212216850213751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42320876014808144566809167 63481314022212216850213751)
    ·
      refine ⟨95221971033318325275320627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63481314022212216850213751 95221971033318325275320627)
      ·
        refine ⟨142832956549977487912980941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95221971033318325275320627 142832956549977487912980941)
        ·
          refine ⟨53562358706241557967367853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142832956549977487912980941 53562358706241557967367853)
          ·
            refine ⟨20085884514840584237762945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53562358706241557967367853 20085884514840584237762945)
            ·
              refine ⟨15064413386130438178322209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20085884514840584237762945 15064413386130438178322209)
              ·
                refine ⟨11298310039597828633741657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15064413386130438178322209 11298310039597828633741657)
                ·
                  refine ⟨8473732529698371475306243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11298310039597828633741657 8473732529698371475306243)
                  ·
                    refine ⟨12710598794547557212959365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8473732529698371475306243 12710598794547557212959365)
                    ·
                      refine ⟨2383237273977666977429881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12710598794547557212959365 2383237273977666977429881)
                      ·
                        rfl

theorem cell23_4641338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_4641338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641338 prefixEnd_4641338 := by exact prefixLift 4641338
  have htrace : WordTrace (prefixWord ++ tailWord_4641338) baseStart_4641338 baseEnd_4641338 := by
    simpa [prefixWord, tailWord_4641338, baseEnd_4641338] using wordTrace_append hprefix tailTrace_4641338
  have hstable : (prefixWord ++ tailWord_4641338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641338).length < 2 ^ (prefixWord ++ tailWord_4641338).sum := by decide
  have hdescent : baseEnd_4641338 < baseStart_4641338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641358 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_4641358 : Nat := 118140960795 + 4641358 * 2 ^ 59
def prefixEnd_4641358 : Nat := 4983230072969 + 3 ^ 40 * 4641358 * 2
def baseEnd_4641358 : Nat := 2383247543590756899179789

theorem tailTrace_4641358 : CollatzResearch.WordTrace tailWord_4641358 prefixEnd_4641358 2383247543590756899179789 := by
  unfold tailWord_4641358
  simp only [CollatzResearch.WordTrace]
  refine ⟨21160529189895015210370591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112856155679440081121976485 21160529189895015210370591)
  ·
    refine ⟨31740793784842522815555887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21160529189895015210370591 31740793784842522815555887)
    ·
      refine ⟨47611190677263784223333831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31740793784842522815555887 47611190677263784223333831)
      ·
        refine ⟨71416786015895676335000747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47611190677263784223333831 71416786015895676335000747)
        ·
          refine ⟨107125179023843514502501121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71416786015895676335000747 107125179023843514502501121)
          ·
            refine ⟨80343884267882635876875841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107125179023843514502501121 80343884267882635876875841)
            ·
              refine ⟨60257913200911976907656881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80343884267882635876875841 60257913200911976907656881)
              ·
                refine ⟨45193434900683982680742661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60257913200911976907656881 45193434900683982680742661)
                ·
                  refine ⟨8473769043878246752639249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45193434900683982680742661 8473769043878246752639249)
                  ·
                    refine ⟨6355326782908685064479437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8473769043878246752639249 6355326782908685064479437)
                    ·
                      refine ⟨2383247543590756899179789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6355326782908685064479437 2383247543590756899179789)
                      ·
                        rfl

theorem cell23_4641358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_4641358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641358 prefixEnd_4641358 := by exact prefixLift 4641358
  have htrace : WordTrace (prefixWord ++ tailWord_4641358) baseStart_4641358 baseEnd_4641358 := by
    simpa [prefixWord, tailWord_4641358, baseEnd_4641358] using wordTrace_append hprefix tailTrace_4641358
  have hstable : (prefixWord ++ tailWord_4641358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641358).length < 2 ^ (prefixWord ++ tailWord_4641358).sum := by decide
  have hdescent : baseEnd_4641358 < baseStart_4641358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641372 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_4641372 : Nat := 118140960795 + 4641372 * 2 ^ 59
def prefixEnd_4641372 : Nat := 4983230072969 + 3 ^ 40 * 4641372 * 2
def baseEnd_4641372 : Nat := 2383254732319919844404725

theorem tailTrace_4641372 : CollatzResearch.WordTrace tailWord_4641372 prefixEnd_4641372 2383254732319919844404725 := by
  unfold tailWord_4641372
  simp only [CollatzResearch.WordTrace]
  refine ⟨84642372070554701036987185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112856496094072934715982913 84642372070554701036987185)
  ·
    refine ⟨63481779052916025777740389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84642372070554701036987185 63481779052916025777740389)
    ·
      refine ⟨11902833572421754833326323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63481779052916025777740389 11902833572421754833326323)
      ·
        refine ⟨17854250358632632249989485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11902833572421754833326323 17854250358632632249989485)
        ·
          refine ⟨6695343884487237093746057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17854250358632632249989485 6695343884487237093746057)
          ·
            refine ⟨5021507913365427820309543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6695343884487237093746057 5021507913365427820309543)
            ·
              refine ⟨7532261870048141730464315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5021507913365427820309543 7532261870048141730464315)
              ·
                refine ⟨11298392805072212595696473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7532261870048141730464315 11298392805072212595696473)
                ·
                  refine ⟨8473794603804159446772355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11298392805072212595696473 8473794603804159446772355)
                  ·
                    refine ⟨12710691905706239170158533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8473794603804159446772355 12710691905706239170158533)
                    ·
                      refine ⟨2383254732319919844404725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12710691905706239170158533 2383254732319919844404725)
                      ·
                        rfl

theorem cell23_4641372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_4641372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641372 prefixEnd_4641372 := by exact prefixLift 4641372
  have htrace : WordTrace (prefixWord ++ tailWord_4641372) baseStart_4641372 baseEnd_4641372 := by
    simpa [prefixWord, tailWord_4641372, baseEnd_4641372] using wordTrace_append hprefix tailTrace_4641372
  have hstable : (prefixWord ++ tailWord_4641372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641372).length < 2 ^ (prefixWord ++ tailWord_4641372).sum := by decide
  have hdescent : baseEnd_4641372 < baseStart_4641372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641468 : List Nat := [2, 2, 2, 3, 1, 1, 4, 8]
def baseStart_4641468 : Nat := 118140960795 + 4641468 * 2 ^ 59
def prefixEnd_4641468 : Nat := 4983230072969 + 3 ^ 40 * 4641468 * 2
def baseEnd_4641468 : Nat := 88270519498620424770529

theorem tailTrace_4641468 : CollatzResearch.WordTrace tailWord_4641468 prefixEnd_4641468 88270519498620424770529 := by
  unfold tailWord_4641468
  simp only [CollatzResearch.WordTrace]
  refine ⟨84644122774380805234734529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112858830365841073646312705 84644122774380805234734529)
  ·
    refine ⟨63483092080785603926050897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84644122774380805234734529 63483092080785603926050897)
    ·
      refine ⟨47612319060589202944538173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63483092080785603926050897 47612319060589202944538173)
      ·
        refine ⟨17854619647720951104201815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47612319060589202944538173 17854619647720951104201815)
        ·
          refine ⟨26781929471581426656302723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17854619647720951104201815 26781929471581426656302723)
          ·
            refine ⟨40172894207372139984454085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26781929471581426656302723 40172894207372139984454085)
            ·
              refine ⟨7532417663882276247085141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40172894207372139984454085 7532417663882276247085141)
              ·
                refine ⟨88270519498620424770529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7532417663882276247085141 88270519498620424770529)
                ·
                  rfl

theorem cell23_4641468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 8].length) (baseStart_4641468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641468 prefixEnd_4641468 := by exact prefixLift 4641468
  have htrace : WordTrace (prefixWord ++ tailWord_4641468) baseStart_4641468 baseEnd_4641468 := by
    simpa [prefixWord, tailWord_4641468, baseEnd_4641468] using wordTrace_append hprefix tailTrace_4641468
  have hstable : (prefixWord ++ tailWord_4641468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641468).length < 2 ^ (prefixWord ++ tailWord_4641468).sum := by decide
  have hdescent : baseEnd_4641468 < baseStart_4641468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641472 : List Nat := [2, 1, 1, 2, 4, 2, 4, 1, 2, 4]
def baseStart_4641472 : Nat := 118140960795 + 4641472 * 2 ^ 59
def prefixEnd_4641472 : Nat := 4983230072969 + 3 ^ 40 * 4641472 * 2
def baseEnd_4641472 : Nat := 794435360128456484384755

theorem tailTrace_4641472 : CollatzResearch.WordTrace tailWord_4641472 prefixEnd_4641472 794435360128456484384755 := by
  unfold tailWord_4641472
  simp only [CollatzResearch.WordTrace]
  refine ⟨84644195720373559576307335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112858927627164746101743113 84644195720373559576307335)
  ·
    refine ⟨126966293580560339364461003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84644195720373559576307335 126966293580560339364461003)
    ·
      refine ⟨190449440370840509046691505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126966293580560339364461003 190449440370840509046691505)
      ·
        refine ⟨142837080278130381785018629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190449440370840509046691505 142837080278130381785018629)
        ·
          refine ⟨26781952552149446584690993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142837080278130381785018629 26781952552149446584690993)
          ·
            refine ⟨20086464414112084938518245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26781952552149446584690993 20086464414112084938518245)
            ·
              refine ⟨3766212077646015925972171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20086464414112084938518245 3766212077646015925972171)
              ·
                refine ⟨5649318116469023888958257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766212077646015925972171 5649318116469023888958257)
                ·
                  refine ⟨4236988587351767916718693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5649318116469023888958257 4236988587351767916718693)
                  ·
                    refine ⟨794435360128456484384755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4236988587351767916718693 794435360128456484384755)
                    ·
                      rfl

theorem cell23_4641472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 2, 4].length) (baseStart_4641472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641472 prefixEnd_4641472 := by exact prefixLift 4641472
  have htrace : WordTrace (prefixWord ++ tailWord_4641472) baseStart_4641472 baseEnd_4641472 := by
    simpa [prefixWord, tailWord_4641472, baseEnd_4641472] using wordTrace_append hprefix tailTrace_4641472
  have hstable : (prefixWord ++ tailWord_4641472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641472).length < 2 ^ (prefixWord ++ tailWord_4641472).sum := by decide
  have hdescent : baseEnd_4641472 < baseStart_4641472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641482 : List Nat := [3, 1, 2, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_4641482 : Nat := 118140960795 + 4641482 * 2 ^ 59
def prefixEnd_4641482 : Nat := 4983230072969 + 3 ^ 40 * 4641482 * 2
def baseEnd_4641482 : Nat := 2383311215191914414029219

theorem tailTrace_4641482 : CollatzResearch.WordTrace tailWord_4641482 prefixEnd_4641482 2383311215191914414029219 := by
  unfold tailWord_4641482
  simp only [CollatzResearch.WordTrace]
  refine ⟨42322189042677722715119675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112859170780473927240319133 42322189042677722715119675)
  ·
    refine ⟨63483283564016584072679513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42322189042677722715119675 63483283564016584072679513)
    ·
      refine ⟨47612462673012438054509635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63483283564016584072679513 47612462673012438054509635)
      ·
        refine ⟨71418694009518657081764453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47612462673012438054509635 71418694009518657081764453)
        ·
          refine ⟨13391005126784748202830835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71418694009518657081764453 13391005126784748202830835)
          ·
            refine ⟨20086507690177122304246253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13391005126784748202830835 20086507690177122304246253)
            ·
              refine ⟨7532440383816420864092345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20086507690177122304246253 7532440383816420864092345)
              ·
                refine ⟨5649330287862315648069259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7532440383816420864092345 5649330287862315648069259)
                ·
                  refine ⟨8473995431793473472103889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5649330287862315648069259 8473995431793473472103889)
                  ·
                    refine ⟨6355496573845105104077917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8473995431793473472103889 6355496573845105104077917)
                    ·
                      refine ⟨2383311215191914414029219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6355496573845105104077917 2383311215191914414029219)
                      ·
                        rfl

theorem cell23_4641482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_4641482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641482 prefixEnd_4641482 := by exact prefixLift 4641482
  have htrace : WordTrace (prefixWord ++ tailWord_4641482) baseStart_4641482 baseEnd_4641482 := by
    simpa [prefixWord, tailWord_4641482, baseEnd_4641482] using wordTrace_append hprefix tailTrace_4641482
  have hstable : (prefixWord ++ tailWord_4641482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641482).length < 2 ^ (prefixWord ++ tailWord_4641482).sum := by decide
  have hdescent : baseEnd_4641482 < baseStart_4641482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641492 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4641492 : Nat := 118140960795 + 4641492 * 2 ^ 59
def prefixEnd_4641492 : Nat := 4983230072969 + 3 ^ 40 * 4641492 * 2
def baseEnd_4641492 : Nat := 2383316349998459374904173

theorem tailTrace_4641492 : CollatzResearch.WordTrace tailWord_4641492 prefixEnd_4641492 2383316349998459374904173 := by
  unfold tailWord_4641492
  simp only [CollatzResearch.WordTrace]
  refine ⟨84644560450337331284171365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112859413933783108378895153 84644560450337331284171365)
  ·
    refine ⟨15870855084438249615782131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84644560450337331284171365 15870855084438249615782131)
    ·
      refine ⟨23806282626657374423673197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15870855084438249615782131 23806282626657374423673197)
      ·
        refine ⟨8927355984996515408877449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23806282626657374423673197 8927355984996515408877449)
        ·
          refine ⟨6695516988747386556658087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8927355984996515408877449 6695516988747386556658087)
          ·
            refine ⟨10043275483121079834987131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6695516988747386556658087 10043275483121079834987131)
            ·
              refine ⟨15064913224681619752480697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10043275483121079834987131 15064913224681619752480697)
              ·
                refine ⟨11298684918511214814360523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15064913224681619752480697 11298684918511214814360523)
                ·
                  refine ⟨16948027377766822221540785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11298684918511214814360523 16948027377766822221540785)
                  ·
                    refine ⟨12711020533325116666155589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16948027377766822221540785 12711020533325116666155589)
                    ·
                      refine ⟨2383316349998459374904173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12711020533325116666155589 2383316349998459374904173)
                      ·
                        rfl

theorem cell23_4641492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4641492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641492 prefixEnd_4641492 := by exact prefixLift 4641492
  have htrace : WordTrace (prefixWord ++ tailWord_4641492) baseStart_4641492 baseEnd_4641492 := by
    simpa [prefixWord, tailWord_4641492, baseEnd_4641492] using wordTrace_append hprefix tailTrace_4641492
  have hstable : (prefixWord ++ tailWord_4641492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641492).length < 2 ^ (prefixWord ++ tailWord_4641492).sum := by decide
  have hdescent : baseEnd_4641492 < baseStart_4641492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641495 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 3]
def baseStart_4641495 : Nat := 118140960795 + 4641495 * 2 ^ 59
def prefixEnd_4641495 : Nat := 4983230072969 + 3 ^ 40 * 4641495 * 2
def baseEnd_4641495 : Nat := 2383317890440422863166659

theorem tailTrace_4641495 : CollatzResearch.WordTrace tailWord_4641495 prefixEnd_4641495 2383317890440422863166659 := by
  unfold tailWord_4641495
  simp only [CollatzResearch.WordTrace]
  refine ⟨169289230319663794080701939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112859486879775862720467959 169289230319663794080701939)
  ·
    refine ⟨253933845479495691121052909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169289230319663794080701939 253933845479495691121052909)
    ·
      refine ⟨95225192054810884170394841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253933845479495691121052909 95225192054810884170394841)
      ·
        refine ⟨71418894041108163127796131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95225192054810884170394841 71418894041108163127796131)
        ·
          refine ⟨107128341061662244691694197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71418894041108163127796131 107128341061662244691694197)
          ·
            refine ⟨10043281974530835439846331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107128341061662244691694197 10043281974530835439846331)
            ·
              refine ⟨15064922961796253159769497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10043281974530835439846331 15064922961796253159769497)
              ·
                refine ⟨11298692221347189869827123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15064922961796253159769497 11298692221347189869827123)
                ·
                  refine ⟨16948038332020784804740685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11298692221347189869827123 16948038332020784804740685)
                  ·
                    refine ⟨6355514374507794301777757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16948038332020784804740685 6355514374507794301777757)
                    ·
                      refine ⟨2383317890440422863166659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6355514374507794301777757 2383317890440422863166659)
                      ·
                        rfl

theorem cell23_4641495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_4641495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641495 prefixEnd_4641495 := by exact prefixLift 4641495
  have htrace : WordTrace (prefixWord ++ tailWord_4641495) baseStart_4641495 baseEnd_4641495 := by
    simpa [prefixWord, tailWord_4641495, baseEnd_4641495] using wordTrace_append hprefix tailTrace_4641495
  have hstable : (prefixWord ++ tailWord_4641495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641495).length < 2 ^ (prefixWord ++ tailWord_4641495).sum := by decide
  have hdescent : baseEnd_4641495 < baseStart_4641495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641522 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 3, 3, 2]
def baseStart_4641522 : Nat := 118140960795 + 4641522 * 2 ^ 59
def prefixEnd_4641522 : Nat := 4983230072969 + 3 ^ 40 * 4641522 * 2
def baseEnd_4641522 : Nat := 2383331754418094257529035

theorem tailTrace_4641522 : CollatzResearch.WordTrace tailWord_4641522 prefixEnd_4641522 2383331754418094257529035 := by
  unfold tailWord_4641522
  simp only [CollatzResearch.WordTrace]
  refine ⟨42322553772641494422983705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112860143393710651794623213 42322553772641494422983705)
  ·
    refine ⟨31741915329481120817237779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42322553772641494422983705 31741915329481120817237779)
    ·
      refine ⟨47612872994221681225856669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31741915329481120817237779 47612872994221681225856669)
      ·
        refine ⟨17854827372833130459696251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47612872994221681225856669 17854827372833130459696251)
        ·
          refine ⟨26782241059249695689544377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17854827372833130459696251 26782241059249695689544377)
          ·
            refine ⟨20086680794437271767158283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26782241059249695689544377 20086680794437271767158283)
            ·
              refine ⟨30130021191655907650737425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20086680794437271767158283 30130021191655907650737425)
              ·
                refine ⟨22597515893741930738053069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30130021191655907650737425 22597515893741930738053069)
                ·
                  refine ⟨8474068460153224026769901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22597515893741930738053069 8474068460153224026769901)
                  ·
                    refine ⟨3177775672557459010038713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8474068460153224026769901 3177775672557459010038713)
                    ·
                      refine ⟨2383331754418094257529035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177775672557459010038713 2383331754418094257529035)
                      ·
                        rfl

theorem cell23_4641522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_4641522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641522 prefixEnd_4641522 := by exact prefixLift 4641522
  have htrace : WordTrace (prefixWord ++ tailWord_4641522) baseStart_4641522 baseEnd_4641522 := by
    simpa [prefixWord, tailWord_4641522, baseEnd_4641522] using wordTrace_append hprefix tailTrace_4641522
  have hstable : (prefixWord ++ tailWord_4641522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641522).length < 2 ^ (prefixWord ++ tailWord_4641522).sum := by decide
  have hdescent : baseEnd_4641522 < baseStart_4641522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641528 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 2, 6]
def baseStart_4641528 : Nat := 118140960795 + 4641528 * 2 ^ 59
def prefixEnd_4641528 : Nat := 4983230072969 + 3 ^ 40 * 4641528 * 2
def baseEnd_4641528 : Nat := 794444945100673744684669

theorem tailTrace_4641528 : CollatzResearch.WordTrace tailWord_4641528 prefixEnd_4641528 794444945100673744684669 := by
  unfold tailWord_4641528
  simp only [CollatzResearch.WordTrace]
  refine ⟨84645216964272120358326619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112860289285696160477768825 84645216964272120358326619)
  ·
    refine ⟨126967825446408180537489929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84645216964272120358326619 126967825446408180537489929)
    ·
      refine ⟨95225869084806135403117447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126967825446408180537489929 95225869084806135403117447)
      ·
        refine ⟨142838803627209203104676171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95225869084806135403117447 142838803627209203104676171)
        ·
          refine ⟨214258205440813804657014257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142838803627209203104676171 214258205440813804657014257)
          ·
            refine ⟨160693654080610353492760693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214258205440813804657014257 160693654080610353492760693)
            ·
              refine ⟨15065030070057220639946315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 160693654080610353492760693 15065030070057220639946315)
              ·
                refine ⟨22597545105085830959919473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15065030070057220639946315 22597545105085830959919473)
                ·
                  refine ⟨16948158828814373219939605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22597545105085830959919473 16948158828814373219939605)
                  ·
                    refine ⟨794444945100673744684669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16948158828814373219939605 794444945100673744684669)
                    ·
                      rfl

theorem cell23_4641528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_4641528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641528 prefixEnd_4641528 := by exact prefixLift 4641528
  have htrace : WordTrace (prefixWord ++ tailWord_4641528) baseStart_4641528 baseEnd_4641528 := by
    simpa [prefixWord, tailWord_4641528, baseEnd_4641528] using wordTrace_append hprefix tailTrace_4641528
  have hstable : (prefixWord ++ tailWord_4641528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641528).length < 2 ^ (prefixWord ++ tailWord_4641528).sum := by decide
  have hdescent : baseEnd_4641528 < baseStart_4641528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641548 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_4641548 : Nat := 118140960795 + 4641548 * 2 ^ 59
def prefixEnd_4641548 : Nat := 4983230072969 + 3 ^ 40 * 4641548 * 2
def baseEnd_4641548 : Nat := 2383345104915111155803915

theorem tailTrace_4641548 : CollatzResearch.WordTrace tailWord_4641548 prefixEnd_4641548 2383345104915111155803915 := by
  unfold tailWord_4641548
  simp only [CollatzResearch.WordTrace]
  refine ⟨84645581694235892066190649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112860775592314522754920865 84645581694235892066190649)
  ·
    refine ⟨63484186270676919049642987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84645581694235892066190649 63484186270676919049642987)
    ·
      refine ⟨95226279406015378574464481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63484186270676919049642987 95226279406015378574464481)
      ·
        refine ⟨71419709554511533930848361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95226279406015378574464481 71419709554511533930848361)
        ·
          refine ⟨53564782165883650448136271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71419709554511533930848361 53564782165883650448136271)
          ·
            refine ⟨80347173248825475672204407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53564782165883650448136271 80347173248825475672204407)
            ·
              refine ⟨120520759873238213508306611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80347173248825475672204407 120520759873238213508306611)
              ·
                refine ⟨180781139809857320262459917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120520759873238213508306611 180781139809857320262459917)
                ·
                  refine ⟨67792927428696495098422469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180781139809857320262459917 67792927428696495098422469)
                  ·
                    refine ⟨12711173892880592830954213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67792927428696495098422469 12711173892880592830954213)
                    ·
                      refine ⟨2383345104915111155803915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12711173892880592830954213 2383345104915111155803915)
                      ·
                        rfl

theorem cell23_4641548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_4641548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641548 prefixEnd_4641548 := by exact prefixLift 4641548
  have htrace : WordTrace (prefixWord ++ tailWord_4641548) baseStart_4641548 baseEnd_4641548 := by
    simpa [prefixWord, tailWord_4641548, baseEnd_4641548] using wordTrace_append hprefix tailTrace_4641548
  have hstable : (prefixWord ++ tailWord_4641548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641548).length < 2 ^ (prefixWord ++ tailWord_4641548).sum := by decide
  have hdescent : baseEnd_4641548 < baseStart_4641548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641582 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4641582 : Nat := 118140960795 + 4641582 * 2 ^ 59
def prefixEnd_4641582 : Nat := 4983230072969 + 3 ^ 40 * 4641582 * 2
def baseEnd_4641582 : Nat := 2383362563257364022778759

theorem tailTrace_4641582 : CollatzResearch.WordTrace tailWord_4641582 prefixEnd_4641582 2383362563257364022778759 := by
  unfold tailWord_4641582
  simp only [CollatzResearch.WordTrace]
  refine ⟨21161550433793575992389875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112861602313565738626079333 21161550433793575992389875)
  ·
    refine ⟨31742325650690363988584813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21161550433793575992389875 31742325650690363988584813)
    ·
      refine ⟨11903372119008886495719305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31742325650690363988584813 11903372119008886495719305)
      ·
        refine ⟨8927529089256664871789479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11903372119008886495719305 8927529089256664871789479)
        ·
          refine ⟨13391293633884997307684219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8927529089256664871789479 13391293633884997307684219)
          ·
            refine ⟨20086940450827495961526329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13391293633884997307684219 20086940450827495961526329)
            ·
              refine ⟨15065205338120621971144747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20086940450827495961526329 15065205338120621971144747)
              ·
                refine ⟨22597808007180932956717121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15065205338120621971144747 22597808007180932956717121)
                ·
                  refine ⟨16948356005385699717537841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22597808007180932956717121 16948356005385699717537841)
                  ·
                    refine ⟨12711267004039274788153381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16948356005385699717537841 12711267004039274788153381)
                    ·
                      refine ⟨2383362563257364022778759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12711267004039274788153381 2383362563257364022778759)
                      ·
                        rfl

theorem cell23_4641582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4641582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641582 prefixEnd_4641582 := by exact prefixLift 4641582
  have htrace : WordTrace (prefixWord ++ tailWord_4641582) baseStart_4641582 baseEnd_4641582 := by
    simpa [prefixWord, tailWord_4641582, baseEnd_4641582] using wordTrace_append hprefix tailTrace_4641582
  have hstable : (prefixWord ++ tailWord_4641582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641582).length < 2 ^ (prefixWord ++ tailWord_4641582).sum := by decide
  have hdescent : baseEnd_4641582 < baseStart_4641582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641585 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 2, 3, 3]
def baseStart_4641585 : Nat := 118140960795 + 4641585 * 2 ^ 59
def prefixEnd_4641585 : Nat := 4983230072969 + 3 ^ 40 * 4641585 * 2
def baseEnd_4641585 : Nat := 2383364103699327511041245

theorem tailTrace_4641585 : CollatzResearch.WordTrace tailWord_4641585 prefixEnd_4641585 2383364103699327511041245 := by
  unfold tailWord_4641585
  simp only [CollatzResearch.WordTrace]
  refine ⟨169292512889337739451478209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112861675259558492967652139 169292512889337739451478209)
  ·
    refine ⟨126969384667003304588608657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169292512889337739451478209 126969384667003304588608657)
    ·
      refine ⟨95227038500252478441456493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126969384667003304588608657 95227038500252478441456493)
      ·
        refine ⟨35710139437594679415546185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95227038500252478441456493 35710139437594679415546185)
        ·
          refine ⟨26782604578196009561659639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35710139437594679415546185 26782604578196009561659639)
          ·
            refine ⟨40173906867294014342489459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26782604578196009561659639 40173906867294014342489459)
            ·
              refine ⟨60260860300941021513734189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40173906867294014342489459 60260860300941021513734189)
              ·
                refine ⟨22597822612852883067650321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60260860300941021513734189 22597822612852883067650321)
                ·
                  refine ⟨16948366959639662300737741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22597822612852883067650321 16948366959639662300737741)
                  ·
                    refine ⟨6355637609864873362776653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16948366959639662300737741 6355637609864873362776653)
                    ·
                      refine ⟨2383364103699327511041245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6355637609864873362776653 2383364103699327511041245)
                      ·
                        rfl

theorem cell23_4641585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_4641585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641585 prefixEnd_4641585 := by exact prefixLift 4641585
  have htrace : WordTrace (prefixWord ++ tailWord_4641585) baseStart_4641585 baseEnd_4641585 := by
    simpa [prefixWord, tailWord_4641585, baseEnd_4641585] using wordTrace_append hprefix tailTrace_4641585
  have hstable : (prefixWord ++ tailWord_4641585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641585).length < 2 ^ (prefixWord ++ tailWord_4641585).sum := by decide
  have hdescent : baseEnd_4641585 < baseStart_4641585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641586 : List Nat := [3, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2]
def baseStart_4641586 : Nat := 118140960795 + 4641586 * 2 ^ 59
def prefixEnd_4641586 : Nat := 4983230072969 + 3 ^ 40 * 4641586 * 2
def baseEnd_4641586 : Nat := 2383364617179982007128741

theorem tailTrace_4641586 : CollatzResearch.WordTrace tailWord_4641586 prefixEnd_4641586 2383364617179982007128741 := by
  unfold tailWord_4641586
  simp only [CollatzResearch.WordTrace]
  refine ⟨42323137340583529155566153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112861699574889411081509741 42323137340583529155566153)
  ·
    refine ⟨31742353005437646866674615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42323137340583529155566153 31742353005437646866674615)
    ·
      refine ⟨47613529508156470300011923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31742353005437646866674615 47613529508156470300011923)
      ·
        refine ⟨71420294262234705450017885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47613529508156470300011923 71420294262234705450017885)
        ·
          refine ⟨26782610348338014543756707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71420294262234705450017885 26782610348338014543756707)
          ·
            refine ⟨40173915522507021815635061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26782610348338014543756707 40173915522507021815635061)
            ·
              refine ⟨3766304580235033295215787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40173915522507021815635061 3766304580235033295215787)
              ·
                refine ⟨5649456870352549942823681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766304580235033295215787 5649456870352549942823681)
                ·
                  refine ⟨4237092652764412457117761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5649456870352549942823681 4237092652764412457117761)
                  ·
                    refine ⟨3177819489573309342838321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4237092652764412457117761 3177819489573309342838321)
                    ·
                      refine ⟨2383364617179982007128741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177819489573309342838321 2383364617179982007128741)
                      ·
                        rfl

theorem cell23_4641586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_4641586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641586 prefixEnd_4641586 := by exact prefixLift 4641586
  have htrace : WordTrace (prefixWord ++ tailWord_4641586) baseStart_4641586 baseEnd_4641586 := by
    simpa [prefixWord, tailWord_4641586, baseEnd_4641586] using wordTrace_append hprefix tailTrace_4641586
  have hstable : (prefixWord ++ tailWord_4641586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641586).length < 2 ^ (prefixWord ++ tailWord_4641586).sum := by decide
  have hdescent : baseEnd_4641586 < baseStart_4641586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641625 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 4, 1, 4]
def baseStart_4641625 : Nat := 118140960795 + 4641625 * 2 ^ 59
def prefixEnd_4641625 : Nat := 4983230072969 + 3 ^ 40 * 4641625 * 2
def baseEnd_4641625 : Nat := 2383384642925507354541061

theorem tailTrace_4641625 : CollatzResearch.WordTrace tailWord_4641625 prefixEnd_4641625 2383384642925507354541061 := by
  unfold tailWord_4641625
  simp only [CollatzResearch.WordTrace]
  refine ⟨169293971809192826282934329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112862647872795217521956219 169293971809192826282934329)
  ·
    refine ⟨126970478856894619712200747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169293971809192826282934329 126970478856894619712200747)
    ·
      refine ⟨190455718285341929568301121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126970478856894619712200747 190455718285341929568301121)
      ·
        refine ⟨142841788714006447176225841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190455718285341929568301121 142841788714006447176225841)
        ·
          refine ⟨107131341535504835382169381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142841788714006447176225841 107131341535504835382169381)
          ·
            refine ⟨20087126537907156634156759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107131341535504835382169381 20087126537907156634156759)
            ·
              refine ⟨30130689806860734951235139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20087126537907156634156759 30130689806860734951235139)
              ·
                refine ⟨45196034710291102426852709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30130689806860734951235139 45196034710291102426852709)
                ·
                  refine ⟨8474256508179581705034883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45196034710291102426852709 8474256508179581705034883)
                  ·
                    refine ⟨12711384762269372557552325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8474256508179581705034883 12711384762269372557552325)
                    ·
                      refine ⟨2383384642925507354541061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12711384762269372557552325 2383384642925507354541061)
                      ·
                        rfl

theorem cell23_4641625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_4641625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641625 prefixEnd_4641625 := by exact prefixLift 4641625
  have htrace : WordTrace (prefixWord ++ tailWord_4641625) baseStart_4641625 baseEnd_4641625 := by
    simpa [prefixWord, tailWord_4641625, baseEnd_4641625] using wordTrace_append hprefix tailTrace_4641625
  have hstable : (prefixWord ++ tailWord_4641625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641625).length < 2 ^ (prefixWord ++ tailWord_4641625).sum := by decide
  have hdescent : baseEnd_4641625 < baseStart_4641625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641719 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 2, 3, 2]
def baseStart_4641719 : Nat := 118140960795 + 4641719 * 2 ^ 59
def prefixEnd_4641719 : Nat := 4983230072969 + 3 ^ 40 * 4641719 * 2
def baseEnd_4641719 : Nat := 2383432910107029986765629

theorem tailTrace_4641719 : CollatzResearch.WordTrace tailWord_4641719 prefixEnd_4641719 2383432910107029986765629 := by
  unfold tailWord_4641719
  simp only [CollatzResearch.WordTrace]
  refine ⟨169297400270852280336856211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112864933513901520224570807 169297400270852280336856211)
  ·
    refine ⟨253946100406278420505284317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169297400270852280336856211 253946100406278420505284317)
    ·
      refine ⟨95229787652354407689481619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253946100406278420505284317 95229787652354407689481619)
      ·
        refine ⟨142844681478531611534222429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95229787652354407689481619 142844681478531611534222429)
        ·
          refine ⟨53566755554449354325333411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142844681478531611534222429 53566755554449354325333411)
          ·
            refine ⟨80350133331674031488000117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53566755554449354325333411 80350133331674031488000117)
            ·
              refine ⟨7532824999844440452000011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80350133331674031488000117 7532824999844440452000011)
              ·
                refine ⟨11299237499766660678000017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7532824999844440452000011 11299237499766660678000017)
                ·
                  refine ⟨8474428124824995508500013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11299237499766660678000017 8474428124824995508500013)
                  ·
                    refine ⟨3177910546809373315687505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8474428124824995508500013 3177910546809373315687505)
                    ·
                      refine ⟨2383432910107029986765629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177910546809373315687505 2383432910107029986765629)
                      ·
                        rfl

theorem cell23_4641719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 3, 2].length) (baseStart_4641719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641719 prefixEnd_4641719 := by exact prefixLift 4641719
  have htrace : WordTrace (prefixWord ++ tailWord_4641719) baseStart_4641719 baseEnd_4641719 := by
    simpa [prefixWord, tailWord_4641719, baseEnd_4641719] using wordTrace_append hprefix tailTrace_4641719
  have hstable : (prefixWord ++ tailWord_4641719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641719).length < 2 ^ (prefixWord ++ tailWord_4641719).sum := by decide
  have hdescent : baseEnd_4641719 < baseStart_4641719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641745 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_4641745 : Nat := 118140960795 + 4641745 * 2 ^ 59
def prefixEnd_4641745 : Nat := 4983230072969 + 3 ^ 40 * 4641745 * 2
def baseEnd_4641745 : Nat := 2383446260604046885040509

theorem tailTrace_4641745 : CollatzResearch.WordTrace tailWord_4641745 prefixEnd_4641745 2383446260604046885040509 := by
  unfold tailWord_4641745
  simp only [CollatzResearch.WordTrace]
  refine ⟨169298348568758086777302689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112865565712505391184868459 169298348568758086777302689)
  ·
    refine ⟨126973761426568565082977017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169298348568758086777302689 126973761426568565082977017)
    ·
      refine ⟨95230321069926423812232763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126973761426568565082977017 95230321069926423812232763)
      ·
        refine ⟨142845481604889635718349145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95230321069926423812232763 142845481604889635718349145)
        ·
          refine ⟨107134111203667226788761859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142845481604889635718349145 107134111203667226788761859)
          ·
            refine ⟨160701166805500840183142789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107134111203667226788761859 160701166805500840183142789)
            ·
              refine ⟨30131468776031407534339273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160701166805500840183142789 30131468776031407534339273)
              ·
                refine ⟨22598601582023555650754455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30131468776031407534339273 22598601582023555650754455)
                ·
                  refine ⟨33897902373035333476131683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22598601582023555650754455 33897902373035333476131683)
                  ·
                    refine ⟨50846853559553000214197525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33897902373035333476131683 50846853559553000214197525)
                    ·
                      refine ⟨2383446260604046885040509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50846853559553000214197525 2383446260604046885040509)
                      ·
                        rfl

theorem cell23_4641745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_4641745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641745 prefixEnd_4641745 := by exact prefixLift 4641745
  have htrace : WordTrace (prefixWord ++ tailWord_4641745) baseStart_4641745 baseEnd_4641745 := by
    simpa [prefixWord, tailWord_4641745, baseEnd_4641745] using wordTrace_append hprefix tailTrace_4641745
  have hstable : (prefixWord ++ tailWord_4641745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641745).length < 2 ^ (prefixWord ++ tailWord_4641745).sum := by decide
  have hdescent : baseEnd_4641745 < baseStart_4641745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641752 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_4641752 : Nat := 118140960795 + 4641752 * 2 ^ 59
def prefixEnd_4641752 : Nat := 4983230072969 + 3 ^ 40 * 4641752 * 2
def baseEnd_4641752 : Nat := 2383449854968628357652977

theorem tailTrace_4641752 : CollatzResearch.WordTrace tailWord_4641752 prefixEnd_4641752 2383449854968628357652977 := by
  unfold tailWord_4641752
  simp only [CollatzResearch.WordTrace]
  refine ⟨84649301939866363486403755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112865735919821817981871673 84649301939866363486403755)
  ·
    refine ⟨126973952909799545229605633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84649301939866363486403755 126973952909799545229605633)
    ·
      refine ⟨95230464682349658922204225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126973952909799545229605633 95230464682349658922204225)
      ·
        refine ⟨71422848511762244191653169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95230464682349658922204225 71422848511762244191653169)
        ·
          refine ⟨53567136383821683143739877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71422848511762244191653169 53567136383821683143739877)
          ·
            refine ⟨10043838071966565589451227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53567136383821683143739877 10043838071966565589451227)
            ·
              refine ⟨15065757107949848384176841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10043838071966565589451227 15065757107949848384176841)
              ·
                refine ⟨11299317830962386288132631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15065757107949848384176841 11299317830962386288132631)
                ·
                  refine ⟨16948976746443579432198947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11299317830962386288132631 16948976746443579432198947)
                  ·
                    refine ⟨25423465119665369148298421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16948976746443579432198947 25423465119665369148298421)
                    ·
                      refine ⟨2383449854968628357652977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25423465119665369148298421 2383449854968628357652977)
                      ·
                        rfl

theorem cell23_4641752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_4641752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641752 prefixEnd_4641752 := by exact prefixLift 4641752
  have htrace : WordTrace (prefixWord ++ tailWord_4641752) baseStart_4641752 baseEnd_4641752 := by
    simpa [prefixWord, tailWord_4641752, baseEnd_4641752] using wordTrace_append hprefix tailTrace_4641752
  have hstable : (prefixWord ++ tailWord_4641752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641752).length < 2 ^ (prefixWord ++ tailWord_4641752).sum := by decide
  have hdescent : baseEnd_4641752 < baseStart_4641752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641759 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 1, 6]
def baseStart_4641759 : Nat := 118140960795 + 4641759 * 2 ^ 59
def prefixEnd_4641759 : Nat := 4983230072969 + 3 ^ 40 * 4641759 * 2
def baseEnd_4641759 : Nat := 794484483111069943421815

theorem tailTrace_4641759 : CollatzResearch.WordTrace tailWord_4641759 prefixEnd_4641759 794484483111069943421815 := by
  unfold tailWord_4641759
  simp only [CollatzResearch.WordTrace]
  refine ⟨169298859190707367168312331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112865906127138244778874887 169298859190707367168312331)
  ·
    refine ⟨253948288786061050752468497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169298859190707367168312331 253948288786061050752468497)
    ·
      refine ⟨190461216589545788064351373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253948288786061050752468497 190461216589545788064351373)
      ·
        refine ⟨71422956221079670524131765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190461216589545788064351373 71422956221079670524131765)
        ·
          refine ⟨6695902145726219111637353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71422956221079670524131765 6695902145726219111637353)
          ·
            refine ⟨5021926609294664333728015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6695902145726219111637353 5021926609294664333728015)
            ·
              refine ⟨7532889913941996500592023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5021926609294664333728015 7532889913941996500592023)
              ·
                refine ⟨11299334870912994750888035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7532889913941996500592023 11299334870912994750888035)
                ·
                  refine ⟨16949002306369492126332053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11299334870912994750888035 16949002306369492126332053)
                  ·
                    refine ⟨794484483111069943421815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16949002306369492126332053 794484483111069943421815)
                    ·
                      rfl

theorem cell23_4641759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 6].length) (baseStart_4641759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641759 prefixEnd_4641759 := by exact prefixLift 4641759
  have htrace : WordTrace (prefixWord ++ tailWord_4641759) baseStart_4641759 baseEnd_4641759 := by
    simpa [prefixWord, tailWord_4641759, baseEnd_4641759] using wordTrace_append hprefix tailTrace_4641759
  have hstable : (prefixWord ++ tailWord_4641759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641759).length < 2 ^ (prefixWord ++ tailWord_4641759).sum := by decide
  have hdescent : baseEnd_4641759 < baseStart_4641759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641792 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 1, 9, 2]
def baseStart_4641792 : Nat := 118140960795 + 4641792 * 2 ^ 59
def prefixEnd_4641792 : Nat := 4983230072969 + 3 ^ 40 * 4641792 * 2
def baseEnd_4641792 : Nat := 2383470394194808201152793

theorem tailTrace_4641792 : CollatzResearch.WordTrace tailWord_4641792 prefixEnd_4641792 2383470394194808201152793 := by
  unfold tailWord_4641792
  simp only [CollatzResearch.WordTrace]
  refine ⟨84650031399793906902131815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112866708533058542536175753 84650031399793906902131815)
  ·
    refine ⟨126975047099690860353197723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84650031399793906902131815 126975047099690860353197723)
    ·
      refine ⟨190462570649536290529796585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126975047099690860353197723 190462570649536290529796585)
      ·
        refine ⟨142846927987152217897347439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190462570649536290529796585 142846927987152217897347439)
        ·
          refine ⟨214270391980728326846021159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142846927987152217897347439 214270391980728326846021159)
          ·
            refine ⟨321405587971092490269031739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214270391980728326846021159 321405587971092490269031739)
            ·
              refine ⟨482108381956638735403547609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321405587971092490269031739 482108381956638735403547609)
              ·
                refine ⟨361581286467479051552660707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482108381956638735403547609 361581286467479051552660707)
                ·
                  refine ⟨542371929701218577328991061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 361581286467479051552660707 542371929701218577328991061)
                  ·
                    refine ⟨3177960525593077601537057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 542371929701218577328991061 3177960525593077601537057)
                    ·
                      refine ⟨2383470394194808201152793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177960525593077601537057 2383470394194808201152793)
                      ·
                        rfl

theorem cell23_4641792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 9, 2].length) (baseStart_4641792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641792 prefixEnd_4641792 := by exact prefixLift 4641792
  have htrace : WordTrace (prefixWord ++ tailWord_4641792) baseStart_4641792 baseEnd_4641792 := by
    simpa [prefixWord, tailWord_4641792, baseEnd_4641792] using wordTrace_append hprefix tailTrace_4641792
  have hstable : (prefixWord ++ tailWord_4641792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641792).length < 2 ^ (prefixWord ++ tailWord_4641792).sum := by decide
  have hdescent : baseEnd_4641792 < baseStart_4641792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641799 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_4641799 : Nat := 118140960795 + 4641799 * 2 ^ 59
def prefixEnd_4641799 : Nat := 4983230072969 + 3 ^ 40 * 4641799 * 2
def baseEnd_4641799 : Nat := 2383473988559389673765261

theorem tailTrace_4641799 : CollatzResearch.WordTrace tailWord_4641799 prefixEnd_4641799 2383473988559389673765261 := by
  unfold tailWord_4641799
  simp only [CollatzResearch.WordTrace]
  refine ⟨169300318110562453999768451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112866878740374969333178967 169300318110562453999768451)
  ·
    refine ⟨253950477165843680999652677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169300318110562453999768451 253950477165843680999652677)
    ·
      refine ⟨47615714468595690187434877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 253950477165843680999652677 47615714468595690187434877)
      ·
        refine ⟨17855892925723383820288079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47615714468595690187434877 17855892925723383820288079)
        ·
          refine ⟨26783839388585075730432119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17855892925723383820288079 26783839388585075730432119)
          ·
            refine ⟨40175759082877613595648179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26783839388585075730432119 40175759082877613595648179)
            ·
              refine ⟨60263638624316420393472269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40175759082877613595648179 60263638624316420393472269)
              ·
                refine ⟨22598864484118657647552101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60263638624316420393472269 22598864484118657647552101)
                ·
                  refine ⟨4237287090772248308916019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22598864484118657647552101 4237287090772248308916019)
                  ·
                    refine ⟨6355930636158372463374029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4237287090772248308916019 6355930636158372463374029)
                    ·
                      refine ⟨2383473988559389673765261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6355930636158372463374029 2383473988559389673765261)
                      ·
                        rfl

theorem cell23_4641799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_4641799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641799 prefixEnd_4641799 := by exact prefixLift 4641799
  have htrace : WordTrace (prefixWord ++ tailWord_4641799) baseStart_4641799 baseEnd_4641799 := by
    simpa [prefixWord, tailWord_4641799, baseEnd_4641799] using wordTrace_append hprefix tailTrace_4641799
  have hstable : (prefixWord ++ tailWord_4641799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641799).length < 2 ^ (prefixWord ++ tailWord_4641799).sum := by decide
  have hdescent : baseEnd_4641799 < baseStart_4641799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641800 : List Nat := [2, 1, 3, 2, 1, 4, 3, 2, 1, 2, 2]
def baseStart_4641800 : Nat := 118140960795 + 4641800 * 2 ^ 59
def prefixEnd_4641800 : Nat := 4983230072969 + 3 ^ 40 * 4641800 * 2
def baseEnd_4641800 : Nat := 2383474502040044169852757

theorem tailTrace_4641800 : CollatzResearch.WordTrace tailWord_4641800 prefixEnd_4641800 2383474502040044169852757 := by
  unfold tailWord_4641800
  simp only [CollatzResearch.WordTrace]
  refine ⟨84650177291779415585277427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112866903055705887447036569 84650177291779415585277427)
  ·
    refine ⟨126975265937669123377916141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84650177291779415585277427 126975265937669123377916141)
    ·
      refine ⟨47615724726625921266718553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126975265937669123377916141 47615724726625921266718553)
      ·
        refine ⟨35711793544969440950038915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47615724726625921266718553 35711793544969440950038915)
        ·
          refine ⟨53567690317454161425058373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35711793544969440950038915 53567690317454161425058373)
          ·
            refine ⟨10043941934522655267198445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53567690317454161425058373 10043941934522655267198445)
            ·
              refine ⟨3766478225445995725199417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10043941934522655267198445 3766478225445995725199417)
              ·
                refine ⟨2824858669084496793899563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3766478225445995725199417 2824858669084496793899563)
                ·
                  refine ⟨4237288003626745190849345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2824858669084496793899563 4237288003626745190849345)
                  ·
                    refine ⟨3177966002720058893137009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4237288003626745190849345 3177966002720058893137009)
                    ·
                      refine ⟨2383474502040044169852757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177966002720058893137009 2383474502040044169852757)
                      ·
                        rfl

theorem cell23_4641800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_4641800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641800 prefixEnd_4641800 := by exact prefixLift 4641800
  have htrace : WordTrace (prefixWord ++ tailWord_4641800) baseStart_4641800 baseEnd_4641800 := by
    simpa [prefixWord, tailWord_4641800, baseEnd_4641800] using wordTrace_append hprefix tailTrace_4641800
  have hstable : (prefixWord ++ tailWord_4641800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641800).length < 2 ^ (prefixWord ++ tailWord_4641800).sum := by decide
  have hdescent : baseEnd_4641800 < baseStart_4641800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641810 : List Nat := [3, 2, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4641810 : Nat := 118140960795 + 4641810 * 2 ^ 59
def prefixEnd_4641810 : Nat := 4983230072969 + 3 ^ 40 * 4641810 * 2
def baseEnd_4641810 : Nat := 794493212282196376909237

theorem tailTrace_4641810 : CollatzResearch.WordTrace tailWord_4641810 prefixEnd_4641810 794493212282196376909237 := by
  unfold tailWord_4641810
  simp only [CollatzResearch.WordTrace]
  refine ⟨42325179828380650719604721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112867146209015068585612589 42325179828380650719604721)
  ·
    refine ⟨31743884871285488039703541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42325179828380650719604721 31743884871285488039703541)
    ·
      refine ⟨2975989206683014503722207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31743884871285488039703541 2975989206683014503722207)
      ·
        refine ⟨4463983810024521755583311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2975989206683014503722207 4463983810024521755583311)
        ·
          refine ⟨6695975715036782633374967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4463983810024521755583311 6695975715036782633374967)
          ·
            refine ⟨10043963572555173950062451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6695975715036782633374967 10043963572555173950062451)
            ·
              refine ⟨15065945358832760925093677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10043963572555173950062451 15065945358832760925093677)
              ·
                refine ⟨5649729509562285346910129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15065945358832760925093677 5649729509562285346910129)
                ·
                  refine ⟨4237297132171714010182597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5649729509562285346910129 4237297132171714010182597)
                  ·
                    refine ⟨794493212282196376909237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4237297132171714010182597 794493212282196376909237)
                    ·
                      rfl

theorem cell23_4641810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4641810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641810 prefixEnd_4641810 := by exact prefixLift 4641810
  have htrace : WordTrace (prefixWord ++ tailWord_4641810) baseStart_4641810 baseEnd_4641810 := by
    simpa [prefixWord, tailWord_4641810, baseEnd_4641810] using wordTrace_append hprefix tailTrace_4641810
  have hstable : (prefixWord ++ tailWord_4641810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641810).length < 2 ^ (prefixWord ++ tailWord_4641810).sum := by decide
  have hdescent : baseEnd_4641810 < baseStart_4641810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641816 : List Nat := [2, 1, 2, 3, 2, 3, 1, 3, 2, 1, 3]
def baseStart_4641816 : Nat := 118140960795 + 4641816 * 2 ^ 59
def prefixEnd_4641816 : Nat := 4983230072969 + 3 ^ 40 * 4641816 * 2
def baseEnd_4641816 : Nat := 2383482717730516107252683

theorem tailTrace_4641816 : CollatzResearch.WordTrace tailWord_4641816 prefixEnd_4641816 2383482717730516107252683 := by
  unfold tailWord_4641816
  simp only [CollatzResearch.WordTrace]
  refine ⟨84650469075750432951568651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112867292101000577268758201 84650469075750432951568651)
  ·
    refine ⟨126975703613625649427352977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84650469075750432951568651 126975703613625649427352977)
    ·
      refine ⟨95231777710219237070514733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126975703613625649427352977 95231777710219237070514733)
      ·
        refine ⟨35711916641332213901443025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95231777710219237070514733 35711916641332213901443025)
        ·
          refine ⟨26783937480999160426082269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35711916641332213901443025 26783937480999160426082269)
          ·
            refine ⟨10043976555374685159780851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26783937480999160426082269 10043976555374685159780851)
            ·
              refine ⟨15065964833062027739671277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10043976555374685159780851 15065964833062027739671277)
              ·
                refine ⟨5649736812398260402376729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15065964833062027739671277 5649736812398260402376729)
                ·
                  refine ⟨4237302609298695301782547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5649736812398260402376729 4237302609298695301782547)
                  ·
                    refine ⟨6355953913948042952673821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4237302609298695301782547 6355953913948042952673821)
                    ·
                      refine ⟨2383482717730516107252683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6355953913948042952673821 2383482717730516107252683)
                      ·
                        rfl

theorem cell23_4641816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_4641816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641816 prefixEnd_4641816 := by exact prefixLift 4641816
  have htrace : WordTrace (prefixWord ++ tailWord_4641816) baseStart_4641816 baseEnd_4641816 := by
    simpa [prefixWord, tailWord_4641816, baseEnd_4641816] using wordTrace_append hprefix tailTrace_4641816
  have hstable : (prefixWord ++ tailWord_4641816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641816).length < 2 ^ (prefixWord ++ tailWord_4641816).sum := by decide
  have hdescent : baseEnd_4641816 < baseStart_4641816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641826 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_4641826 : Nat := 118140960795 + 4641826 * 2 ^ 59
def prefixEnd_4641826 : Nat := 4983230072969 + 3 ^ 40 * 4641826 * 2
def baseEnd_4641826 : Nat := 2383487852537061068127637

theorem tailTrace_4641826 : CollatzResearch.WordTrace tailWord_4641826 prefixEnd_4641826 2383487852537061068127637 := by
  unfold tailWord_4641826
  simp only [CollatzResearch.WordTrace]
  refine ⟨42325325720366159402750333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112867535254309758407334221 42325325720366159402750333)
  ·
    refine ⟨15871997145137309776031375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42325325720366159402750333 15871997145137309776031375)
    ·
      refine ⟨23807995717705964664047063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15871997145137309776031375 23807995717705964664047063)
      ·
        refine ⟨35711993576558946996070595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23807995717705964664047063 35711993576558946996070595)
        ·
          refine ⟨53567990364838420494105893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35711993576558946996070595 53567990364838420494105893)
          ·
            refine ⟨10043998193407203842644855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53567990364838420494105893 10043998193407203842644855)
            ·
              refine ⟨15065997290110805763967283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10043998193407203842644855 15065997290110805763967283)
              ·
                refine ⟨22598995935166208645950925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15065997290110805763967283 22598995935166208645950925)
                ·
                  refine ⟨8474623475687328242231597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22598995935166208645950925 8474623475687328242231597)
                  ·
                    refine ⟨3177983803382748090836849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8474623475687328242231597 3177983803382748090836849)
                    ·
                      refine ⟨2383487852537061068127637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3177983803382748090836849 2383487852537061068127637)
                      ·
                        rfl

theorem cell23_4641826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_4641826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641826 prefixEnd_4641826 := by exact prefixLift 4641826
  have htrace : WordTrace (prefixWord ++ tailWord_4641826) baseStart_4641826 baseEnd_4641826 := by
    simpa [prefixWord, tailWord_4641826, baseEnd_4641826] using wordTrace_append hprefix tailTrace_4641826
  have hstable : (prefixWord ++ tailWord_4641826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641826).length < 2 ^ (prefixWord ++ tailWord_4641826).sum := by decide
  have hdescent : baseEnd_4641826 < baseStart_4641826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641842 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_4641842 : Nat := 118140960795 + 4641842 * 2 ^ 59
def prefixEnd_4641842 : Nat := 4983230072969 + 3 ^ 40 * 4641842 * 2
def baseEnd_4641842 : Nat := 2383496068227533005527563

theorem tailTrace_4641842 : CollatzResearch.WordTrace tailWord_4641842 prefixEnd_4641842 2383496068227533005527563 := by
  unfold tailWord_4641842
  simp only [CollatzResearch.WordTrace]
  refine ⟨42325471612351668085895945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112867924299604448229055853 42325471612351668085895945)
  ·
    refine ⟨31744103709263751064421959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42325471612351668085895945 31744103709263751064421959)
    ·
      refine ⟨47616155563895626596632939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31744103709263751064421959 47616155563895626596632939)
      ·
        refine ⟨71424233345843439894949409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47616155563895626596632939 71424233345843439894949409)
        ·
          refine ⟨53568175009382579921212057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71424233345843439894949409 53568175009382579921212057)
          ·
            refine ⟨40176131257036934940909043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53568175009382579921212057 40176131257036934940909043)
            ·
              refine ⟨60264196885555402411363565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40176131257036934940909043 60264196885555402411363565)
              ·
                refine ⟨22599073832083275904261337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60264196885555402411363565 22599073832083275904261337)
                ·
                  refine ⟨16949305374062456928196003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22599073832083275904261337 16949305374062456928196003)
                  ·
                    refine ⟨25423958061093685392294005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16949305374062456928196003 25423958061093685392294005)
                    ·
                      refine ⟨2383496068227533005527563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25423958061093685392294005 2383496068227533005527563)
                      ·
                        rfl

theorem cell23_4641842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_4641842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641842 prefixEnd_4641842 := by exact prefixLift 4641842
  have htrace : WordTrace (prefixWord ++ tailWord_4641842) baseStart_4641842 baseEnd_4641842 := by
    simpa [prefixWord, tailWord_4641842, baseEnd_4641842] using wordTrace_append hprefix tailTrace_4641842
  have hstable : (prefixWord ++ tailWord_4641842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641842).length < 2 ^ (prefixWord ++ tailWord_4641842).sum := by decide
  have hdescent : baseEnd_4641842 < baseStart_4641842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641869 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_4641869 : Nat := 118140960795 + 4641869 * 2 ^ 59
def prefixEnd_4641869 : Nat := 4983230072969 + 3 ^ 40 * 4641869 * 2
def baseEnd_4641869 : Nat := 2383509932205204399889939

theorem tailTrace_4641869 : CollatzResearch.WordTrace tailWord_4641869 prefixEnd_4641869 2383509932205204399889939 := by
  unfold tailWord_4641869
  simp only [CollatzResearch.WordTrace]
  refine ⟨169302871220308855954816661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112868580813539237303211107 169302871220308855954816661)
  ·
    refine ⟨7936072088451977622882031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 169302871220308855954816661 7936072088451977622882031)
    ·
      refine ⟨11904108132677966434323047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7936072088451977622882031 11904108132677966434323047)
      ·
        refine ⟨17856162199016949651484571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11904108132677966434323047 17856162199016949651484571)
        ·
          refine ⟨26784243298525424477226857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17856162199016949651484571 26784243298525424477226857)
          ·
            refine ⟨20088182473894068357920143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26784243298525424477226857 20088182473894068357920143)
            ·
              refine ⟨30132273710841102536880215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20088182473894068357920143 30132273710841102536880215)
              ·
                refine ⟨45198410566261653805320323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30132273710841102536880215 45198410566261653805320323)
                ·
                  refine ⟨67797615849392480707980485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45198410566261653805320323 67797615849392480707980485)
                  ·
                    refine ⟨12712052971761090132746341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67797615849392480707980485 12712052971761090132746341)
                    ·
                      refine ⟨2383509932205204399889939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12712052971761090132746341 2383509932205204399889939)
                      ·
                        rfl

theorem cell23_4641869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_4641869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641869 prefixEnd_4641869 := by exact prefixLift 4641869
  have htrace : WordTrace (prefixWord ++ tailWord_4641869) baseStart_4641869 baseEnd_4641869 := by
    simpa [prefixWord, tailWord_4641869, baseEnd_4641869] using wordTrace_append hprefix tailTrace_4641869
  have hstable : (prefixWord ++ tailWord_4641869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641869).length < 2 ^ (prefixWord ++ tailWord_4641869).sum := by decide
  have hdescent : baseEnd_4641869 < baseStart_4641869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641939 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 3, 4]
def baseStart_4641939 : Nat := 118140960795 + 4641939 * 2 ^ 59
def prefixEnd_4641939 : Nat := 4983230072969 + 3 ^ 40 * 4641939 * 2
def baseEnd_4641939 : Nat := 794515291950339708671539

theorem tailTrace_4641939 : CollatzResearch.WordTrace tailWord_4641939 prefixEnd_4641939 794515291950339708671539 := by
  unfold tailWord_4641939
  simp only [CollatzResearch.WordTrace]
  refine ⟨169305424330055257909864871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112870282886703505273243247 169305424330055257909864871)
  ·
    refine ⟨253958136495082886864797307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169305424330055257909864871 253958136495082886864797307)
    ·
      refine ⟨380937204742624330297195961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253958136495082886864797307 380937204742624330297195961)
      ·
        refine ⟨285702903556968247722896971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380937204742624330297195961 285702903556968247722896971)
        ·
          refine ⟨428554355335452371584345457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285702903556968247722896971 428554355335452371584345457)
          ·
            refine ⟨321415766501589278688259093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428554355335452371584345457 321415766501589278688259093)
            ·
              refine ⟨15066364054761997438512145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 321415766501589278688259093 15066364054761997438512145)
              ·
                refine ⟨11299773041071498078884109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15066364054761997438512145 11299773041071498078884109)
                ·
                  refine ⟨4237414890401811779581541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11299773041071498078884109 4237414890401811779581541)
                  ·
                    refine ⟨794515291950339708671539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4237414890401811779581541 794515291950339708671539)
                    ·
                      rfl

theorem cell23_4641939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 4].length) (baseStart_4641939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641939 prefixEnd_4641939 := by exact prefixLift 4641939
  have htrace : WordTrace (prefixWord ++ tailWord_4641939) baseStart_4641939 baseEnd_4641939 := by
    simpa [prefixWord, tailWord_4641939, baseEnd_4641939] using wordTrace_append hprefix tailTrace_4641939
  have hstable : (prefixWord ++ tailWord_4641939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641939).length < 2 ^ (prefixWord ++ tailWord_4641939).sum := by decide
  have hdescent : baseEnd_4641939 < baseStart_4641939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641949 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_4641949 : Nat := 118140960795 + 4641949 * 2 ^ 59
def prefixEnd_4641949 : Nat := 4983230072969 + 3 ^ 40 * 4641949 * 2
def baseEnd_4641949 : Nat := 2383551010657564086889571

theorem tailTrace_4641949 : CollatzResearch.WordTrace tailWord_4641949 prefixEnd_4641949 2383551010657564086889571 := by
  unfold tailWord_4641949
  simp only [CollatzResearch.WordTrace]
  refine ⟨169305789060019029617728901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112870526040012686411819267 169305789060019029617728901)
  ·
    refine ⟨31744835448753568053324169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169305789060019029617728901 31744835448753568053324169)
    ·
      refine ⟨23808626586565176039993127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31744835448753568053324169 23808626586565176039993127)
      ·
        refine ⟨35712939879847764059989691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23808626586565176039993127 35712939879847764059989691)
        ·
          refine ⟨53569409819771646089984537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35712939879847764059989691 53569409819771646089984537)
          ·
            refine ⟨40177057364828734567488403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53569409819771646089984537 40177057364828734567488403)
            ·
              refine ⟨60265586047243101851232605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40177057364828734567488403 60265586047243101851232605)
              ·
                refine ⟨22599594767716163194212227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60265586047243101851232605 22599594767716163194212227)
                ·
                  refine ⟨33899392151574244791318341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22599594767716163194212227 33899392151574244791318341)
                  ·
                    refine ⟨6356136028420170898372189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33899392151574244791318341 6356136028420170898372189)
                    ·
                      refine ⟨2383551010657564086889571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6356136028420170898372189 2383551010657564086889571)
                      ·
                        rfl

theorem cell23_4641949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_4641949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641949 prefixEnd_4641949 := by exact prefixLift 4641949
  have htrace : WordTrace (prefixWord ++ tailWord_4641949) baseStart_4641949 baseEnd_4641949 := by
    simpa [prefixWord, tailWord_4641949, baseEnd_4641949] using wordTrace_append hprefix tailTrace_4641949
  have hstable : (prefixWord ++ tailWord_4641949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641949).length < 2 ^ (prefixWord ++ tailWord_4641949).sum := by decide
  have hdescent : baseEnd_4641949 < baseStart_4641949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641952 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 10]
def baseStart_4641952 : Nat := 118140960795 + 4641952 * 2 ^ 59
def prefixEnd_4641952 : Nat := 4983230072969 + 3 ^ 40 * 4641952 * 2
def baseEnd_4641952 : Nat := 264839172344391952794673

theorem tailTrace_4641952 : CollatzResearch.WordTrace tailWord_4641952 prefixEnd_4641952 264839172344391952794673 := by
  unfold tailWord_4641952
  simp only [CollatzResearch.WordTrace]
  refine ⟨84652949239504080565044055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112870598986005440753392073 84652949239504080565044055)
  ·
    refine ⟨126979423859256120847566083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84652949239504080565044055 126979423859256120847566083)
    ·
      refine ⟨190469135788884181271349125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126979423859256120847566083 190469135788884181271349125)
      ·
        refine ⟨35712962960415783988377961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190469135788884181271349125 35712962960415783988377961)
        ·
          refine ⟨26784722220311837991283471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35712962960415783988377961 26784722220311837991283471)
          ·
            refine ⟨40177083330467756986925207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26784722220311837991283471 40177083330467756986925207)
            ·
              refine ⟨60265624995701635480387811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40177083330467756986925207 60265624995701635480387811)
              ·
                refine ⟨90398437493552453220581717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60265624995701635480387811 90398437493552453220581717)
                ·
                  refine ⟨264839172344391952794673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 90398437493552453220581717 264839172344391952794673)
                  ·
                    rfl

theorem cell23_4641952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 10].length) (baseStart_4641952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641952 prefixEnd_4641952 := by exact prefixLift 4641952
  have htrace : WordTrace (prefixWord ++ tailWord_4641952) baseStart_4641952 baseEnd_4641952 := by
    simpa [prefixWord, tailWord_4641952, baseEnd_4641952] using wordTrace_append hprefix tailTrace_4641952
  have hstable : (prefixWord ++ tailWord_4641952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641952).length < 2 ^ (prefixWord ++ tailWord_4641952).sum := by decide
  have hdescent : baseEnd_4641952 < baseStart_4641952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641969 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 8]
def baseStart_4641969 : Nat := 118140960795 + 4641969 * 2 ^ 59
def prefixEnd_4641969 : Nat := 4983230072969 + 3 ^ 40 * 4641969 * 2
def baseEnd_4641969 : Nat := 264840142252294889848831

theorem tailTrace_4641969 : CollatzResearch.WordTrace tailWord_4641969 prefixEnd_4641969 264840142252294889848831 := by
  unfold tailWord_4641969
  simp only [CollatzResearch.WordTrace]
  refine ⟨169306518519946573033456961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112871012346631048688971307 169306518519946573033456961)
  ·
    refine ⟨126979888889959929775092721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169306518519946573033456961 126979888889959929775092721)
    ·
      refine ⟨95234916667469947331319541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126979888889959929775092721 95234916667469947331319541)
      ·
        refine ⟨8928273437575307562311207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95234916667469947331319541 8928273437575307562311207)
        ·
          refine ⟨13392410156362961343466811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8928273437575307562311207 13392410156362961343466811)
          ·
            refine ⟨20088615234544442015200217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13392410156362961343466811 20088615234544442015200217)
            ·
              refine ⟨15066461425908331511400163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20088615234544442015200217 15066461425908331511400163)
              ·
                refine ⟨22599692138862497267100245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15066461425908331511400163 22599692138862497267100245)
                ·
                  refine ⟨264840142252294889848831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22599692138862497267100245 264840142252294889848831)
                  ·
                    rfl

theorem cell23_4641969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 8].length) (baseStart_4641969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641969 prefixEnd_4641969 := by exact prefixLift 4641969
  have htrace : WordTrace (prefixWord ++ tailWord_4641969) baseStart_4641969 baseEnd_4641969 := by
    simpa [prefixWord, tailWord_4641969, baseEnd_4641969] using wordTrace_append hprefix tailTrace_4641969
  have hstable : (prefixWord ++ tailWord_4641969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641969).length < 2 ^ (prefixWord ++ tailWord_4641969).sum := by decide
  have hdescent : baseEnd_4641969 < baseStart_4641969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4641999 : List Nat := [1, 1, 2, 1, 1, 3, 2, 6, 1, 5]
def baseStart_4641999 : Nat := 118140960795 + 4641999 * 2 ^ 59
def prefixEnd_4641999 : Nat := 4983230072969 + 3 ^ 40 * 4641999 * 2
def baseEnd_4641999 : Nat := 794525561563429630421447

theorem tailTrace_4641999 : CollatzResearch.WordTrace tailWord_4641999 prefixEnd_4641999 794525561563429630421447 := by
  unfold tailWord_4641999
  simp only [CollatzResearch.WordTrace]
  refine ⟨169307612709837888157049051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112871741806558592104699367 169307612709837888157049051)
  ·
    refine ⟨253961419064756832235573577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169307612709837888157049051 253961419064756832235573577)
    ·
      refine ⟨190471064298567624176680183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253961419064756832235573577 190471064298567624176680183)
      ·
        refine ⟨285706596447851436265020275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190471064298567624176680183 285706596447851436265020275)
        ·
          refine ⟨428559894671777154397530413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285706596447851436265020275 428559894671777154397530413)
          ·
            refine ⟨160709960501916432899073905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 428559894671777154397530413 160709960501916432899073905)
            ·
              refine ⟨120532470376437324674305429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160709960501916432899073905 120532470376437324674305429)
              ·
                refine ⟨5649959548895499594108067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120532470376437324674305429 5649959548895499594108067)
                ·
                  refine ⟨8474939323343249391162101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5649959548895499594108067 8474939323343249391162101)
                  ·
                    refine ⟨794525561563429630421447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8474939323343249391162101 794525561563429630421447)
                    ·
                      rfl

theorem cell23_4641999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 5].length) (baseStart_4641999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4641999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4641999 prefixEnd_4641999 := by exact prefixLift 4641999
  have htrace : WordTrace (prefixWord ++ tailWord_4641999) baseStart_4641999 baseEnd_4641999 := by
    simpa [prefixWord, tailWord_4641999, baseEnd_4641999] using wordTrace_append hprefix tailTrace_4641999
  have hstable : (prefixWord ++ tailWord_4641999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4641999).length < 2 ^ (prefixWord ++ tailWord_4641999).sum := by decide
  have hdescent : baseEnd_4641999 < baseStart_4641999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4641999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642046 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_4642046 : Nat := 118140960795 + 4642046 * 2 ^ 59
def prefixEnd_4642046 : Nat := 4983230072969 + 3 ^ 40 * 4642046 * 2
def baseEnd_4642046 : Nat := 794533606093683402458875

theorem tailTrace_4642046 : CollatzResearch.WordTrace tailWord_4642046 prefixEnd_4642046 794533606093683402458875 := by
  unfold tailWord_4642046
  simp only [CollatzResearch.WordTrace]
  refine ⟨21163665867583451898001249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112872884627111743456006661 21163665867583451898001249)
  ·
    refine ⟨15872749400687588923500937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21163665867583451898001249 15872749400687588923500937)
    ·
      refine ⟨11904562050515691692625703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15872749400687588923500937 11904562050515691692625703)
      ·
        refine ⟨17856843075773537538938555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11904562050515691692625703 17856843075773537538938555)
        ·
          refine ⟨26785264613660306308407833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17856843075773537538938555 26785264613660306308407833)
          ·
            refine ⟨20088948460245229731305875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26785264613660306308407833 20088948460245229731305875)
            ·
              refine ⟨30133422690367844596958813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20088948460245229731305875 30133422690367844596958813)
              ·
                refine ⟨11300033508887941723859555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30133422690367844596958813 11300033508887941723859555)
                ·
                  refine ⟨16950050263331912585789333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11300033508887941723859555 16950050263331912585789333)
                  ·
                    refine ⟨794533606093683402458875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16950050263331912585789333 794533606093683402458875)
                    ·
                      rfl

theorem cell23_4642046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_4642046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642046 prefixEnd_4642046 := by exact prefixLift 4642046
  have htrace : WordTrace (prefixWord ++ tailWord_4642046) baseStart_4642046 baseEnd_4642046 := by
    simpa [prefixWord, tailWord_4642046, baseEnd_4642046] using wordTrace_append hprefix tailTrace_4642046
  have hstable : (prefixWord ++ tailWord_4642046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642046).length < 2 ^ (prefixWord ++ tailWord_4642046).sum := by decide
  have hdescent : baseEnd_4642046 < baseStart_4642046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642053 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 3, 2, 2]
def baseStart_4642053 : Nat := 118140960795 + 4642053 * 2 ^ 59
def prefixEnd_4642053 : Nat := 4983230072969 + 3 ^ 40 * 4642053 * 2
def baseEnd_4642053 : Nat := 2383604412645631679989093

theorem tailTrace_4642053 : CollatzResearch.WordTrace tailWord_4642053 prefixEnd_4642053 2383604412645631679989093 := by
  unfold tailWord_4642053
  simp only [CollatzResearch.WordTrace]
  refine ⟨169309582251642255379514813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112873054834428170253009875 169309582251642255379514813)
  ·
    refine ⟨63491093344365845767318055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169309582251642255379514813 63491093344365845767318055)
    ·
      refine ⟨95236640016548768650977083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63491093344365845767318055 95236640016548768650977083)
      ·
        refine ⟨142854960024823152976465625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95236640016548768650977083 142854960024823152976465625)
        ·
          refine ⟨107141220018617364732349219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142854960024823152976465625 107141220018617364732349219)
          ·
            refine ⟨160711830027926047098523829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107141220018617364732349219 160711830027926047098523829)
            ·
              refine ⟨15066734065118066915486609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 160711830027926047098523829 15066734065118066915486609)
              ·
                refine ⟨11300050548838550186614957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15066734065118066915486609 11300050548838550186614957)
                ·
                  refine ⟨4237518955814456319980609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11300050548838550186614957 4237518955814456319980609)
                  ·
                    refine ⟨3178139216860842239985457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4237518955814456319980609 3178139216860842239985457)
                    ·
                      refine ⟨2383604412645631679989093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3178139216860842239985457 2383604412645631679989093)
                      ·
                        rfl

theorem cell23_4642053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 2, 2].length) (baseStart_4642053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642053 prefixEnd_4642053 := by exact prefixLift 4642053
  have htrace : WordTrace (prefixWord ++ tailWord_4642053) baseStart_4642053 baseEnd_4642053 := by
    simpa [prefixWord, tailWord_4642053, baseEnd_4642053] using wordTrace_append hprefix tailTrace_4642053
  have hstable : (prefixWord ++ tailWord_4642053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642053).length < 2 ^ (prefixWord ++ tailWord_4642053).sum := by decide
  have hdescent : baseEnd_4642053 < baseStart_4642053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642080 : List Nat := [2, 1, 1, 5, 3, 2, 1, 2, 2, 4]
def baseStart_4642080 : Nat := 118140960795 + 4642080 * 2 ^ 59
def prefixEnd_4642080 : Nat := 4983230072969 + 3 ^ 40 * 4642080 * 2
def baseEnd_4642080 : Nat := 794539425541101024783823

theorem tailTrace_4642080 : CollatzResearch.WordTrace tailWord_4642080 prefixEnd_4642080 794539425541101024783823 := by
  unfold tailWord_4642080
  simp only [CollatzResearch.WordTrace]
  refine ⟨84655283511272219495373847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112873711348362959327165129 84655283511272219495373847)
  ·
    refine ⟨126982925266908329243060771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84655283511272219495373847 126982925266908329243060771)
    ·
      refine ⟨190474387900362493864591157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126982925266908329243060771 190474387900362493864591157)
      ·
        refine ⟨17856973865658983799805421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 190474387900362493864591157 17856973865658983799805421)
        ·
          refine ⟨6696365199622118924927033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17856973865658983799805421 6696365199622118924927033)
          ·
            refine ⟨5022273899716589193695275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6696365199622118924927033 5022273899716589193695275)
            ·
              refine ⟨7533410849574883790542913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5022273899716589193695275 7533410849574883790542913)
              ·
                refine ⟨5650058137181162842907185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7533410849574883790542913 5650058137181162842907185)
                ·
                  refine ⟨4237543602885872132180389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5650058137181162842907185 4237543602885872132180389)
                  ·
                    refine ⟨794539425541101024783823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4237543602885872132180389 794539425541101024783823)
                    ·
                      rfl

theorem cell23_4642080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 2, 4].length) (baseStart_4642080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642080 prefixEnd_4642080 := by exact prefixLift 4642080
  have htrace : WordTrace (prefixWord ++ tailWord_4642080) baseStart_4642080 baseEnd_4642080 := by
    simpa [prefixWord, tailWord_4642080, baseEnd_4642080] using wordTrace_append hprefix tailTrace_4642080
  have hstable : (prefixWord ++ tailWord_4642080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642080).length < 2 ^ (prefixWord ++ tailWord_4642080).sum := by decide
  have hdescent : baseEnd_4642080 < baseStart_4642080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642146 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_4642146 : Nat := 118140960795 + 4642146 * 2 ^ 59
def prefixEnd_4642146 : Nat := 4983230072969 + 3 ^ 40 * 4642146 * 2
def baseEnd_4642146 : Nat := 2383652166346499816126165

theorem tailTrace_4642146 : CollatzResearch.WordTrace tailWord_4642146 prefixEnd_4642146 2383652166346499816126165 := by
  unfold tailWord_4642146
  simp only [CollatzResearch.WordTrace]
  refine ⟨42328243560076333065662573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112875316160203554841766861 42328243560076333065662573)
  ·
    refine ⟨15873091335028624899623465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42328243560076333065662573 15873091335028624899623465)
    ·
      refine ⟨11904818501271468674717599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15873091335028624899623465 11904818501271468674717599)
      ·
        refine ⟨17857227751907203012076399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11904818501271468674717599 17857227751907203012076399)
        ·
          refine ⟨26785841627860804518114599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17857227751907203012076399 26785841627860804518114599)
          ·
            refine ⟨40178762441791206777171899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26785841627860804518114599 40178762441791206777171899)
            ·
              refine ⟨60268143662686810165757849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40178762441791206777171899 60268143662686810165757849)
              ·
                refine ⟨45201107747015107624318387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60268143662686810165757849 45201107747015107624318387)
                ·
                  refine ⟨67801661620522661436477581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45201107747015107624318387 67801661620522661436477581)
                  ·
                    refine ⟨25425623107695998038679093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67801661620522661436477581 25425623107695998038679093)
                    ·
                      refine ⟨2383652166346499816126165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25425623107695998038679093 2383652166346499816126165)
                      ·
                        rfl

theorem cell23_4642146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_4642146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642146 prefixEnd_4642146 := by exact prefixLift 4642146
  have htrace : WordTrace (prefixWord ++ tailWord_4642146) baseStart_4642146 baseEnd_4642146 := by
    simpa [prefixWord, tailWord_4642146, baseEnd_4642146] using wordTrace_append hprefix tailTrace_4642146
  have hstable : (prefixWord ++ tailWord_4642146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642146).length < 2 ^ (prefixWord ++ tailWord_4642146).sum := by decide
  have hdescent : baseEnd_4642146 < baseStart_4642146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642154 : List Nat := [3, 1, 3, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_4642154 : Nat := 118140960795 + 4642154 * 2 ^ 59
def prefixEnd_4642154 : Nat := 4983230072969 + 3 ^ 40 * 4642154 * 2
def baseEnd_4642154 : Nat := 2383656274191735784826129

theorem tailTrace_4642154 : CollatzResearch.WordTrace tailWord_4642154 prefixEnd_4642154 2383656274191735784826129 := by
  unfold tailWord_4642154
  simp only [CollatzResearch.WordTrace]
  refine ⟨42328316506069087407235379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112875510682850899752627677 42328316506069087407235379)
  ·
    refine ⟨63492474759103631110853069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42328316506069087407235379 63492474759103631110853069)
    ·
      refine ⟨23809678034663861666569901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63492474759103631110853069 23809678034663861666569901)
      ·
        refine ⟨8928629262998948124963713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23809678034663861666569901 8928629262998948124963713)
        ·
          refine ⟨6696471947249211093722785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8928629262998948124963713 6696471947249211093722785)
          ·
            refine ⟨5022353960436908320292089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6696471947249211093722785 5022353960436908320292089)
            ·
              refine ⟨3766765470327681240219067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5022353960436908320292089 3766765470327681240219067)
              ·
                refine ⟨5650148205491521860328601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766765470327681240219067 5650148205491521860328601)
                ·
                  refine ⟨4237611154118641395246451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5650148205491521860328601 4237611154118641395246451)
                  ·
                    refine ⟨6356416731177962092869677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4237611154118641395246451 6356416731177962092869677)
                    ·
                      refine ⟨2383656274191735784826129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6356416731177962092869677 2383656274191735784826129)
                      ·
                        rfl

theorem cell23_4642154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_4642154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642154 prefixEnd_4642154 := by exact prefixLift 4642154
  have htrace : WordTrace (prefixWord ++ tailWord_4642154) baseStart_4642154 baseEnd_4642154 := by
    simpa [prefixWord, tailWord_4642154, baseEnd_4642154] using wordTrace_append hprefix tailTrace_4642154
  have hstable : (prefixWord ++ tailWord_4642154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642154).length < 2 ^ (prefixWord ++ tailWord_4642154).sum := by decide
  have hdescent : baseEnd_4642154 < baseStart_4642154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642160 : List Nat := [2, 1, 1, 1, 4, 2, 3, 3, 2, 2, 2]
def baseStart_4642160 : Nat := 118140960795 + 4642160 * 2 ^ 59
def prefixEnd_4642160 : Nat := 4983230072969 + 3 ^ 40 * 4642160 * 2
def baseEnd_4642160 : Nat := 2383659355075662761351101

theorem tailTrace_4642160 : CollatzResearch.WordTrace tailWord_4642160 prefixEnd_4642160 2383659355075662761351101 := by
  unfold tailWord_4642160
  simp only [CollatzResearch.WordTrace]
  refine ⟨84656742431127306326829967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112875656574836408435773289 84656742431127306326829967)
  ·
    refine ⟨126985113646690959490244951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84656742431127306326829967 126985113646690959490244951)
    ·
      refine ⟨190477670470036439235367427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126985113646690959490244951 190477670470036439235367427)
      ·
        refine ⟨285716505705054658853051141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190477670470036439235367427 285716505705054658853051141)
        ·
          refine ⟨53571844819697748534947089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 285716505705054658853051141 53571844819697748534947089)
          ·
            refine ⟨40178883614773311401210317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53571844819697748534947089 40178883614773311401210317)
            ·
              refine ⟨15067081355539991775453869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40178883614773311401210317 15067081355539991775453869)
              ·
                refine ⟨5650155508327496915795201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15067081355539991775453869 5650155508327496915795201)
                ·
                  refine ⟨4237616631245622686846401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5650155508327496915795201 4237616631245622686846401)
                  ·
                    refine ⟨3178212473434217015134801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4237616631245622686846401 3178212473434217015134801)
                    ·
                      refine ⟨2383659355075662761351101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3178212473434217015134801 2383659355075662761351101)
                      ·
                        rfl

theorem cell23_4642160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 2, 2, 2].length) (baseStart_4642160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642160 prefixEnd_4642160 := by exact prefixLift 4642160
  have htrace : WordTrace (prefixWord ++ tailWord_4642160) baseStart_4642160 baseEnd_4642160 := by
    simpa [prefixWord, tailWord_4642160, baseEnd_4642160] using wordTrace_append hprefix tailTrace_4642160
  have hstable : (prefixWord ++ tailWord_4642160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642160).length < 2 ^ (prefixWord ++ tailWord_4642160).sum := by decide
  have hdescent : baseEnd_4642160 < baseStart_4642160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642200 : List Nat := [2, 1, 2, 5, 2, 1, 1, 4, 5]
def baseStart_4642200 : Nat := 118140960795 + 4642200 * 2 ^ 59
def prefixEnd_4642200 : Nat := 4983230072969 + 3 ^ 40 * 4642200 * 2
def baseEnd_4642200 : Nat := 264853321589093622761213

theorem tailTrace_4642200 : CollatzResearch.WordTrace tailWord_4642200 prefixEnd_4642200 264853321589093622761213 := by
  unfold tailWord_4642200
  simp only [CollatzResearch.WordTrace]
  refine ⟨84657471891054849742558027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112876629188073132990077369 84657471891054849742558027)
  ·
    refine ⟨126986207836582274613837041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84657471891054849742558027 126986207836582274613837041)
    ·
      refine ⟨95239655877436705960377781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126986207836582274613837041 95239655877436705960377781)
      ·
        refine ⟨8928717738509691183785417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95239655877436705960377781 8928717738509691183785417)
        ·
          refine ⟨6696538303882268387839063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8928717738509691183785417 6696538303882268387839063)
          ·
            refine ⟨10044807455823402581758595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6696538303882268387839063 10044807455823402581758595)
            ·
              refine ⟨15067211183735103872637893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10044807455823402581758595 15067211183735103872637893)
              ·
                refine ⟨2825102096950331976119605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15067211183735103872637893 2825102096950331976119605)
                ·
                  refine ⟨264853321589093622761213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2825102096950331976119605 264853321589093622761213)
                  ·
                    rfl

theorem cell23_4642200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 5].length) (baseStart_4642200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642200 prefixEnd_4642200 := by exact prefixLift 4642200
  have htrace : WordTrace (prefixWord ++ tailWord_4642200) baseStart_4642200 baseEnd_4642200 := by
    simpa [prefixWord, tailWord_4642200, baseEnd_4642200] using wordTrace_append hprefix tailTrace_4642200
  have hstable : (prefixWord ++ tailWord_4642200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642200).length < 2 ^ (prefixWord ++ tailWord_4642200).sum := by decide
  have hdescent : baseEnd_4642200 < baseStart_4642200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642233 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 1, 3, 4]
def baseStart_4642233 : Nat := 118140960795 + 4642233 * 2 ^ 59
def prefixEnd_4642233 : Nat := 4983230072969 + 3 ^ 40 * 4642233 * 2
def baseEnd_4642233 : Nat := 2383696839163440975738265

theorem tailTrace_4642233 : CollatzResearch.WordTrace tailWord_4642233 prefixEnd_4642233 2383696839163440975738265 := by
  unfold tailWord_4642233
  simp only [CollatzResearch.WordTrace]
  refine ⟨169316147390990146121067353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112877431593993430747378235 169316147390990146121067353)
  ·
    refine ⟨126987110543242609590800515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169316147390990146121067353 126987110543242609590800515)
    ·
      refine ⟨190480665814863914386200773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126987110543242609590800515 190480665814863914386200773)
      ·
        refine ⟨35715124840286983947412645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190480665814863914386200773 35715124840286983947412645)
        ·
          refine ⟨6696585907553809490139871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35715124840286983947412645 6696585907553809490139871)
          ·
            refine ⟨10044878861330714235209807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6696585907553809490139871 10044878861330714235209807)
            ·
              refine ⟨15067318291996071352814711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10044878861330714235209807 15067318291996071352814711)
              ·
                refine ⟨22600977437994107029222067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15067318291996071352814711 22600977437994107029222067)
                ·
                  refine ⟨33901466156991160543833101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22600977437994107029222067 33901466156991160543833101)
                  ·
                    refine ⟨12713049808871685203937413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33901466156991160543833101 12713049808871685203937413)
                    ·
                      refine ⟨2383696839163440975738265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12713049808871685203937413 2383696839163440975738265)
                      ·
                        rfl

theorem cell23_4642233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_4642233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642233 prefixEnd_4642233 := by exact prefixLift 4642233
  have htrace : WordTrace (prefixWord ++ tailWord_4642233) baseStart_4642233 baseEnd_4642233 := by
    simpa [prefixWord, tailWord_4642233, baseEnd_4642233] using wordTrace_append hprefix tailTrace_4642233
  have hstable : (prefixWord ++ tailWord_4642233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642233).length < 2 ^ (prefixWord ++ tailWord_4642233).sum := by decide
  have hdescent : baseEnd_4642233 < baseStart_4642233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642283 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 5, 1, 3]
def baseStart_4642283 : Nat := 118140960795 + 4642283 * 2 ^ 59
def prefixEnd_4642283 : Nat := 4983230072969 + 3 ^ 40 * 4642283 * 2
def baseEnd_4642283 : Nat := 2383722513196165780113035

theorem tailTrace_4642283 : CollatzResearch.WordTrace tailWord_4642283 prefixEnd_4642283 2383722513196165780113035 := by
  unfold tailWord_4642283
  simp only [CollatzResearch.WordTrace]
  refine ⟨169317971040809004660387503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112878647360539336440258335 169317971040809004660387503)
  ·
    refine ⟨253976956561213506990581255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169317971040809004660387503 253976956561213506990581255)
    ·
      refine ⟨380965434841820260485871883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253976956561213506990581255 380965434841820260485871883)
      ·
        refine ⟨571448152262730390728807825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380965434841820260485871883 571448152262730390728807825)
        ·
          refine ⟨428586114197047793046605869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571448152262730390728807825 428586114197047793046605869)
          ·
            refine ⟨160719792823892922392477201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 428586114197047793046605869 160719792823892922392477201)
            ·
              refine ⟨120539844617919691794357901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160719792823892922392477201 120539844617919691794357901)
              ·
                refine ⟨45202441731719884422884213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120539844617919691794357901 45202441731719884422884213)
                ·
                  refine ⟨4237728912348739164645395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45202441731719884422884213 4237728912348739164645395)
                  ·
                    refine ⟨6356593368523108746968093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4237728912348739164645395 6356593368523108746968093)
                    ·
                      refine ⟨2383722513196165780113035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6356593368523108746968093 2383722513196165780113035)
                      ·
                        rfl

theorem cell23_4642283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 1, 3].length) (baseStart_4642283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642283 prefixEnd_4642283 := by exact prefixLift 4642283
  have htrace : WordTrace (prefixWord ++ tailWord_4642283) baseStart_4642283 baseEnd_4642283 := by
    simpa [prefixWord, tailWord_4642283, baseEnd_4642283] using wordTrace_append hprefix tailTrace_4642283
  have hstable : (prefixWord ++ tailWord_4642283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642283).length < 2 ^ (prefixWord ++ tailWord_4642283).sum := by decide
  have hdescent : baseEnd_4642283 < baseStart_4642283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642294 : List Nat := [5, 1, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_4642294 : Nat := 118140960795 + 4642294 * 2 ^ 59
def prefixEnd_4642294 : Nat := 4983230072969 + 3 ^ 40 * 4642294 * 2
def baseEnd_4642294 : Nat := 794576053827788412358495

theorem tailTrace_4642294 : CollatzResearch.WordTrace tailWord_4642294 prefixEnd_4642294 794576053827788412358495 := by
  unfold tailWord_4642294
  simp only [CollatzResearch.WordTrace]
  refine ⟨10582398265235572096189871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112878914829179435692691957 10582398265235572096189871)
  ·
    refine ⟨15873597397853358144284807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10582398265235572096189871 15873597397853358144284807)
    ·
      refine ⟨23810396096780037216427211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15873597397853358144284807 23810396096780037216427211)
      ·
        refine ⟨35715594145170055824640817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23810396096780037216427211 35715594145170055824640817)
        ·
          refine ⟨26786695608877541868480613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35715594145170055824640817 26786695608877541868480613)
          ·
            refine ⟨5022505426664539100340115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26786695608877541868480613 5022505426664539100340115)
            ·
              refine ⟨7533758139996808650510173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5022505426664539100340115 7533758139996808650510173)
              ·
                refine ⟨2825159302498803243941315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7533758139996808650510173 2825159302498803243941315)
                ·
                  refine ⟨4237738953748204865911973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825159302498803243941315 4237738953748204865911973)
                  ·
                    refine ⟨794576053827788412358495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4237738953748204865911973 794576053827788412358495)
                    ·
                      rfl

theorem cell23_4642294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_4642294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642294 prefixEnd_4642294 := by exact prefixLift 4642294
  have htrace : WordTrace (prefixWord ++ tailWord_4642294) baseStart_4642294 baseEnd_4642294 := by
    simpa [prefixWord, tailWord_4642294, baseEnd_4642294] using wordTrace_append hprefix tailTrace_4642294
  have hstable : (prefixWord ++ tailWord_4642294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642294).length < 2 ^ (prefixWord ++ tailWord_4642294).sum := by decide
  have hdescent : baseEnd_4642294 < baseStart_4642294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642324 : List Nat := [2, 4, 3, 1, 2, 2, 2, 1, 6]
def baseStart_4642324 : Nat := 118140960795 + 4642324 * 2 ^ 59
def prefixEnd_4642324 : Nat := 4983230072969 + 3 ^ 40 * 4642324 * 2
def baseEnd_4642324 : Nat := 264860396211444457744483

theorem tailTrace_4642324 : CollatzResearch.WordTrace tailWord_4642324 prefixEnd_4642324 264860396211444457744483 := by
  unfold tailWord_4642324
  simp only [CollatzResearch.WordTrace]
  refine ⟨84659733216830234331315013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112879644289106979108420017 84659733216830234331315013)
  ·
    refine ⟨15873699978155668937121565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84659733216830234331315013 15873699978155668937121565)
    ·
      refine ⟨5952637491808375851420587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15873699978155668937121565 5952637491808375851420587)
      ·
        refine ⟨8928956237712563777130881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5952637491808375851420587 8928956237712563777130881)
        ·
          refine ⟨6696717178284422832848161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8928956237712563777130881 6696717178284422832848161)
          ·
            refine ⟨5022537883713317124636121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6696717178284422832848161 5022537883713317124636121)
            ·
              refine ⟨3766903412784987843477091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5022537883713317124636121 3766903412784987843477091)
              ·
                refine ⟨5650355119177481765215637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766903412784987843477091 5650355119177481765215637)
                ·
                  refine ⟨264860396211444457744483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5650355119177481765215637 264860396211444457744483)
                  ·
                    rfl

theorem cell23_4642324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_4642324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642324 prefixEnd_4642324 := by exact prefixLift 4642324
  have htrace : WordTrace (prefixWord ++ tailWord_4642324) baseStart_4642324 baseEnd_4642324 := by
    simpa [prefixWord, tailWord_4642324, baseEnd_4642324] using wordTrace_append hprefix tailTrace_4642324
  have hstable : (prefixWord ++ tailWord_4642324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642324).length < 2 ^ (prefixWord ++ tailWord_4642324).sum := by decide
  have hdescent : baseEnd_4642324 < baseStart_4642324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642333 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_4642333 : Nat := 118140960795 + 4642333 * 2 ^ 59
def prefixEnd_4642333 : Nat := 4983230072969 + 3 ^ 40 * 4642333 * 2
def baseEnd_4642333 : Nat := 794582729076296861495935

theorem tailTrace_4642333 : CollatzResearch.WordTrace tailWord_4642333 prefixEnd_4642333 794582729076296861495935 := by
  unfold tailWord_4642333
  simp only [CollatzResearch.WordTrace]
  refine ⟨169319794690627863199707653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112879863127085242133138435 169319794690627863199707653)
  ·
    refine ⟨31747461504492724349945185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169319794690627863199707653 31747461504492724349945185)
    ·
      refine ⟨23810596128369543262458889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31747461504492724349945185 23810596128369543262458889)
      ·
        refine ⟨17857947096277157446844167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23810596128369543262458889 17857947096277157446844167)
        ·
          refine ⟨26786920644415736170266251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17857947096277157446844167 26786920644415736170266251)
          ·
            refine ⟨40180380966623604255399377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26786920644415736170266251 40180380966623604255399377)
            ·
              refine ⟨30135285724967703191549533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40180380966623604255399377 30135285724967703191549533)
              ·
                refine ⟨11300732146862888696831075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30135285724967703191549533 11300732146862888696831075)
                ·
                  refine ⟨16951098220294333045246613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11300732146862888696831075 16951098220294333045246613)
                  ·
                    refine ⟨794582729076296861495935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16951098220294333045246613 794582729076296861495935)
                    ·
                      rfl

theorem cell23_4642333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_4642333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642333 prefixEnd_4642333 := by exact prefixLift 4642333
  have htrace : WordTrace (prefixWord ++ tailWord_4642333) baseStart_4642333 baseEnd_4642333 := by
    simpa [prefixWord, tailWord_4642333, baseEnd_4642333] using wordTrace_append hprefix tailTrace_4642333
  have hstable : (prefixWord ++ tailWord_4642333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642333).length < 2 ^ (prefixWord ++ tailWord_4642333).sum := by decide
  have hdescent : baseEnd_4642333 < baseStart_4642333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642344 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_4642344 : Nat := 118140960795 + 4642344 * 2 ^ 59
def prefixEnd_4642344 : Nat := 4983230072969 + 3 ^ 40 * 4642344 * 2
def baseEnd_4642344 : Nat := 2383753835516090041450255

theorem tailTrace_4642344 : CollatzResearch.WordTrace tailWord_4642344 prefixEnd_4642344 2383753835516090041450255 := by
  unfold tailWord_4642344
  simp only [CollatzResearch.WordTrace]
  refine ⟨84660097946794006039179043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112880130595725341385572057 84660097946794006039179043)
  ·
    refine ⟨126990146920191009058768565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84660097946794006039179043 126990146920191009058768565)
    ·
      refine ⟨11905326273767907099259553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126990146920191009058768565 11905326273767907099259553)
      ·
        refine ⟨8928994705325930324444665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11905326273767907099259553 8928994705325930324444665)
        ·
          refine ⟨6696746028994447743333499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8928994705325930324444665 6696746028994447743333499)
          ·
            refine ⟨10045119043491671615000249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6696746028994447743333499 10045119043491671615000249)
            ·
              refine ⟨7533839282618753711250187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10045119043491671615000249 7533839282618753711250187)
              ·
                refine ⟨11300758923928130566875281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7533839282618753711250187 11300758923928130566875281)
                ·
                  refine ⟨8475569192946097925156461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11300758923928130566875281 8475569192946097925156461)
                  ·
                    refine ⟨3178338447354786721933673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8475569192946097925156461 3178338447354786721933673)
                    ·
                      refine ⟨2383753835516090041450255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3178338447354786721933673 2383753835516090041450255)
                      ·
                        rfl

theorem cell23_4642344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_4642344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642344 prefixEnd_4642344 := by exact prefixLift 4642344
  have htrace : WordTrace (prefixWord ++ tailWord_4642344) baseStart_4642344 baseEnd_4642344 := by
    simpa [prefixWord, tailWord_4642344, baseEnd_4642344] using wordTrace_append hprefix tailTrace_4642344
  have hstable : (prefixWord ++ tailWord_4642344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642344).length < 2 ^ (prefixWord ++ tailWord_4642344).sum := by decide
  have hdescent : baseEnd_4642344 < baseStart_4642344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642350 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_4642350 : Nat := 118140960795 + 4642350 * 2 ^ 59
def prefixEnd_4642350 : Nat := 4983230072969 + 3 ^ 40 * 4642350 * 2
def baseEnd_4642350 : Nat := 794585638800005672658409

theorem tailTrace_4642350 : CollatzResearch.WordTrace tailWord_4642350 prefixEnd_4642350 794585638800005672658409 := by
  unfold tailWord_4642350
  simp only [CollatzResearch.WordTrace]
  refine ⟨21165051841445784387884563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112880276487710850068717669 21165051841445784387884563)
  ·
    refine ⟨31747577762168676581826845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21165051841445784387884563 31747577762168676581826845)
    ·
      refine ⟨11905341660813253718185067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31747577762168676581826845 11905341660813253718185067)
      ·
        refine ⟨17858012491219880577277601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11905341660813253718185067 17858012491219880577277601)
        ·
          refine ⟨13393509368414910432958201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17858012491219880577277601 13393509368414910432958201)
          ·
            refine ⟨10045132026311182824718651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13393509368414910432958201 10045132026311182824718651)
            ·
              refine ⟨15067698039466774237077977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10045132026311182824718651 15067698039466774237077977)
              ·
                refine ⟨11300773529600080677808483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15067698039466774237077977 11300773529600080677808483)
                ·
                  refine ⟨16951160294400121016712725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11300773529600080677808483 16951160294400121016712725)
                  ·
                    refine ⟨794585638800005672658409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16951160294400121016712725 794585638800005672658409)
                    ·
                      rfl

theorem cell23_4642350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_4642350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642350 prefixEnd_4642350 := by exact prefixLift 4642350
  have htrace : WordTrace (prefixWord ++ tailWord_4642350) baseStart_4642350 baseEnd_4642350 := by
    simpa [prefixWord, tailWord_4642350, baseEnd_4642350] using wordTrace_append hprefix tailTrace_4642350
  have hstable : (prefixWord ++ tailWord_4642350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642350).length < 2 ^ (prefixWord ++ tailWord_4642350).sum := by decide
  have hdescent : baseEnd_4642350 < baseStart_4642350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642357 : List Nat := [1, 3, 3, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_4642357 : Nat := 118140960795 + 4642357 * 2 ^ 59
def prefixEnd_4642357 : Nat := 4983230072969 + 3 ^ 40 * 4642357 * 2
def baseEnd_4642357 : Nat := 2383760510764598490587695

theorem tailTrace_4642357 : CollatzResearch.WordTrace tailWord_4642357 prefixEnd_4642357 2383760510764598490587695 := by
  unfold tailWord_4642357
  simp only [CollatzResearch.WordTrace]
  refine ⟨169320670042540915298581325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112880446695027276865720883 169320670042540915298581325)
  ·
    refine ⟨63495251265952843236967997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169320670042540915298581325 63495251265952843236967997)
    ·
      refine ⟨23810719224732316213862999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63495251265952843236967997 23810719224732316213862999)
      ·
        refine ⟨35716078837098474320794499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23810719224732316213862999 35716078837098474320794499)
        ·
          refine ⟨53574118255647711481191749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35716078837098474320794499 53574118255647711481191749)
          ·
            refine ⟨10045147172933945902723453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53574118255647711481191749 10045147172933945902723453)
            ·
              refine ⟨3766930189850229713521295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10045147172933945902723453 3766930189850229713521295)
              ·
                refine ⟨5650395284775344570281943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766930189850229713521295 5650395284775344570281943)
                ·
                  refine ⟨8475592927163016855422915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5650395284775344570281943 8475592927163016855422915)
                  ·
                    refine ⟨12713389390744525283134373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8475592927163016855422915 12713389390744525283134373)
                    ·
                      refine ⟨2383760510764598490587695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12713389390744525283134373 2383760510764598490587695)
                      ·
                        rfl

theorem cell23_4642357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_4642357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642357 prefixEnd_4642357 := by exact prefixLift 4642357
  have htrace : WordTrace (prefixWord ++ tailWord_4642357) baseStart_4642357 baseEnd_4642357 := by
    simpa [prefixWord, tailWord_4642357, baseEnd_4642357] using wordTrace_append hprefix tailTrace_4642357
  have hstable : (prefixWord ++ tailWord_4642357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642357).length < 2 ^ (prefixWord ++ tailWord_4642357).sum := by decide
  have hdescent : baseEnd_4642357 < baseStart_4642357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642360 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 1, 1, 5]
def baseStart_4642360 : Nat := 118140960795 + 4642360 * 2 ^ 59
def prefixEnd_4642360 : Nat := 4983230072969 + 3 ^ 40 * 4642360 * 2
def baseEnd_4642360 : Nat := 2383762051206561978850181

theorem tailTrace_4642360 : CollatzResearch.WordTrace tailWord_4642360 prefixEnd_4642360 2383762051206561978850181 := by
  unfold tailWord_4642360
  simp only [CollatzResearch.WordTrace]
  refine ⟨84660389730765023405470267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112880519641020031207293689 84660389730765023405470267)
  ·
    refine ⟨126990584596147535108205401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84660389730765023405470267 126990584596147535108205401)
    ·
      refine ⟨95242938447110651331154051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126990584596147535108205401 95242938447110651331154051)
      ·
        refine ⟨142864407670665976996731077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95242938447110651331154051 142864407670665976996731077)
        ·
          refine ⟨26787076438249870686887077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142864407670665976996731077 26787076438249870686887077)
          ·
            refine ⟨5022576832171850753791327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26787076438249870686887077 5022576832171850753791327)
            ·
              refine ⟨7533865248257776130686991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5022576832171850753791327 7533865248257776130686991)
              ·
                refine ⟨11300797872386664196030487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7533865248257776130686991 11300797872386664196030487)
                ·
                  refine ⟨16951196808579996294045731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11300797872386664196030487 16951196808579996294045731)
                  ·
                    refine ⟨25426795212869994441068597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16951196808579996294045731 25426795212869994441068597)
                    ·
                      refine ⟨2383762051206561978850181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25426795212869994441068597 2383762051206561978850181)
                      ·
                        rfl

theorem cell23_4642360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_4642360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642360 prefixEnd_4642360 := by exact prefixLift 4642360
  have htrace : WordTrace (prefixWord ++ tailWord_4642360) baseStart_4642360 baseEnd_4642360 := by
    simpa [prefixWord, tailWord_4642360, baseEnd_4642360] using wordTrace_append hprefix tailTrace_4642360
  have hstable : (prefixWord ++ tailWord_4642360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642360).length < 2 ^ (prefixWord ++ tailWord_4642360).sum := by decide
  have hdescent : baseEnd_4642360 < baseStart_4642360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642373 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 3, 3, 3]
def baseStart_4642373 : Nat := 118140960795 + 4642373 * 2 ^ 59
def prefixEnd_4642373 : Nat := 4983230072969 + 3 ^ 40 * 4642373 * 2
def baseEnd_4642373 : Nat := 2383768726455070427987621

theorem tailTrace_4642373 : CollatzResearch.WordTrace tailWord_4642373 prefixEnd_4642373 2383768726455070427987621 := by
  unfold tailWord_4642373
  simp only [CollatzResearch.WordTrace]
  refine ⟨169321253610482950031163773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112880835740321966687442515 169321253610482950031163773)
  ·
    refine ⟨63495470103931106261686415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169321253610482950031163773 63495470103931106261686415)
    ·
      refine ⟨95243205155896659392529623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63495470103931106261686415 95243205155896659392529623)
      ·
        refine ⟨142864807733844989088794435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95243205155896659392529623 142864807733844989088794435)
        ·
          refine ⟨214297211600767483633191653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142864807733844989088794435 214297211600767483633191653)
          ·
            refine ⟨40180727175143903181223435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214297211600767483633191653 40180727175143903181223435)
            ·
              refine ⟨60271090762715854771835153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40180727175143903181223435 60271090762715854771835153)
              ·
                refine ⟨45203318072036891078876365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60271090762715854771835153 45203318072036891078876365)
                ·
                  refine ⟨16951244277013834154578637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45203318072036891078876365 16951244277013834154578637)
                  ·
                    refine ⟨6356716603880187807966989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16951244277013834154578637 6356716603880187807966989)
                    ·
                      refine ⟨2383768726455070427987621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6356716603880187807966989 2383768726455070427987621)
                      ·
                        rfl

theorem cell23_4642373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_4642373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642373 prefixEnd_4642373 := by exact prefixLift 4642373
  have htrace : WordTrace (prefixWord ++ tailWord_4642373) baseStart_4642373 baseEnd_4642373 := by
    simpa [prefixWord, tailWord_4642373, baseEnd_4642373] using wordTrace_append hprefix tailTrace_4642373
  have hstable : (prefixWord ++ tailWord_4642373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642373).length < 2 ^ (prefixWord ++ tailWord_4642373).sum := by decide
  have hdescent : baseEnd_4642373 < baseStart_4642373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642443 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 4]
def baseStart_4642443 : Nat := 118140960795 + 4642443 * 2 ^ 59
def prefixEnd_4642443 : Nat := 4983230072969 + 3 ^ 40 * 4642443 * 2
def baseEnd_4642443 : Nat := 2383804670100885154112299

theorem tailTrace_4642443 : CollatzResearch.WordTrace tailWord_4642443 prefixEnd_4642443 2383804670100885154112299 := by
  unfold tailWord_4642443
  simp only [CollatzResearch.WordTrace]
  refine ⟨169323806720229351986211983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112882537813486234657474655 169323806720229351986211983)
  ·
    refine ⟨253985710080344027979317975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169323806720229351986211983 253985710080344027979317975)
    ·
      refine ⟨380978565120516041968976963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253985710080344027979317975 380978565120516041968976963)
      ·
        refine ⟨571467847680774062953465445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380978565120516041968976963 571467847680774062953465445)
        ·
          refine ⟨107150221440145136803774771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 571467847680774062953465445 107150221440145136803774771)
          ·
            refine ⟨160725332160217705205662157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107150221440145136803774771 160725332160217705205662157)
            ·
              refine ⟨60271999560081639452123309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160725332160217705205662157 60271999560081639452123309)
              ·
                refine ⟨22601999835030614794546241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60271999560081639452123309 22601999835030614794546241)
                ·
                  refine ⟨16951499876272961095909681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22601999835030614794546241 16951499876272961095909681)
                  ·
                    refine ⟨12713624907204720821932261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16951499876272961095909681 12713624907204720821932261)
                    ·
                      refine ⟨2383804670100885154112299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12713624907204720821932261 2383804670100885154112299)
                      ·
                        rfl

theorem cell23_4642443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 4].length) (baseStart_4642443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642443 prefixEnd_4642443 := by exact prefixLift 4642443
  have htrace : WordTrace (prefixWord ++ tailWord_4642443) baseStart_4642443 baseEnd_4642443 := by
    simpa [prefixWord, tailWord_4642443, baseEnd_4642443] using wordTrace_append hprefix tailTrace_4642443
  have hstable : (prefixWord ++ tailWord_4642443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642443).length < 2 ^ (prefixWord ++ tailWord_4642443).sum := by decide
  have hdescent : baseEnd_4642443 < baseStart_4642443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642500 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_4642500 : Nat := 118140960795 + 4642500 * 2 ^ 59
def prefixEnd_4642500 : Nat := 4983230072969 + 3 ^ 40 * 4642500 * 2
def baseEnd_4642500 : Nat := 794611312832730477033179

theorem tailTrace_4642500 : CollatzResearch.WordTrace tailWord_4642500 prefixEnd_4642500 794611312832730477033179 := by
  unfold tailWord_4642500
  simp only [CollatzResearch.WordTrace]
  refine ⟨84662942840511425360518477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112883923787348567147357969 84662942840511425360518477)
  ·
    refine ⟨31748603565191784510194429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84662942840511425360518477 31748603565191784510194429)
    ·
      refine ⟨11905726336946919191322911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31748603565191784510194429 11905726336946919191322911)
      ·
        refine ⟨17858589505420378786984367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11905726336946919191322911 17858589505420378786984367)
        ·
          refine ⟨26787884258130568180476551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17858589505420378786984367 26787884258130568180476551)
          ·
            refine ⟨40181826387195852270714827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26787884258130568180476551 40181826387195852270714827)
            ·
              refine ⟨60272739580793778406072241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40181826387195852270714827 60272739580793778406072241)
              ·
                refine ⟨45204554685595333804554181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60272739580793778406072241 45204554685595333804554181)
                ·
                  refine ⟨8475854003549125088353909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45204554685595333804554181 8475854003549125088353909)
                  ·
                    refine ⟨794611312832730477033179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8475854003549125088353909 794611312832730477033179)
                    ·
                      rfl

theorem cell23_4642500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_4642500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642500 prefixEnd_4642500 := by exact prefixLift 4642500
  have htrace : WordTrace (prefixWord ++ tailWord_4642500) baseStart_4642500 baseEnd_4642500 := by
    simpa [prefixWord, tailWord_4642500, baseEnd_4642500] using wordTrace_append hprefix tailTrace_4642500
  have hstable : (prefixWord ++ tailWord_4642500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642500).length < 2 ^ (prefixWord ++ tailWord_4642500).sum := by decide
  have hdescent : baseEnd_4642500 < baseStart_4642500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642604 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 3]
def baseStart_4642604 : Nat := 118140960795 + 4642604 * 2 ^ 59
def prefixEnd_4642604 : Nat := 4983230072969 + 3 ^ 40 * 4642604 * 2
def baseEnd_4642604 : Nat := 2383887340486259024199059

theorem tailTrace_4642604 : CollatzResearch.WordTrace tailWord_4642604 prefixEnd_4642604 2383887340486259024199059 := by
  unfold tailWord_4642604
  simp only [CollatzResearch.WordTrace]
  refine ⟨84664839436323038241411433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112886452581764050988548577 84664839436323038241411433)
  ·
    refine ⟨63498629577242278681058575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84664839436323038241411433 63498629577242278681058575)
    ·
      refine ⟨95247944365863418021587863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63498629577242278681058575 95247944365863418021587863)
      ·
        refine ⟨142871916548795127032381795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95247944365863418021587863 142871916548795127032381795)
        ·
          refine ⟨214307874823192690548572693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142871916548795127032381795 214307874823192690548572693)
          ·
            refine ⟨10045681632337157369464345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 214307874823192690548572693 10045681632337157369464345)
            ·
              refine ⟨7534261224252868027098259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10045681632337157369464345 7534261224252868027098259)
              ·
                refine ⟨11301391836379302040647389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7534261224252868027098259 11301391836379302040647389)
                ·
                  refine ⟨4238021938642238265242771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11301391836379302040647389 4238021938642238265242771)
                  ·
                    refine ⟨6357032907963357397864157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4238021938642238265242771 6357032907963357397864157)
                    ·
                      refine ⟨2383887340486259024199059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6357032907963357397864157 2383887340486259024199059)
                      ·
                        rfl

theorem cell23_4642604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_4642604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642604 prefixEnd_4642604 := by exact prefixLift 4642604
  have htrace : WordTrace (prefixWord ++ tailWord_4642604) baseStart_4642604 baseEnd_4642604 := by
    simpa [prefixWord, tailWord_4642604, baseEnd_4642604] using wordTrace_append hprefix tailTrace_4642604
  have hstable : (prefixWord ++ tailWord_4642604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642604).length < 2 ^ (prefixWord ++ tailWord_4642604).sum := by decide
  have hdescent : baseEnd_4642604 < baseStart_4642604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642627 : List Nat := [1, 1, 1, 3, 1, 5, 1, 4, 1, 1, 4]
def baseStart_4642627 : Nat := 118140960795 + 4642627 * 2 ^ 59
def prefixEnd_4642627 : Nat := 4983230072969 + 3 ^ 40 * 4642627 * 2
def baseEnd_4642627 : Nat := 2383899150541312434211453

theorem tailTrace_4642627 : CollatzResearch.WordTrace tailWord_4642627 prefixEnd_4642627 2383899150541312434211453 := by
  unfold tailWord_4642627
  simp only [CollatzResearch.WordTrace]
  refine ⟨169330517751562751410910135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112887011834375167607273423 169330517751562751410910135)
  ·
    refine ⟨253995776627344127116365203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169330517751562751410910135 253995776627344127116365203)
    ·
      refine ⟨380993664941016190674547805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253995776627344127116365203 380993664941016190674547805)
      ·
        refine ⟨142872624352881071502955427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 380993664941016190674547805 142872624352881071502955427)
        ·
          refine ⟨214308936529321607254433141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142872624352881071502955427 214308936529321607254433141)
          ·
            refine ⟨20091462799623900680103107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 214308936529321607254433141 20091462799623900680103107)
            ·
              refine ⟨30137194199435851020154661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20091462799623900680103107 30137194199435851020154661)
              ·
                refine ⟨5650723912394222066278999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30137194199435851020154661 5650723912394222066278999)
                ·
                  refine ⟨8476085868591333099418499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5650723912394222066278999 8476085868591333099418499)
                  ·
                    refine ⟨12714128802886999649127749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8476085868591333099418499 12714128802886999649127749)
                    ·
                      refine ⟨2383899150541312434211453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12714128802886999649127749 2383899150541312434211453)
                      ·
                        rfl

theorem cell23_4642627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_4642627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642627 prefixEnd_4642627 := by exact prefixLift 4642627
  have htrace : WordTrace (prefixWord ++ tailWord_4642627) baseStart_4642627 baseEnd_4642627 := by
    simpa [prefixWord, tailWord_4642627, baseEnd_4642627] using wordTrace_append hprefix tailTrace_4642627
  have hstable : (prefixWord ++ tailWord_4642627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642627).length < 2 ^ (prefixWord ++ tailWord_4642627).sum := by decide
  have hdescent : baseEnd_4642627 < baseStart_4642627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642640 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 4]
def baseStart_4642640 : Nat := 118140960795 + 4642640 * 2 ^ 59
def prefixEnd_4642640 : Nat := 4983230072969 + 3 ^ 40 * 4642640 * 2
def baseEnd_4642640 : Nat := 2383905825789820883348893

theorem tailTrace_4642640 : CollatzResearch.WordTrace tailWord_4642640 prefixEnd_4642640 2383905825789820883348893 := by
  unfold tailWord_4642640
  simp only [CollatzResearch.WordTrace]
  refine ⟨84665495950257827315566687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112887327933677103087422249 84665495950257827315566687)
  ·
    refine ⟨126998243925386740973350031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84665495950257827315566687 126998243925386740973350031)
    ·
      refine ⟨190497365888080111460025047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126998243925386740973350031 190497365888080111460025047)
      ·
        refine ⟨285746048832120167190037571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190497365888080111460025047 285746048832120167190037571)
        ·
          refine ⟨428619073248180250785056357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285746048832120167190037571 428619073248180250785056357)
          ·
            refine ⟨80366076234033797022198067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 428619073248180250785056357 80366076234033797022198067)
            ·
              refine ⟨120549114351050695533297101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80366076234033797022198067 120549114351050695533297101)
              ·
                refine ⟨45205917881644010824986413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120549114351050695533297101 45205917881644010824986413)
                ·
                  refine ⟨16952219205616504059369905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45205917881644010824986413 16952219205616504059369905)
                  ·
                    refine ⟨12714164404212378044527429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16952219205616504059369905 12714164404212378044527429)
                    ·
                      refine ⟨2383905825789820883348893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12714164404212378044527429 2383905825789820883348893)
                      ·
                        rfl

theorem cell23_4642640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_4642640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642640 prefixEnd_4642640 := by exact prefixLift 4642640
  have htrace : WordTrace (prefixWord ++ tailWord_4642640) baseStart_4642640 baseEnd_4642640 := by
    simpa [prefixWord, tailWord_4642640, baseEnd_4642640] using wordTrace_append hprefix tailTrace_4642640
  have hstable : (prefixWord ++ tailWord_4642640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642640).length < 2 ^ (prefixWord ++ tailWord_4642640).sum := by decide
  have hdescent : baseEnd_4642640 < baseStart_4642640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642644 : List Nat := [2, 4, 1, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_4642644 : Nat := 118140960795 + 4642644 * 2 ^ 59
def prefixEnd_4642644 : Nat := 4983230072969 + 3 ^ 40 * 4642644 * 2
def baseEnd_4642644 : Nat := 2383907879712438867698875

theorem tailTrace_4642644 : CollatzResearch.WordTrace tailWord_4642644 prefixEnd_4642644 2383907879712438867698875 := by
  unfold tailWord_4642644
  simp only [CollatzResearch.WordTrace]
  refine ⟨84665568896250581657139493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112887425195000775542852657 84665568896250581657139493)
  ·
    refine ⟨15874794168046984060713655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84665568896250581657139493 15874794168046984060713655)
    ·
      refine ⟨23812191252070476091070483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15874794168046984060713655 23812191252070476091070483)
      ·
        refine ⟨35718286878105714136605725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23812191252070476091070483 35718286878105714136605725)
        ·
          refine ⟨13394357579289642801227147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35718286878105714136605725 13394357579289642801227147)
          ·
            refine ⟨20091536368934464201840721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13394357579289642801227147 20091536368934464201840721)
            ·
              refine ⟨15068652276700848151380541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20091536368934464201840721 15068652276700848151380541)
              ·
                refine ⟨5650744603762818056767703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15068652276700848151380541 5650744603762818056767703)
                ·
                  refine ⟨8476116905644227085151555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5650744603762818056767703 8476116905644227085151555)
                  ·
                    refine ⟨12714175358466340627727333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8476116905644227085151555 12714175358466340627727333)
                    ·
                      refine ⟨2383907879712438867698875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12714175358466340627727333 2383907879712438867698875)
                      ·
                        rfl

theorem cell23_4642644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_4642644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642644 prefixEnd_4642644 := by exact prefixLift 4642644
  have htrace : WordTrace (prefixWord ++ tailWord_4642644) baseStart_4642644 baseEnd_4642644 := by
    simpa [prefixWord, tailWord_4642644, baseEnd_4642644] using wordTrace_append hprefix tailTrace_4642644
  have hstable : (prefixWord ++ tailWord_4642644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642644).length < 2 ^ (prefixWord ++ tailWord_4642644).sum := by decide
  have hdescent : baseEnd_4642644 < baseStart_4642644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642678 : List Nat := [5, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_4642678 : Nat := 118140960795 + 4642678 * 2 ^ 59
def prefixEnd_4642678 : Nat := 4983230072969 + 3 ^ 40 * 4642678 * 2
def baseEnd_4642678 : Nat := 2383925338054691734673719

theorem tailTrace_4642678 : CollatzResearch.WordTrace tailWord_4642678 prefixEnd_4642678 2383925338054691734673719 := by
  unfold tailWord_4642678
  simp only [CollatzResearch.WordTrace]
  refine ⟨10583273617148624195063543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112888251916251991414011125 10583273617148624195063543)
  ·
    refine ⟨15874910425722936292595315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10583273617148624195063543 15874910425722936292595315)
    ·
      refine ⟨23812365638584404438892973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15874910425722936292595315 23812365638584404438892973)
      ·
        refine ⟨8929637114469151664584865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23812365638584404438892973 8929637114469151664584865)
        ·
          refine ⟨6697227835851863748438649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8929637114469151664584865 6697227835851863748438649)
          ·
            refine ⟨5022920876888897811328987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6697227835851863748438649 5022920876888897811328987)
            ·
              refine ⟨7534381315333346716993481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5022920876888897811328987 7534381315333346716993481)
              ·
                refine ⟨5650785986500010037745111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7534381315333346716993481 5650785986500010037745111)
                ·
                  refine ⟨8476178979750015056617667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5650785986500010037745111 8476178979750015056617667)
                  ·
                    refine ⟨12714268469625022584926501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8476178979750015056617667 12714268469625022584926501)
                    ·
                      refine ⟨2383925338054691734673719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12714268469625022584926501 2383925338054691734673719)
                      ·
                        rfl

theorem cell23_4642678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_4642678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642678 prefixEnd_4642678 := by exact prefixLift 4642678
  have htrace : WordTrace (prefixWord ++ tailWord_4642678) baseStart_4642678 baseEnd_4642678 := by
    simpa [prefixWord, tailWord_4642678, baseEnd_4642678] using wordTrace_append hprefix tailTrace_4642678
  have hstable : (prefixWord ++ tailWord_4642678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642678).length < 2 ^ (prefixWord ++ tailWord_4642678).sum := by decide
  have hdescent : baseEnd_4642678 < baseStart_4642678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642698 : List Nat := [3, 1, 2, 4, 2, 1, 3, 1, 1, 2, 3]
def baseStart_4642698 : Nat := 118140960795 + 4642698 * 2 ^ 59
def prefixEnd_4642698 : Nat := 4983230072969 + 3 ^ 40 * 4642698 * 2
def baseEnd_4642698 : Nat := 2383935607667781656423627

theorem tailTrace_4642698 : CollatzResearch.WordTrace tailWord_4642698 prefixEnd_4642698 2383935607667781656423627 := by
  unfold tailWord_4642698
  simp only [CollatzResearch.WordTrace]
  refine ⟨42333276833576382634186187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112888738222870353691163165 42333276833576382634186187)
  ·
    refine ⟨63499915250364573951279281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42333276833576382634186187 63499915250364573951279281)
    ·
      refine ⟨47624936437773430463459461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63499915250364573951279281 47624936437773430463459461)
      ·
        refine ⟨8929675582082518211898649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47624936437773430463459461 8929675582082518211898649)
        ·
          refine ⟨6697256686561888658923987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8929675582082518211898649 6697256686561888658923987)
          ·
            refine ⟨10045885029842832988385981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6697256686561888658923987 10045885029842832988385981)
            ·
              refine ⟨3767206886191062370644743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10045885029842832988385981 3767206886191062370644743)
              ·
                refine ⟨5650810329286593555967115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3767206886191062370644743 5650810329286593555967115)
                ·
                  refine ⟨8476215493929890333950673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5650810329286593555967115 8476215493929890333950673)
                  ·
                    refine ⟨6357161620447417750463005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8476215493929890333950673 6357161620447417750463005)
                    ·
                      refine ⟨2383935607667781656423627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6357161620447417750463005 2383935607667781656423627)
                      ·
                        rfl

theorem cell23_4642698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_4642698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642698 prefixEnd_4642698 := by exact prefixLift 4642698
  have htrace : WordTrace (prefixWord ++ tailWord_4642698) baseStart_4642698 baseEnd_4642698 := by
    simpa [prefixWord, tailWord_4642698, baseEnd_4642698] using wordTrace_append hprefix tailTrace_4642698
  have hstable : (prefixWord ++ tailWord_4642698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642698).length < 2 ^ (prefixWord ++ tailWord_4642698).sum := by decide
  have hdescent : baseEnd_4642698 < baseStart_4642698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642711 : List Nat := [1, 1, 3, 3, 1, 4, 2, 2, 2, 1, 3]
def baseStart_4642711 : Nat := 118140960795 + 4642711 * 2 ^ 59
def prefixEnd_4642711 : Nat := 4983230072969 + 3 ^ 40 * 4642711 * 2
def baseEnd_4642711 : Nat := 2383942282916290105561067

theorem tailTrace_4642711 : CollatzResearch.WordTrace tailWord_4642711 prefixEnd_4642711 2383942282916290105561067 := by
  unfold tailWord_4642711
  simp only [CollatzResearch.WordTrace]
  refine ⟨169333581483258433756967987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112889054322172289171311991 169333581483258433756967987)
  ·
    refine ⟨254000372224887650635451981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169333581483258433756967987 254000372224887650635451981)
    ·
      refine ⟨95250139584332868988294493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254000372224887650635451981 95250139584332868988294493)
      ·
        refine ⟨35718802344124825870610435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95250139584332868988294493 35718802344124825870610435)
        ·
          refine ⟨53578203516187238805915653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35718802344124825870610435 53578203516187238805915653)
          ·
            refine ⟨10045913159285107276109185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53578203516187238805915653 10045913159285107276109185)
            ·
              refine ⟨7534434869463830457081889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10045913159285107276109185 7534434869463830457081889)
              ·
                refine ⟨5650826152097872842811417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7534434869463830457081889 5650826152097872842811417)
                ·
                  refine ⟨4238119614073404632108563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5650826152097872842811417 4238119614073404632108563)
                  ·
                    refine ⟨6357179421110106948162845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4238119614073404632108563 6357179421110106948162845)
                    ·
                      refine ⟨2383942282916290105561067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6357179421110106948162845 2383942282916290105561067)
                      ·
                        rfl

theorem cell23_4642711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_4642711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642711 prefixEnd_4642711 := by exact prefixLift 4642711
  have htrace : WordTrace (prefixWord ++ tailWord_4642711) baseStart_4642711 baseEnd_4642711 := by
    simpa [prefixWord, tailWord_4642711, baseEnd_4642711] using wordTrace_append hprefix tailTrace_4642711
  have hstable : (prefixWord ++ tailWord_4642711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642711).length < 2 ^ (prefixWord ++ tailWord_4642711).sum := by decide
  have hdescent : baseEnd_4642711 < baseStart_4642711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642717 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_4642717 : Nat := 118140960795 + 4642717 * 2 ^ 59
def prefixEnd_4642717 : Nat := 4983230072969 + 3 ^ 40 * 4642717 * 2
def baseEnd_4642717 : Nat := 2383945363800217082086039

theorem tailTrace_4642717 : CollatzResearch.WordTrace tailWord_4642717 prefixEnd_4642717 2383945363800217082086039 := by
  unfold tailWord_4642717
  simp only [CollatzResearch.WordTrace]
  refine ⟨169333800321236696781686405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112889200214157797854457603 169333800321236696781686405)
  ·
    refine ⟨31750087560231880646566201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169333800321236696781686405 31750087560231880646566201)
    ·
      refine ⟨23812565670173910484924651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31750087560231880646566201 23812565670173910484924651)
      ·
        refine ⟨35718848505260865727386977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23812565670173910484924651 35718848505260865727386977)
        ·
          refine ⟨26789136378945649295540233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35718848505260865727386977 26789136378945649295540233)
          ·
            refine ⟨20091852284209236971655175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26789136378945649295540233 20091852284209236971655175)
            ·
              refine ⟨30137778426313855457482763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20091852284209236971655175 30137778426313855457482763)
              ·
                refine ⟨45206667639470783186224145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30137778426313855457482763 45206667639470783186224145)
                ·
                  refine ⟨33905000729603087389668109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45206667639470783186224145 33905000729603087389668109)
                  ·
                    refine ⟨12714375273601157771125541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33905000729603087389668109 12714375273601157771125541)
                    ·
                      refine ⟨2383945363800217082086039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12714375273601157771125541 2383945363800217082086039)
                      ·
                        rfl

theorem cell23_4642717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_4642717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642717 prefixEnd_4642717 := by exact prefixLift 4642717
  have htrace : WordTrace (prefixWord ++ tailWord_4642717) baseStart_4642717 baseEnd_4642717 := by
    simpa [prefixWord, tailWord_4642717, baseEnd_4642717] using wordTrace_append hprefix tailTrace_4642717
  have hstable : (prefixWord ++ tailWord_4642717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642717).length < 2 ^ (prefixWord ++ tailWord_4642717).sum := by decide
  have hdescent : baseEnd_4642717 < baseStart_4642717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642718 : List Nat := [4, 3, 1, 3, 2, 1, 1, 8]
def baseStart_4642718 : Nat := 118140960795 + 4642718 * 2 ^ 59
def prefixEnd_4642718 : Nat := 4983230072969 + 3 ^ 40 * 4642718 * 2
def baseEnd_4642718 : Nat := 88294291751143391784205

theorem tailTrace_4642718 : CollatzResearch.WordTrace tailWord_4642718 prefixEnd_4642718 88294291751143391784205 := by
  unfold tailWord_4642718
  simp only [CollatzResearch.WordTrace]
  refine ⟨21166729599279134244059101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112889224529488715968315205 21166729599279134244059101)
  ·
    refine ⟨7937523599729675341522163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21166729599279134244059101 7937523599729675341522163)
    ·
      refine ⟨11906285399594513012283245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7937523599729675341522163 11906285399594513012283245)
      ·
        refine ⟨4464857024847942379606217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11906285399594513012283245 4464857024847942379606217)
        ·
          refine ⟨3348642768635956784704663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4464857024847942379606217 3348642768635956784704663)
          ·
            refine ⟨5022964152953935177056995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3348642768635956784704663 5022964152953935177056995)
            ·
              refine ⟨7534446229430902765585493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5022964152953935177056995 7534446229430902765585493)
              ·
                refine ⟨88294291751143391784205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7534446229430902765585493 88294291751143391784205)
                ·
                  rfl

theorem cell23_4642718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_4642718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642718 prefixEnd_4642718 := by exact prefixLift 4642718
  have htrace : WordTrace (prefixWord ++ tailWord_4642718) baseStart_4642718 baseEnd_4642718 := by
    simpa [prefixWord, tailWord_4642718, baseEnd_4642718] using wordTrace_append hprefix tailTrace_4642718
  have hstable : (prefixWord ++ tailWord_4642718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642718).length < 2 ^ (prefixWord ++ tailWord_4642718).sum := by decide
  have hdescent : baseEnd_4642718 < baseStart_4642718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642727 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 1, 8]
def baseStart_4642727 : Nat := 118140960795 + 4642727 * 2 ^ 59
def prefixEnd_4642727 : Nat := 4983230072969 + 3 ^ 40 * 4642727 * 2
def baseEnd_4642727 : Nat := 794650166202254014320331

theorem tailTrace_4642727 : CollatzResearch.WordTrace tailWord_4642727 prefixEnd_4642727 794650166202254014320331 := by
  unfold tailWord_4642727
  simp only [CollatzResearch.WordTrace]
  refine ⟨169334165051200468489550435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112889443367466978993033623 169334165051200468489550435)
  ·
    refine ⟨254001247576800702734325653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169334165051200468489550435 254001247576800702734325653)
    ·
      refine ⟨11906308480162532940671515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 254001247576800702734325653 11906308480162532940671515)
      ·
        refine ⟨17859462720243799411007273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11906308480162532940671515 17859462720243799411007273)
        ·
          refine ⟨13394597040182849558255455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17859462720243799411007273 13394597040182849558255455)
          ·
            refine ⟨20091895560274274337383183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13394597040182849558255455 20091895560274274337383183)
            ·
              refine ⟨30137843340411411506074775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20091895560274274337383183 30137843340411411506074775)
              ·
                refine ⟨45206765010617117259112163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30137843340411411506074775 45206765010617117259112163)
                ·
                  refine ⟨67810147515925675888668245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45206765010617117259112163 67810147515925675888668245)
                  ·
                    refine ⟨794650166202254014320331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67810147515925675888668245 794650166202254014320331)
                    ·
                      rfl

theorem cell23_4642727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_4642727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642727 prefixEnd_4642727 := by exact prefixLift 4642727
  have htrace : WordTrace (prefixWord ++ tailWord_4642727) baseStart_4642727 baseEnd_4642727 := by
    simpa [prefixWord, tailWord_4642727, baseEnd_4642727] using wordTrace_append hprefix tailTrace_4642727
  have hstable : (prefixWord ++ tailWord_4642727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642727).length < 2 ^ (prefixWord ++ tailWord_4642727).sum := by decide
  have hdescent : baseEnd_4642727 < baseStart_4642727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642728 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_4642728 : Nat := 118140960795 + 4642728 * 2 ^ 59
def prefixEnd_4642728 : Nat := 4983230072969 + 3 ^ 40 * 4642728 * 2
def baseEnd_4642728 : Nat := 2383951012087416539048489

theorem tailTrace_4642728 : CollatzResearch.WordTrace tailWord_4642728 prefixEnd_4642728 2383951012087416539048489 := by
  unfold tailWord_4642728
  simp only [CollatzResearch.WordTrace]
  refine ⟨84667100762098422830168419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112889467682797897106891225 84667100762098422830168419)
  ·
    refine ⟨127000651143147634245252629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84667100762098422830168419 127000651143147634245252629)
    ·
      refine ⟨5953155522335045355246217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 127000651143147634245252629 5953155522335045355246217)
      ·
        refine ⟨4464866641751284016434663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5953155522335045355246217 4464866641751284016434663)
        ·
          refine ⟨6697299962626926024651995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4464866641751284016434663 6697299962626926024651995)
          ·
            refine ⟨10045949943940389036977993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6697299962626926024651995 10045949943940389036977993)
            ·
              refine ⟨7534462457955291777733495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10045949943940389036977993 7534462457955291777733495)
              ·
                refine ⟨11301693686932937666600243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7534462457955291777733495 11301693686932937666600243)
                ·
                  refine ⟨16952540530399406499900365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11301693686932937666600243 16952540530399406499900365)
                  ·
                    refine ⟨6357202698899777437462637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16952540530399406499900365 6357202698899777437462637)
                    ·
                      refine ⟨2383951012087416539048489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6357202698899777437462637 2383951012087416539048489)
                      ·
                        rfl

theorem cell23_4642728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_4642728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642728 prefixEnd_4642728 := by exact prefixLift 4642728
  have htrace : WordTrace (prefixWord ++ tailWord_4642728) baseStart_4642728 baseEnd_4642728 := by
    simpa [prefixWord, tailWord_4642728, baseEnd_4642728] using wordTrace_append hprefix tailTrace_4642728
  have hstable : (prefixWord ++ tailWord_4642728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642728).length < 2 ^ (prefixWord ++ tailWord_4642728).sum := by decide
  have hdescent : baseEnd_4642728 < baseStart_4642728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642767 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 3]
def baseStart_4642767 : Nat := 118140960795 + 4642767 * 2 ^ 59
def prefixEnd_4642767 : Nat := 4983230072969 + 3 ^ 40 * 4642767 * 2
def baseEnd_4642767 : Nat := 2383971037832941886460809

theorem tailTrace_4642767 : CollatzResearch.WordTrace tailWord_4642767 prefixEnd_4642767 2383971037832941886460809 := by
  unfold tailWord_4642767
  simp only [CollatzResearch.WordTrace]
  refine ⟨169335623971055555321006555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112890415980703703547337703 169335623971055555321006555)
  ·
    refine ⟨254003435956583332981509833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169335623971055555321006555 254003435956583332981509833)
    ·
      refine ⟨190502576967437499736132375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254003435956583332981509833 190502576967437499736132375)
      ·
        refine ⟨285753865451156249604198563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190502576967437499736132375 285753865451156249604198563)
        ·
          refine ⟨428630798176734374406297845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285753865451156249604198563 428630798176734374406297845)
          ·
            refine ⟨40184137329068847600590423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 428630798176734374406297845 40184137329068847600590423)
            ·
              refine ⟨60276205993603271400885635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40184137329068847600590423 60276205993603271400885635)
              ·
                refine ⟨90414308990404907101328453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60276205993603271400885635 90414308990404907101328453)
                ·
                  refine ⟨16952682935700920081499085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90414308990404907101328453 16952682935700920081499085)
                  ·
                    refine ⟨6357256100887845030562157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16952682935700920081499085 6357256100887845030562157)
                    ·
                      refine ⟨2383971037832941886460809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6357256100887845030562157 2383971037832941886460809)
                      ·
                        rfl

theorem cell23_4642767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 3].length) (baseStart_4642767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642767 prefixEnd_4642767 := by exact prefixLift 4642767
  have htrace : WordTrace (prefixWord ++ tailWord_4642767) baseStart_4642767 baseEnd_4642767 := by
    simpa [prefixWord, tailWord_4642767, baseEnd_4642767] using wordTrace_append hprefix tailTrace_4642767
  have hstable : (prefixWord ++ tailWord_4642767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642767).length < 2 ^ (prefixWord ++ tailWord_4642767).sum := by decide
  have hdescent : baseEnd_4642767 < baseStart_4642767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642787 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 1, 7]
def baseStart_4642787 : Nat := 118140960795 + 4642787 * 2 ^ 59
def prefixEnd_4642787 : Nat := 4983230072969 + 3 ^ 40 * 4642787 * 2
def baseEnd_4642787 : Nat := 794660435815343936070239

theorem tailTrace_4642787 : CollatzResearch.WordTrace tailWord_4642787 prefixEnd_4642787 794660435815343936070239 := by
  unfold tailWord_4642787
  simp only [CollatzResearch.WordTrace]
  refine ⟨169336353430983098736734615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112890902287322065824489743 169336353430983098736734615)
  ·
    refine ⟨254004530146474648105101923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169336353430983098736734615 254004530146474648105101923)
    ·
      refine ⟨381006795219711972157652885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254004530146474648105101923 381006795219711972157652885)
      ·
        refine ⟨17859693525923998694889979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 381006795219711972157652885 17859693525923998694889979)
        ·
          refine ⟨26789540288885998042334969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17859693525923998694889979 26789540288885998042334969)
          ·
            refine ⟨20092155216664498531751227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26789540288885998042334969 20092155216664498531751227)
            ·
              refine ⟨30138232824996747797626841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20092155216664498531751227 30138232824996747797626841)
              ·
                refine ⟨22603674618747560848220131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30138232824996747797626841 22603674618747560848220131)
                ·
                  refine ⟨33905511928121341272330197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22603674618747560848220131 33905511928121341272330197)
                  ·
                    refine ⟨794660435815343936070239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33905511928121341272330197 794660435815343936070239)
                    ·
                      rfl

theorem cell23_4642787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 7].length) (baseStart_4642787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642787 prefixEnd_4642787 := by exact prefixLift 4642787
  have htrace : WordTrace (prefixWord ++ tailWord_4642787) baseStart_4642787 baseEnd_4642787 := by
    simpa [prefixWord, tailWord_4642787, baseEnd_4642787] using wordTrace_append hprefix tailTrace_4642787
  have hstable : (prefixWord ++ tailWord_4642787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642787).length < 2 ^ (prefixWord ++ tailWord_4642787).sum := by decide
  have hdescent : baseEnd_4642787 < baseStart_4642787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642807 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_4642807 : Nat := 118140960795 + 4642807 * 2 ^ 59
def prefixEnd_4642807 : Nat := 4983230072969 + 3 ^ 40 * 4642807 * 2
def baseEnd_4642807 : Nat := 2383991577059121729960625

theorem tailTrace_4642807 : CollatzResearch.WordTrace tailWord_4642807 prefixEnd_4642807 2383991577059121729960625 := by
  unfold tailWord_4642807
  simp only [CollatzResearch.WordTrace]
  refine ⟨169337082890910642152462675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112891388593940428101641783 169337082890910642152462675)
  ·
    refine ⟨254005624336365963228694013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169337082890910642152462675 254005624336365963228694013)
    ·
      refine ⟨95252109126137236210760255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254005624336365963228694013 95252109126137236210760255)
      ·
        refine ⟨142878163689205854316140383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95252109126137236210760255 142878163689205854316140383)
        ·
          refine ⟨214317245533808781474210575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142878163689205854316140383 214317245533808781474210575)
          ·
            refine ⟨321475868300713172211315863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214317245533808781474210575 321475868300713172211315863)
            ·
              refine ⟨482213802451069758316973795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321475868300713172211315863 482213802451069758316973795)
              ·
                refine ⟨723320703676604637475460693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482213802451069758316973795 723320703676604637475460693)
                ·
                  refine ⟨8476414496210210595415555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 723320703676604637475460693 8476414496210210595415555)
                  ·
                    refine ⟨12714621744315315893123333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8476414496210210595415555 12714621744315315893123333)
                    ·
                      refine ⟨2383991577059121729960625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12714621744315315893123333 2383991577059121729960625)
                      ·
                        rfl

theorem cell23_4642807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_4642807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642807 prefixEnd_4642807 := by exact prefixLift 4642807
  have htrace : WordTrace (prefixWord ++ tailWord_4642807) baseStart_4642807 baseEnd_4642807 := by
    simpa [prefixWord, tailWord_4642807, baseEnd_4642807] using wordTrace_append hprefix tailTrace_4642807
  have hstable : (prefixWord ++ tailWord_4642807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642807).length < 2 ^ (prefixWord ++ tailWord_4642807).sum := by decide
  have hdescent : baseEnd_4642807 < baseStart_4642807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642824 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_4642824 : Nat := 118140960795 + 4642824 * 2 ^ 59
def prefixEnd_4642824 : Nat := 4983230072969 + 3 ^ 40 * 4642824 * 2
def baseEnd_4642824 : Nat := 2384000306230248163448047

theorem tailTrace_4642824 : CollatzResearch.WordTrace tailWord_4642824 prefixEnd_4642824 2384000306230248163448047 := by
  unfold tailWord_4642824
  simp only [CollatzResearch.WordTrace]
  refine ⟨84668851465924527027915763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112891801954566036037221017 84668851465924527027915763)
  ·
    refine ⟨127003277198886790541873645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84668851465924527027915763 127003277198886790541873645)
    ·
      refine ⟨47626228949582546453202617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127003277198886790541873645 47626228949582546453202617)
      ·
        refine ⟨35719671712186909839901963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47626228949582546453202617 35719671712186909839901963)
        ·
          refine ⟨53579507568280364759852945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35719671712186909839901963 53579507568280364759852945)
          ·
            refine ⟨40184630676210273569889709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53579507568280364759852945 40184630676210273569889709)
            ·
              refine ⟨15069236503578852588708641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40184630676210273569889709 15069236503578852588708641)
              ·
                refine ⟨11301927377684139441531481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15069236503578852588708641 11301927377684139441531481)
                ·
                  refine ⟨8476445533263104581148611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11301927377684139441531481 8476445533263104581148611)
                  ·
                    refine ⟨12714668299894656871722917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8476445533263104581148611 12714668299894656871722917)
                    ·
                      refine ⟨2384000306230248163448047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12714668299894656871722917 2384000306230248163448047)
                      ·
                        rfl

theorem cell23_4642824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_4642824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642824 prefixEnd_4642824 := by exact prefixLift 4642824
  have htrace : WordTrace (prefixWord ++ tailWord_4642824) baseStart_4642824 baseEnd_4642824 := by
    simpa [prefixWord, tailWord_4642824, baseEnd_4642824] using wordTrace_append hprefix tailTrace_4642824
  have hstable : (prefixWord ++ tailWord_4642824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642824).length < 2 ^ (prefixWord ++ tailWord_4642824).sum := by decide
  have hdescent : baseEnd_4642824 < baseStart_4642824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
