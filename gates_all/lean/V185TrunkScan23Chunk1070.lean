import V185TrunkScan23Chunk1069

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6334115 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 6]
def baseStart_6334115 : Nat := 118140960795 + 6334115 * 2 ^ 59
def prefixEnd_6334115 : Nat := 4983230072969 + 3 ^ 40 * 6334115 * 2
def baseEnd_6334115 : Nat := 3252445515853590479632441

theorem tailTrace_6334115 : CollatzResearch.WordTrace tailWord_6334115 prefixEnd_6334115 3252445515853590479632441 := by
  unfold tailWord_6334115
  simp only [CollatzResearch.WordTrace]
  refine ⟨231024153447590610562147799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154016102298393740374765199 231024153447590610562147799)
  ·
    refine ⟨346536230171385915843221699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231024153447590610562147799 346536230171385915843221699)
    ·
      refine ⟨519804345257078873764832549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346536230171385915843221699 519804345257078873764832549)
      ·
        refine ⟨97463314735702288830906103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 519804345257078873764832549 97463314735702288830906103)
        ·
          refine ⟨146194972103553433246359155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97463314735702288830906103 146194972103553433246359155)
          ·
            refine ⟨219292458155330149869538733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146194972103553433246359155 219292458155330149869538733)
            ·
              refine ⟨82234671808248806201077025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219292458155330149869538733 82234671808248806201077025)
              ·
                refine ⟨61676003856186604650807769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82234671808248806201077025 61676003856186604650807769)
                ·
                  refine ⟨46257002892139953488105827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61676003856186604650807769 46257002892139953488105827)
                  ·
                    refine ⟨69385504338209930232158741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46257002892139953488105827 69385504338209930232158741)
                    ·
                      refine ⟨3252445515853590479632441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69385504338209930232158741 3252445515853590479632441)
                      ·
                        rfl

theorem cell23_6334115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_6334115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334115 prefixEnd_6334115 := by exact prefixLift 6334115
  have htrace : WordTrace (prefixWord ++ tailWord_6334115) baseStart_6334115 baseEnd_6334115 := by
    simpa [prefixWord, tailWord_6334115, baseEnd_6334115] using wordTrace_append hprefix tailTrace_6334115
  have hstable : (prefixWord ++ tailWord_6334115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334115).length < 2 ^ (prefixWord ++ tailWord_6334115).sum := by decide
  have hdescent : baseEnd_6334115 < baseStart_6334115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334142 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 8]
def baseStart_6334142 : Nat := 118140960795 + 6334142 * 2 ^ 59
def prefixEnd_6334142 : Nat := 4983230072969 + 3 ^ 40 * 6334142 * 2
def baseEnd_6334142 : Nat := 361384375536806874888313

theorem tailTrace_6334142 : CollatzResearch.WordTrace tailWord_6334142 prefixEnd_6334142 361384375536806874888313 := by
  unfold tailWord_6334142
  simp only [CollatzResearch.WordTrace]
  refine ⟨28878142277311599271672585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154016758812328529448920453 28878142277311599271672585)
  ·
    refine ⟨21658606707983699453754439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28878142277311599271672585 21658606707983699453754439)
    ·
      refine ⟨32487910061975549180631659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21658606707983699453754439 32487910061975549180631659)
      ·
        refine ⟨48731865092963323770947489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32487910061975549180631659 48731865092963323770947489)
        ·
          refine ⟨36548898819722492828210617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48731865092963323770947489 36548898819722492828210617)
          ·
            refine ⟨27411674114791869621157963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36548898819722492828210617 27411674114791869621157963)
            ·
              refine ⟨41117511172187804431736945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27411674114791869621157963 41117511172187804431736945)
              ·
                refine ⟨30838133379140853323802709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41117511172187804431736945 30838133379140853323802709)
                ·
                  refine ⟨361384375536806874888313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30838133379140853323802709 361384375536806874888313)
                  ·
                    rfl

theorem cell23_6334142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_6334142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334142 prefixEnd_6334142 := by exact prefixLift 6334142
  have htrace : WordTrace (prefixWord ++ tailWord_6334142) baseStart_6334142 baseEnd_6334142 := by
    simpa [prefixWord, tailWord_6334142, baseEnd_6334142] using wordTrace_append hprefix tailTrace_6334142
  have hstable : (prefixWord ++ tailWord_6334142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334142).length < 2 ^ (prefixWord ++ tailWord_6334142).sum := by decide
  have hdescent : baseEnd_6334142 < baseStart_6334142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334156 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 2, 2, 3]
def baseStart_6334156 : Nat := 118140960795 + 6334156 * 2 ^ 59
def prefixEnd_6334156 : Nat := 4983230072969 + 3 ^ 40 * 6334156 * 2
def baseEnd_6334156 : Nat := 3252466568560424819219753

theorem tailTrace_6334156 : CollatzResearch.WordTrace tailWord_6334156 prefixEnd_6334156 3252466568560424819219753 := by
  unfold tailWord_6334156
  simp only [CollatzResearch.WordTrace]
  refine ⟨115512824420221037282195161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154017099226961383042926881 115512824420221037282195161)
  ·
    refine ⟨86634618315165777961646371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115512824420221037282195161 86634618315165777961646371)
    ·
      refine ⟨129951927472748666942469557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86634618315165777961646371 129951927472748666942469557)
      ·
        refine ⟨12182993200570187525856521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129951927472748666942469557 12182993200570187525856521)
        ·
          refine ⟨9137244900427640644392391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12182993200570187525856521 9137244900427640644392391)
          ·
            refine ⟨13705867350641460966588587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9137244900427640644392391 13705867350641460966588587)
            ·
              refine ⟨20558801025962191449882881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13705867350641460966588587 20558801025962191449882881)
              ·
                refine ⟨15419100769471643587412161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20558801025962191449882881 15419100769471643587412161)
                ·
                  refine ⟨11564325577103732690559121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15419100769471643587412161 11564325577103732690559121)
                  ·
                    refine ⟨8673244182827799517919341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11564325577103732690559121 8673244182827799517919341)
                    ·
                      refine ⟨3252466568560424819219753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8673244182827799517919341 3252466568560424819219753)
                      ·
                        rfl

theorem cell23_6334156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_6334156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334156 prefixEnd_6334156 := by exact prefixLift 6334156
  have htrace : WordTrace (prefixWord ++ tailWord_6334156) baseStart_6334156 baseEnd_6334156 := by
    simpa [prefixWord, tailWord_6334156, baseEnd_6334156] using wordTrace_append hprefix tailTrace_6334156
  have hstable : (prefixWord ++ tailWord_6334156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334156).length < 2 ^ (prefixWord ++ tailWord_6334156).sum := by decide
  have hdescent : baseEnd_6334156 < baseStart_6334156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334189 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_6334189 : Nat := 118140960795 + 6334189 * 2 ^ 59
def prefixEnd_6334189 : Nat := 4983230072969 + 3 ^ 40 * 6334189 * 2
def baseEnd_6334189 : Nat := 1084161171140674396702367

theorem tailTrace_6334189 : CollatzResearch.WordTrace tailWord_6334189 prefixEnd_6334189 1084161171140674396702367 := by
  unfold tailWord_6334189
  simp only [CollatzResearch.WordTrace]
  refine ⟨231026852449322521200341621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154017901632881680800227747 231026852449322521200341621)
  ·
    refine ⟨21658767417123986362532027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231026852449322521200341621 21658767417123986362532027)
    ·
      refine ⟨32488151125685979543798041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21658767417123986362532027 32488151125685979543798041)
      ·
        refine ⟨24366113344264484657848531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32488151125685979543798041 24366113344264484657848531)
        ·
          refine ⟨36549170016396726986772797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24366113344264484657848531 36549170016396726986772797)
          ·
            refine ⟨13705938756148772620039799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36549170016396726986772797 13705938756148772620039799)
            ·
              refine ⟨20558908134223158930059699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13705938756148772620039799 20558908134223158930059699)
              ·
                refine ⟨30838362201334738395089549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20558908134223158930059699 30838362201334738395089549)
                ·
                  refine ⟨11564385825500526898158581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30838362201334738395089549 11564385825500526898158581)
                  ·
                    refine ⟨1084161171140674396702367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11564385825500526898158581 1084161171140674396702367)
                    ·
                      rfl

theorem cell23_6334189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_6334189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334189 prefixEnd_6334189 := by exact prefixLift 6334189
  have htrace : WordTrace (prefixWord ++ tailWord_6334189) baseStart_6334189 baseEnd_6334189 := by
    simpa [prefixWord, tailWord_6334189, baseEnd_6334189] using wordTrace_append hprefix tailTrace_6334189
  have hstable : (prefixWord ++ tailWord_6334189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334189).length < 2 ^ (prefixWord ++ tailWord_6334189).sum := by decide
  have hdescent : baseEnd_6334189 < baseStart_6334189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334209 : List Nat := [1, 2, 4, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_6334209 : Nat := 118140960795 + 6334209 * 2 ^ 59
def prefixEnd_6334209 : Nat := 4983230072969 + 3 ^ 40 * 6334209 * 2
def baseEnd_6334209 : Nat := 3252493783035113111857009

theorem tailTrace_6334209 : CollatzResearch.WordTrace tailWord_6334209 prefixEnd_6334209 3252493783035113111857009 := by
  unfold tailWord_6334209
  simp only [CollatzResearch.WordTrace]
  refine ⟨231027581909250064616069681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154018387939500043077379787 231027581909250064616069681)
  ·
    refine ⟨173270686431937548462052261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231027581909250064616069681 173270686431937548462052261)
    ·
      refine ⟨32488253705988290336634799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173270686431937548462052261 32488253705988290336634799)
      ·
        refine ⟨48732380558982435504952199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32488253705988290336634799 48732380558982435504952199)
        ·
          refine ⟨73098570838473653257428299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48732380558982435504952199 73098570838473653257428299)
          ·
            refine ⟨109647856257710479886142449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73098570838473653257428299 109647856257710479886142449)
            ·
              refine ⟨82235892193282859914606837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109647856257710479886142449 82235892193282859914606837)
              ·
                refine ⟨7709614893120268116994391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82235892193282859914606837 7709614893120268116994391)
                ·
                  refine ⟨11564422339680402175491587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7709614893120268116994391 11564422339680402175491587)
                  ·
                    refine ⟨17346633509520603263237381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11564422339680402175491587 17346633509520603263237381)
                    ·
                      refine ⟨3252493783035113111857009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17346633509520603263237381 3252493783035113111857009)
                      ·
                        rfl

theorem cell23_6334209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_6334209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334209 prefixEnd_6334209 := by exact prefixLift 6334209
  have htrace : WordTrace (prefixWord ++ tailWord_6334209) baseStart_6334209 baseEnd_6334209 := by
    simpa [prefixWord, tailWord_6334209, baseEnd_6334209] using wordTrace_append hprefix tailTrace_6334209
  have hstable : (prefixWord ++ tailWord_6334209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334209).length < 2 ^ (prefixWord ++ tailWord_6334209).sum := by decide
  have hdescent : baseEnd_6334209 < baseStart_6334209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334219 : List Nat := [1, 1, 1, 1, 5, 1, 3, 4, 2, 4]
def baseStart_6334219 : Nat := 118140960795 + 6334219 * 2 ^ 59
def prefixEnd_6334219 : Nat := 4983230072969 + 3 ^ 40 * 6334219 * 2
def baseEnd_6334219 : Nat := 1084166305947219357577321

theorem tailTrace_6334219 : CollatzResearch.WordTrace tailWord_6334219 prefixEnd_6334219 1084166305947219357577321 := by
  unfold tailWord_6334219
  simp only [CollatzResearch.WordTrace]
  refine ⟨231027946639213836323933711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154018631092809224215955807 231027946639213836323933711)
  ·
    refine ⟨346541919958820754485900567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231027946639213836323933711 346541919958820754485900567)
    ·
      refine ⟨519812879938231131728850851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346541919958820754485900567 519812879938231131728850851)
      ·
        refine ⟨779719319907346697593276277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519812879938231131728850851 779719319907346697593276277)
        ·
          refine ⟨73098686241313752899369651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 779719319907346697593276277 73098686241313752899369651)
          ·
            refine ⟨109648029361970629349054477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73098686241313752899369651 109648029361970629349054477)
            ·
              refine ⟨41118011010738986005895429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109648029361970629349054477 41118011010738986005895429)
              ·
                refine ⟨7709627064513559876105393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41118011010738986005895429 7709627064513559876105393)
                ·
                  refine ⟨5782220298385169907079045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7709627064513559876105393 5782220298385169907079045)
                  ·
                    refine ⟨1084166305947219357577321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5782220298385169907079045 1084166305947219357577321)
                    ·
                      rfl

theorem cell23_6334219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 4].length) (baseStart_6334219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334219 prefixEnd_6334219 := by exact prefixLift 6334219
  have htrace : WordTrace (prefixWord ++ tailWord_6334219) baseStart_6334219 baseEnd_6334219 := by
    simpa [prefixWord, tailWord_6334219, baseEnd_6334219] using wordTrace_append hprefix tailTrace_6334219
  have hstable : (prefixWord ++ tailWord_6334219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334219).length < 2 ^ (prefixWord ++ tailWord_6334219).sum := by decide
  have hdescent : baseEnd_6334219 < baseStart_6334219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334222 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_6334222 : Nat := 118140960795 + 6334222 * 2 ^ 59
def prefixEnd_6334222 : Nat := 4983230072969 + 3 ^ 40 * 6334222 * 2
def baseEnd_6334222 : Nat := 3252500458283621560994449

theorem tailTrace_6334222 : CollatzResearch.WordTrace tailWord_6334222 prefixEnd_6334222 3252500458283621560994449 := by
  unfold tailWord_6334222
  simp only [CollatzResearch.WordTrace]
  refine ⟨28878507007275370979536615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154018704038801978557528613 28878507007275370979536615)
  ·
    refine ⟨43317760510913056469304923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28878507007275370979536615 43317760510913056469304923)
    ·
      refine ⟨64976640766369584703957385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43317760510913056469304923 64976640766369584703957385)
      ·
        refine ⟨48732480574777188527968039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64976640766369584703957385 48732480574777188527968039)
        ·
          refine ⟨73098720862165782791952059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48732480574777188527968039 73098720862165782791952059)
          ·
            refine ⟨109648081293248674187928089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73098720862165782791952059 109648081293248674187928089)
            ·
              refine ⟨82236060969936505640946067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109648081293248674187928089 82236060969936505640946067)
              ·
                refine ⟨123354091454904758461419101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82236060969936505640946067 123354091454904758461419101)
                ·
                  refine ⟨46257784295589284423032163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123354091454904758461419101 46257784295589284423032163)
                  ·
                    refine ⟨69386676443383926634548245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46257784295589284423032163 69386676443383926634548245)
                    ·
                      refine ⟨3252500458283621560994449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69386676443383926634548245 3252500458283621560994449)
                      ·
                        rfl

theorem cell23_6334222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_6334222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334222 prefixEnd_6334222 := by exact prefixLift 6334222
  have htrace : WordTrace (prefixWord ++ tailWord_6334222) baseStart_6334222 baseEnd_6334222 := by
    simpa [prefixWord, tailWord_6334222, baseEnd_6334222] using wordTrace_append hprefix tailTrace_6334222
  have hstable : (prefixWord ++ tailWord_6334222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334222).length < 2 ^ (prefixWord ++ tailWord_6334222).sum := by decide
  have hdescent : baseEnd_6334222 < baseStart_6334222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334226 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_6334226 : Nat := 118140960795 + 6334226 * 2 ^ 59
def prefixEnd_6334226 : Nat := 4983230072969 + 3 ^ 40 * 6334226 * 2
def baseEnd_6334226 : Nat := 3252502512206239545344431

theorem tailTrace_6334226 : CollatzResearch.WordTrace tailWord_6334226 prefixEnd_6334226 3252502512206239545344431 := by
  unfold tailWord_6334226
  simp only [CollatzResearch.WordTrace]
  refine ⟨57757050487547119129859633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154018801300125651012959021 57757050487547119129859633)
  ·
    refine ⟨43317787865660339347394725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57757050487547119129859633 43317787865660339347394725)
    ·
      refine ⟨8122085224811313627636511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43317787865660339347394725 8122085224811313627636511)
      ·
        refine ⟨12183127837216970441454767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8122085224811313627636511 12183127837216970441454767)
        ·
          refine ⟨18274691755825455662182151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12183127837216970441454767 18274691755825455662182151)
          ·
            refine ⟨27412037633738183493273227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18274691755825455662182151 27412037633738183493273227)
            ·
              refine ⟨41118056450607275239909841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27412037633738183493273227 41118056450607275239909841)
              ·
                refine ⟨30838542337955456429932381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41118056450607275239909841 30838542337955456429932381)
                ·
                  refine ⟨11564453376733296161224643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30838542337955456429932381 11564453376733296161224643)
                  ·
                    refine ⟨17346680065099944241836965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11564453376733296161224643 17346680065099944241836965)
                    ·
                      refine ⟨3252502512206239545344431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17346680065099944241836965 3252502512206239545344431)
                      ·
                        rfl

theorem cell23_6334226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_6334226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334226 prefixEnd_6334226 := by exact prefixLift 6334226
  have htrace : WordTrace (prefixWord ++ tailWord_6334226) baseStart_6334226 baseEnd_6334226 := by
    simpa [prefixWord, tailWord_6334226, baseEnd_6334226] using wordTrace_append hprefix tailTrace_6334226
  have hstable : (prefixWord ++ tailWord_6334226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334226).length < 2 ^ (prefixWord ++ tailWord_6334226).sum := by decide
  have hdescent : baseEnd_6334226 < baseStart_6334226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334229 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_6334229 : Nat := 118140960795 + 6334229 * 2 ^ 59
def prefixEnd_6334229 : Nat := 4983230072969 + 3 ^ 40 * 6334229 * 2
def baseEnd_6334229 : Nat := 3252504052648203033606917

theorem tailTrace_6334229 : CollatzResearch.WordTrace tailWord_6334229 prefixEnd_6334229 3252504052648203033606917 := by
  unfold tailWord_6334229
  simp only [CollatzResearch.WordTrace]
  refine ⟨231028311369177608031797741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154018874246118405354531827 231028311369177608031797741)
  ·
    refine ⟨86635616763441603011924153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231028311369177608031797741 86635616763441603011924153)
    ·
      refine ⟨64976712572581202258943115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86635616763441603011924153 64976712572581202258943115)
      ·
        refine ⟨97465068858871803388414673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64976712572581202258943115 97465068858871803388414673)
        ·
          refine ⟨73098801644153852541311005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97465068858871803388414673 73098801644153852541311005)
          ·
            refine ⟨27412050616557694702991627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73098801644153852541311005 27412050616557694702991627)
            ·
              refine ⟨41118075924836542054487441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27412050616557694702991627 41118075924836542054487441)
              ·
                refine ⟨30838556943627406540865581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41118075924836542054487441 30838556943627406540865581)
                ·
                  refine ⟨11564458853860277452824593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30838556943627406540865581 11564458853860277452824593)
                  ·
                    refine ⟨8673344140395208089618445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11564458853860277452824593 8673344140395208089618445)
                    ·
                      refine ⟨3252504052648203033606917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8673344140395208089618445 3252504052648203033606917)
                      ·
                        rfl

theorem cell23_6334229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_6334229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334229 prefixEnd_6334229 := by exact prefixLift 6334229
  have htrace : WordTrace (prefixWord ++ tailWord_6334229) baseStart_6334229 baseEnd_6334229 := by
    simpa [prefixWord, tailWord_6334229, baseEnd_6334229] using wordTrace_append hprefix tailTrace_6334229
  have hstable : (prefixWord ++ tailWord_6334229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334229).length < 2 ^ (prefixWord ++ tailWord_6334229).sum := by decide
  have hdescent : baseEnd_6334229 < baseStart_6334229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334232 : List Nat := [2, 1, 2, 3, 1, 1, 5, 8]
def baseStart_6334232 : Nat := 118140960795 + 6334232 * 2 ^ 59
def prefixEnd_6334232 : Nat := 4983230072969 + 3 ^ 40 * 6334232 * 2
def baseEnd_6334232 : Nat := 120463170114450611921089

theorem tailTrace_6334232 : CollatzResearch.WordTrace tailWord_6334232 prefixEnd_6334232 120463170114450611921089 := by
  unfold tailWord_6334232
  simp only [CollatzResearch.WordTrace]
  refine ⟨115514210394083369772078475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154018947192111159696104633 115514210394083369772078475)
  ·
    refine ⟨173271315591125054658117713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115514210394083369772078475 173271315591125054658117713)
    ·
      refine ⟨129953486693343790993588285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173271315591125054658117713 129953486693343790993588285)
      ·
        refine ⟨48732557510003921622595607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129953486693343790993588285 48732557510003921622595607)
        ·
          refine ⟨73098836265005882433893411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48732557510003921622595607 73098836265005882433893411)
          ·
            refine ⟨109648254397508823650840117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73098836265005882433893411 109648254397508823650840117)
            ·
              refine ⟨10279523849766452217266261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109648254397508823650840117 10279523849766452217266261)
              ·
                refine ⟨120463170114450611921089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10279523849766452217266261 120463170114450611921089)
                ·
                  rfl

theorem cell23_6334232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 8].length) (baseStart_6334232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334232 prefixEnd_6334232 := by exact prefixLift 6334232
  have htrace : WordTrace (prefixWord ++ tailWord_6334232) baseStart_6334232 baseEnd_6334232 := by
    simpa [prefixWord, tailWord_6334232, baseEnd_6334232] using wordTrace_append hprefix tailTrace_6334232
  have hstable : (prefixWord ++ tailWord_6334232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334232).length < 2 ^ (prefixWord ++ tailWord_6334232).sum := by decide
  have hdescent : baseEnd_6334232 < baseStart_6334232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334239 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 4]
def baseStart_6334239 : Nat := 118140960795 + 6334239 * 2 ^ 59
def prefixEnd_6334239 : Nat := 4983230072969 + 3 ^ 40 * 6334239 * 2
def baseEnd_6334239 : Nat := 3252509187454747994481871

theorem tailTrace_6334239 : CollatzResearch.WordTrace tailWord_6334239 prefixEnd_6334239 3252509187454747994481871 := by
  unfold tailWord_6334239
  simp only [CollatzResearch.WordTrace]
  refine ⟨231028676099141379739661771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154019117399427586493107847 231028676099141379739661771)
  ·
    refine ⟨346543014148712069609492657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231028676099141379739661771 346543014148712069609492657)
    ·
      refine ⟨259907260611534052207119493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346543014148712069609492657 259907260611534052207119493)
      ·
        refine ⟨48732611364662634788834905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259907260611534052207119493 48732611364662634788834905)
        ·
          refine ⟨36549458523496976091626179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48732611364662634788834905 36549458523496976091626179)
          ·
            refine ⟨54824187785245464137439269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36549458523496976091626179 54824187785245464137439269)
            ·
              refine ⟨10279535209733524525769863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54824187785245464137439269 10279535209733524525769863)
              ·
                refine ⟨15419302814600286788654795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10279535209733524525769863 15419302814600286788654795)
                ·
                  refine ⟨23128954221900430182982193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15419302814600286788654795 23128954221900430182982193)
                  ·
                    refine ⟨17346715666425322637236645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23128954221900430182982193 17346715666425322637236645)
                    ·
                      refine ⟨3252509187454747994481871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17346715666425322637236645 3252509187454747994481871)
                      ·
                        rfl

theorem cell23_6334239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_6334239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334239 prefixEnd_6334239 := by exact prefixLift 6334239
  have htrace : WordTrace (prefixWord ++ tailWord_6334239) baseStart_6334239 baseEnd_6334239 := by
    simpa [prefixWord, tailWord_6334239, baseEnd_6334239] using wordTrace_append hprefix tailTrace_6334239
  have hstable : (prefixWord ++ tailWord_6334239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334239).length < 2 ^ (prefixWord ++ tailWord_6334239).sum := by decide
  have hdescent : baseEnd_6334239 < baseStart_6334239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334260 : List Nat := [2, 5, 1, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_6334260 : Nat := 118140960795 + 6334260 * 2 ^ 59
def prefixEnd_6334260 : Nat := 4983230072969 + 3 ^ 40 * 6334260 * 2
def baseEnd_6334260 : Nat := 3252519970548492412319275

theorem tailTrace_6334260 : CollatzResearch.WordTrace tailWord_6334260 prefixEnd_6334260 3252519970548492412319275 := by
  unfold tailWord_6334260
  simp only [CollatzResearch.WordTrace]
  refine ⟨115514721016032650163088117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154019628021376866884117489 115514721016032650163088117)
  ·
    refine ⟨10829505095253060952789511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115514721016032650163088117 10829505095253060952789511)
    ·
      refine ⟨16244257642879591429184267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10829505095253060952789511 16244257642879591429184267)
      ·
        refine ⟨24366386464319387143776401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16244257642879591429184267 24366386464319387143776401)
        ·
          refine ⟨18274789848239540357832301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24366386464319387143776401 18274789848239540357832301)
          ·
            refine ⟨6853046193089827634187113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18274789848239540357832301 6853046193089827634187113)
            ·
              refine ⟨5139784644817370725640335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6853046193089827634187113 5139784644817370725640335)
              ·
                refine ⟨7709676967226056088460503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5139784644817370725640335 7709676967226056088460503)
                ·
                  refine ⟨11564515450839084132690755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7709676967226056088460503 11564515450839084132690755)
                  ·
                    refine ⟨17346773176258626199036133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11564515450839084132690755 17346773176258626199036133)
                    ·
                      refine ⟨3252519970548492412319275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17346773176258626199036133 3252519970548492412319275)
                      ·
                        rfl

theorem cell23_6334260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_6334260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334260 prefixEnd_6334260 := by exact prefixLift 6334260
  have htrace : WordTrace (prefixWord ++ tailWord_6334260) baseStart_6334260 baseEnd_6334260 := by
    simpa [prefixWord, tailWord_6334260, baseEnd_6334260] using wordTrace_append hprefix tailTrace_6334260
  have hstable : (prefixWord ++ tailWord_6334260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334260).length < 2 ^ (prefixWord ++ tailWord_6334260).sum := by decide
  have hdescent : baseEnd_6334260 < baseStart_6334260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334303 : List Nat := [1, 1, 2, 3, 1, 5, 2, 2, 1, 3, 2]
def baseStart_6334303 : Nat := 118140960795 + 6334303 * 2 ^ 59
def prefixEnd_6334303 : Nat := 4983230072969 + 3 ^ 40 * 6334303 * 2
def baseEnd_6334303 : Nat := 3252542050216635744081577

theorem tailTrace_6334303 : CollatzResearch.WordTrace tailWord_6334303 prefixEnd_6334303 3252542050216635744081577 := by
  unfold tailWord_6334303
  simp only [CollatzResearch.WordTrace]
  refine ⟨231031010370909518669991563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154020673580606345779994375 231031010370909518669991563)
  ·
    refine ⟨346546515556364278004987345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231031010370909518669991563 346546515556364278004987345)
    ·
      refine ⟨259909886667273208503740509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346546515556364278004987345 259909886667273208503740509)
      ·
        refine ⟨97466207500227453188902691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259909886667273208503740509 97466207500227453188902691)
        ·
          refine ⟨146199311250341179783354037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97466207500227453188902691 146199311250341179783354037)
          ·
            refine ⟨13706185429719485604689441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146199311250341179783354037 13706185429719485604689441)
            ·
              refine ⟨10279639072289614203517081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13706185429719485604689441 10279639072289614203517081)
              ·
                refine ⟨7709729304217210652637811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10279639072289614203517081 7709729304217210652637811)
                ·
                  refine ⟨11564593956325815978956717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7709729304217210652637811 11564593956325815978956717)
                  ·
                    refine ⟨4336722733622180992108769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11564593956325815978956717 4336722733622180992108769)
                    ·
                      refine ⟨3252542050216635744081577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4336722733622180992108769 3252542050216635744081577)
                      ·
                        rfl

theorem cell23_6334303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_6334303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334303 prefixEnd_6334303 := by exact prefixLift 6334303
  have htrace : WordTrace (prefixWord ++ tailWord_6334303) baseStart_6334303 baseEnd_6334303 := by
    simpa [prefixWord, tailWord_6334303, baseEnd_6334303] using wordTrace_append hprefix tailTrace_6334303
  have hstable : (prefixWord ++ tailWord_6334303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334303).length < 2 ^ (prefixWord ++ tailWord_6334303).sum := by decide
  have hdescent : baseEnd_6334303 < baseStart_6334303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334333 : List Nat := [1, 4, 1, 1, 2, 1, 1, 6, 2, 2, 2]
def baseStart_6334333 : Nat := 118140960795 + 6334333 * 2 ^ 59
def prefixEnd_6334333 : Nat := 4983230072969 + 3 ^ 40 * 6334333 * 2
def baseEnd_6334333 : Nat := 3252557454636270626706439

theorem tailTrace_6334333 : CollatzResearch.WordTrace tailWord_6334333 prefixEnd_6334333 3252557454636270626706439 := by
  unfold tailWord_6334333
  simp only [CollatzResearch.WordTrace]
  refine ⟨231032104560800833793583653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154021403040533889195722435 231032104560800833793583653)
  ·
    refine ⟨43318519605150156336296935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231032104560800833793583653 43318519605150156336296935)
    ·
      refine ⟨64977779407725234504445403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43318519605150156336296935 64977779407725234504445403)
      ·
        refine ⟨97466669111587851756668105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64977779407725234504445403 97466669111587851756668105)
        ·
          refine ⟨73100001833690888817501079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97466669111587851756668105 73100001833690888817501079)
          ·
            refine ⟨109650002750536333226251619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73100001833690888817501079 109650002750536333226251619)
            ·
              refine ⟨164475004125804499839377429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109650002750536333226251619 164475004125804499839377429)
              ·
                refine ⟨7709765818397085929970817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164475004125804499839377429 7709765818397085929970817)
                ·
                  refine ⟨5782324363797814447478113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7709765818397085929970817 5782324363797814447478113)
                  ·
                    refine ⟨4336743272848360835608585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5782324363797814447478113 4336743272848360835608585)
                    ·
                      refine ⟨3252557454636270626706439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4336743272848360835608585 3252557454636270626706439)
                      ·
                        rfl

theorem cell23_6334333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_6334333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334333 prefixEnd_6334333 := by exact prefixLift 6334333
  have htrace : WordTrace (prefixWord ++ tailWord_6334333) baseStart_6334333 baseEnd_6334333 := by
    simpa [prefixWord, tailWord_6334333, baseEnd_6334333] using wordTrace_append hprefix tailTrace_6334333
  have hstable : (prefixWord ++ tailWord_6334333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334333).length < 2 ^ (prefixWord ++ tailWord_6334333).sum := by decide
  have hdescent : baseEnd_6334333 < baseStart_6334333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334339 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 7]
def baseStart_6334339 : Nat := 118140960795 + 6334339 * 2 ^ 59
def prefixEnd_6334339 : Nat := 4983230072969 + 3 ^ 40 * 6334339 * 2
def baseEnd_6334339 : Nat := 361395615057799733692379

theorem tailTrace_6334339 : CollatzResearch.WordTrace tailWord_6334339 prefixEnd_6334339 361395615057799733692379 := by
  unfold tailWord_6334339
  simp only [CollatzResearch.WordTrace]
  refine ⟨231032323398779096818302071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154021548932519397878868047 231032323398779096818302071)
  ·
    refine ⟨346548485098168645227453107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231032323398779096818302071 346548485098168645227453107)
    ·
      refine ⟨519822727647252967841179661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346548485098168645227453107 519822727647252967841179661)
      ·
        refine ⟨194933522867719862940442373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 519822727647252967841179661 194933522867719862940442373)
        ·
          refine ⟨36550035537697474301332945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194933522867719862940442373 36550035537697474301332945)
          ·
            refine ⟨27412526653273105725999709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36550035537697474301332945 27412526653273105725999709)
            ·
              refine ⟨10279697494977414647249891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27412526653273105725999709 10279697494977414647249891)
              ·
                refine ⟨15419546242466121970874837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10279697494977414647249891 15419546242466121970874837)
                ·
                  refine ⟨361395615057799733692379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15419546242466121970874837 361395615057799733692379)
                  ·
                    rfl

theorem cell23_6334339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 7].length) (baseStart_6334339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334339 prefixEnd_6334339 := by exact prefixLift 6334339
  have htrace : WordTrace (prefixWord ++ tailWord_6334339) baseStart_6334339 baseEnd_6334339 := by
    simpa [prefixWord, tailWord_6334339, baseEnd_6334339] using wordTrace_append hprefix tailTrace_6334339
  have hstable : (prefixWord ++ tailWord_6334339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334339).length < 2 ^ (prefixWord ++ tailWord_6334339).sum := by decide
  have hdescent : baseEnd_6334339 < baseStart_6334339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334409 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 3, 4, 3]
def baseStart_6334409 : Nat := 118140960795 + 6334409 * 2 ^ 59
def prefixEnd_6334409 : Nat := 4983230072969 + 3 ^ 40 * 6334409 * 2
def baseEnd_6334409 : Nat := 3252596479166012329356089

theorem tailTrace_6334409 : CollatzResearch.WordTrace tailWord_6334409 prefixEnd_6334409 3252596479166012329356089 := by
  unfold tailWord_6334409
  simp only [CollatzResearch.WordTrace]
  refine ⟨231034876508525498773350281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154023251005683665848900187 231034876508525498773350281)
  ·
    refine ⟨173276157381394124080012711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231034876508525498773350281 173276157381394124080012711)
    ·
      refine ⟨259914236072091186120019067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173276157381394124080012711 259914236072091186120019067)
      ·
        refine ⟨389871354108136779180028601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259914236072091186120019067 389871354108136779180028601)
        ·
          refine ⟨292403515581102584385021451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389871354108136779180028601 292403515581102584385021451)
          ·
            refine ⟨438605273371653876577532177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292403515581102584385021451 438605273371653876577532177)
            ·
              refine ⟨328953955028740407433149133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438605273371653876577532177 328953955028740407433149133)
              ·
                refine ⟨123357733135777652787430925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328953955028740407433149133 123357733135777652787430925)
                ·
                  refine ⟨46259149925916619795286597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123357733135777652787430925 46259149925916619795286597)
                  ·
                    refine ⟨8673590611109366211616237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46259149925916619795286597 8673590611109366211616237)
                    ·
                      refine ⟨3252596479166012329356089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8673590611109366211616237 3252596479166012329356089)
                      ·
                        rfl

theorem cell23_6334409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 4, 3].length) (baseStart_6334409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334409 prefixEnd_6334409 := by exact prefixLift 6334409
  have htrace : WordTrace (prefixWord ++ tailWord_6334409) baseStart_6334409 baseEnd_6334409 := by
    simpa [prefixWord, tailWord_6334409, baseEnd_6334409] using wordTrace_append hprefix tailTrace_6334409
  have hstable : (prefixWord ++ tailWord_6334409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334409).length < 2 ^ (prefixWord ++ tailWord_6334409).sum := by decide
  have hdescent : baseEnd_6334409 < baseStart_6334409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334433 : List Nat := [1, 2, 3, 1, 2, 1, 3, 5, 1, 4]
def baseStart_6334433 : Nat := 118140960795 + 6334433 * 2 ^ 59
def prefixEnd_6334433 : Nat := 4983230072969 + 3 ^ 40 * 6334433 * 2
def baseEnd_6334433 : Nat := 1084202934233906745151993

theorem tailTrace_6334433 : CollatzResearch.WordTrace tailWord_6334433 prefixEnd_6334433 1084202934233906745151993 := by
  unfold tailWord_6334433
  simp only [CollatzResearch.WordTrace]
  refine ⟨231035751860438550872223953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154023834573625700581482635 231035751860438550872223953)
  ·
    refine ⟨173276813895328913154167965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231035751860438550872223953 173276813895328913154167965)
    ·
      refine ⟨64978805210748342432812987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173276813895328913154167965 64978805210748342432812987)
      ·
        refine ⟨97468207816122513649219481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64978805210748342432812987 97468207816122513649219481)
        ·
          refine ⟨73101155862091885236914611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97468207816122513649219481 73101155862091885236914611)
          ·
            refine ⟨109651733793137827855371917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73101155862091885236914611 109651733793137827855371917)
            ·
              refine ⟨41119400172426685445764469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109651733793137827855371917 41119400172426685445764469)
              ·
                refine ⟨3854943766165001760540419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41119400172426685445764469 3854943766165001760540419)
                ·
                  refine ⟨5782415649247502640810629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854943766165001760540419 5782415649247502640810629)
                  ·
                    refine ⟨1084202934233906745151993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5782415649247502640810629 1084202934233906745151993)
                    ·
                      rfl

theorem cell23_6334433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_6334433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334433 prefixEnd_6334433 := by exact prefixLift 6334433
  have htrace : WordTrace (prefixWord ++ tailWord_6334433) baseStart_6334433 baseEnd_6334433 := by
    simpa [prefixWord, tailWord_6334433, baseEnd_6334433] using wordTrace_append hprefix tailTrace_6334433
  have hstable : (prefixWord ++ tailWord_6334433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334433).length < 2 ^ (prefixWord ++ tailWord_6334433).sum := by decide
  have hdescent : baseEnd_6334433 < baseStart_6334433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334446 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 8]
def baseStart_6334446 : Nat := 118140960795 + 6334446 * 2 ^ 59
def prefixEnd_6334446 : Nat := 4983230072969 + 3 ^ 40 * 6334446 * 2
def baseEnd_6334446 : Nat := 361401719772247631621491

theorem tailTrace_6334446 : CollatzResearch.WordTrace tailWord_6334446 prefixEnd_6334446 361401719772247631621491 := by
  unfold tailWord_6334446
  simp only [CollatzResearch.WordTrace]
  refine ⟨28879528251173931761555899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154024150672927636061631461 28879528251173931761555899)
  ·
    refine ⟨43319292376760897642333849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28879528251173931761555899 43319292376760897642333849)
    ·
      refine ⟨32489469282570673231750387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43319292376760897642333849 32489469282570673231750387)
      ·
        refine ⟨48734203923856009847625581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32489469282570673231750387 48734203923856009847625581)
        ·
          refine ⟨18275326471446003692859593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48734203923856009847625581 18275326471446003692859593)
          ·
            refine ⟨13706494853584502769644695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18275326471446003692859593 13706494853584502769644695)
            ·
              refine ⟨20559742280376754154467043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13706494853584502769644695 20559742280376754154467043)
              ·
                refine ⟨30839613420565131231700565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20559742280376754154467043 30839613420565131231700565)
                ·
                  refine ⟨361401719772247631621491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30839613420565131231700565 361401719772247631621491)
                  ·
                    rfl

theorem cell23_6334446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_6334446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334446 prefixEnd_6334446 := by exact prefixLift 6334446
  have htrace : WordTrace (prefixWord ++ tailWord_6334446) baseStart_6334446 baseEnd_6334446 := by
    simpa [prefixWord, tailWord_6334446, baseEnd_6334446] using wordTrace_append hprefix tailTrace_6334446
  have hstable : (prefixWord ++ tailWord_6334446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334446).length < 2 ^ (prefixWord ++ tailWord_6334446).sum := by decide
  have hdescent : baseEnd_6334446 < baseStart_6334446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334459 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 5, 5]
def baseStart_6334459 : Nat := 118140960795 + 6334459 * 2 ^ 59
def prefixEnd_6334459 : Nat := 4983230072969 + 3 ^ 40 * 6334459 * 2
def baseEnd_6334459 : Nat := 1084207384399579044576953

theorem tailTrace_6334459 : CollatzResearch.WordTrace tailWord_6334459 prefixEnd_6334459 1084207384399579044576953 := by
  unfold tailWord_6334459
  simp only [CollatzResearch.WordTrace]
  refine ⟨231036700158344357312670431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154024466772229571541780287 231036700158344357312670431)
  ·
    refine ⟨346555050237516535969005647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231036700158344357312670431 346555050237516535969005647)
    ·
      refine ⟨519832575356274803953508471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346555050237516535969005647 519832575356274803953508471)
      ·
        refine ⟨779748863034412205930262707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519832575356274803953508471 779748863034412205930262707)
        ·
          refine ⟨1169623294551618308895394061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779748863034412205930262707 1169623294551618308895394061)
          ·
            refine ⟨438608735456856865835772773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1169623294551618308895394061 438608735456856865835772773)
            ·
              refine ⟨82239137898160662344207395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 438608735456856865835772773 82239137898160662344207395)
              ·
                refine ⟨123358706847240993516311093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82239137898160662344207395 123358706847240993516311093)
                ·
                  refine ⟨11564878766928843142154165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123358706847240993516311093 11564878766928843142154165)
                  ·
                    refine ⟨1084207384399579044576953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11564878766928843142154165 1084207384399579044576953)
                    ·
                      rfl

theorem cell23_6334459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 5].length) (baseStart_6334459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334459 prefixEnd_6334459 := by exact prefixLift 6334459
  have htrace : WordTrace (prefixWord ++ tailWord_6334459) baseStart_6334459 baseEnd_6334459 := by
    simpa [prefixWord, tailWord_6334459, baseEnd_6334459] using wordTrace_append hprefix tailTrace_6334459
  have hstable : (prefixWord ++ tailWord_6334459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334459).length < 2 ^ (prefixWord ++ tailWord_6334459).sum := by decide
  have hdescent : baseEnd_6334459 < baseStart_6334459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334489 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 3, 6]
def baseStart_6334489 : Nat := 118140960795 + 6334489 * 2 ^ 59
def prefixEnd_6334489 : Nat := 4983230072969 + 3 ^ 40 * 6334489 * 2
def baseEnd_6334489 : Nat := 1084212519206124005451907

theorem tailTrace_6334489 : CollatzResearch.WordTrace tailWord_6334489 prefixEnd_6334489 1084212519206124005451907 := by
  unfold tailWord_6334489
  simp only [CollatzResearch.WordTrace]
  refine ⟨231037794348235672436262521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154025196232157114957508347 231037794348235672436262521)
  ·
    refine ⟨173278345761176754327196891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231037794348235672436262521 173278345761176754327196891)
    ·
      refine ⟨259917518641765131490795337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173278345761176754327196891 259917518641765131490795337)
      ·
        refine ⟨194938138981323848618096503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259917518641765131490795337 194938138981323848618096503)
        ·
          refine ⟨292407208471985772927144755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194938138981323848618096503 292407208471985772927144755)
          ·
            refine ⟨438610812707978659390717133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292407208471985772927144755 438610812707978659390717133)
            ·
              refine ⟨164479054765491997271518925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 438610812707978659390717133 164479054765491997271518925)
              ·
                refine ⟨61679645537059498976819597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164479054765491997271518925 61679645537059498976819597)
                ·
                  refine ⟨23129867076397312116307349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61679645537059498976819597 23129867076397312116307349)
                  ·
                    refine ⟨1084212519206124005451907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23129867076397312116307349 1084212519206124005451907)
                    ·
                      rfl

theorem cell23_6334489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_6334489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334489 prefixEnd_6334489 := by exact prefixLift 6334489
  have htrace : WordTrace (prefixWord ++ tailWord_6334489) baseStart_6334489 baseEnd_6334489 := by
    simpa [prefixWord, tailWord_6334489, baseEnd_6334489] using wordTrace_append hprefix tailTrace_6334489
  have hstable : (prefixWord ++ tailWord_6334489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334489).length < 2 ^ (prefixWord ++ tailWord_6334489).sum := by decide
  have hdescent : baseEnd_6334489 < baseStart_6334489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334493 : List Nat := [1, 4, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_6334493 : Nat := 118140960795 + 6334493 * 2 ^ 59
def prefixEnd_6334493 : Nat := 4983230072969 + 3 ^ 40 * 6334493 * 2
def baseEnd_6334493 : Nat := 1084213203846996666901901

theorem tailTrace_6334493 : CollatzResearch.WordTrace tailWord_6334493 prefixEnd_6334493 1084213203846996666901901 := by
  unfold tailWord_6334493
  simp only [CollatzResearch.WordTrace]
  refine ⟨231037940240221181119408133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154025293493480787412938755 231037940240221181119408133)
  ·
    refine ⟨43319613795041471459889025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231037940240221181119408133 43319613795041471459889025)
    ·
      refine ⟨32489710346281103594916769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43319613795041471459889025 32489710346281103594916769)
      ·
        refine ⟨24367282759710827696187577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32489710346281103594916769 24367282759710827696187577)
        ·
          refine ⟨18275462069783120772140683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24367282759710827696187577 18275462069783120772140683)
          ·
            refine ⟨27413193104674681158211025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18275462069783120772140683 27413193104674681158211025)
            ·
              refine ⟨20559894828506010868658269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27413193104674681158211025 20559894828506010868658269)
              ·
                refine ⟨7709960560689754075746851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20559894828506010868658269 7709960560689754075746851)
                ·
                  refine ⟨11564940841034631113620277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7709960560689754075746851 11564940841034631113620277)
                  ·
                    refine ⟨1084213203846996666901901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11564940841034631113620277 1084213203846996666901901)
                    ·
                      rfl

theorem cell23_6334493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_6334493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334493 prefixEnd_6334493 := by exact prefixLift 6334493
  have htrace : WordTrace (prefixWord ++ tailWord_6334493) baseStart_6334493 baseEnd_6334493 := by
    simpa [prefixWord, tailWord_6334493, baseEnd_6334493] using wordTrace_append hprefix tailTrace_6334493
  have hstable : (prefixWord ++ tailWord_6334493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334493).length < 2 ^ (prefixWord ++ tailWord_6334493).sum := by decide
  have hdescent : baseEnd_6334493 < baseStart_6334493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334519 : List Nat := [1, 1, 3, 1, 2, 2, 3, 10]
def baseStart_6334519 : Nat := 118140960795 + 6334519 * 2 ^ 59
def prefixEnd_6334519 : Nat := 4983230072969 + 3 ^ 40 * 6334519 * 2
def baseEnd_6334519 : Nat := 120468628223629885147429

theorem tailTrace_6334519 : CollatzResearch.WordTrace tailWord_6334519 prefixEnd_6334519 120468628223629885147429 := by
  unfold tailWord_6334519
  simp only [CollatzResearch.WordTrace]
  refine ⟨231038888538126987559854611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154025925692084658373236407 231038888538126987559854611)
  ·
    refine ⟨346558332807190481339781917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231038888538126987559854611 346558332807190481339781917)
    ·
      refine ⟨129959374802696430502418219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346558332807190481339781917 129959374802696430502418219)
      ·
        refine ⟨194939062204044645753627329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129959374802696430502418219 194939062204044645753627329)
        ·
          refine ⟨146204296653033484315220497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194939062204044645753627329 146204296653033484315220497)
          ·
            refine ⟨109653222489775113236415373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146204296653033484315220497 109653222489775113236415373)
            ·
              refine ⟨41119958433665667463655765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109653222489775113236415373 41119958433665667463655765)
              ·
                refine ⟨120468628223629885147429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41119958433665667463655765 120468628223629885147429)
                ·
                  rfl

theorem cell23_6334519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 10].length) (baseStart_6334519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334519 prefixEnd_6334519 := by exact prefixLift 6334519
  have htrace : WordTrace (prefixWord ++ tailWord_6334519) baseStart_6334519 baseEnd_6334519 := by
    simpa [prefixWord, tailWord_6334519, baseEnd_6334519] using wordTrace_append hprefix tailTrace_6334519
  have hstable : (prefixWord ++ tailWord_6334519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334519).length < 2 ^ (prefixWord ++ tailWord_6334519).sum := by decide
  have hdescent : baseEnd_6334519 < baseStart_6334519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334539 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 6]
def baseStart_6334539 : Nat := 118140960795 + 6334539 * 2 ^ 59
def prefixEnd_6334539 : Nat := 4983230072969 + 3 ^ 40 * 6334539 * 2
def baseEnd_6334539 : Nat := 3252663231651096820730491

theorem tailTrace_6334539 : CollatzResearch.WordTrace tailWord_6334539 prefixEnd_6334539 3252663231651096820730491 := by
  unfold tailWord_6334539
  simp only [CollatzResearch.WordTrace]
  refine ⟨231039617998054530975582671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154026411998703020650388447 231039617998054530975582671)
  ·
    refine ⟨346559426997081796463374007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231039617998054530975582671 346559426997081796463374007)
    ·
      refine ⟨519839140495622694695061011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346559426997081796463374007 519839140495622694695061011)
      ·
        refine ⟨779758710743434042042591517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519839140495622694695061011 779758710743434042042591517)
        ·
          refine ⟨292409516528787765765971819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 779758710743434042042591517 292409516528787765765971819)
          ·
            refine ⟨438614274793181648648957729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292409516528787765765971819 438614274793181648648957729)
            ·
              refine ⟨328960706094886236486718297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438614274793181648648957729 328960706094886236486718297)
              ·
                refine ⟨246720529571164677365038723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328960706094886236486718297 246720529571164677365038723)
                ·
                  refine ⟨370080794356747016047558085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246720529571164677365038723 370080794356747016047558085)
                  ·
                    refine ⟨69390148941890065508917141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 370080794356747016047558085 69390148941890065508917141)
                    ·
                      refine ⟨3252663231651096820730491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69390148941890065508917141 3252663231651096820730491)
                      ·
                        rfl

theorem cell23_6334539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_6334539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334539 prefixEnd_6334539 := by exact prefixLift 6334539
  have htrace : WordTrace (prefixWord ++ tailWord_6334539) baseStart_6334539 baseEnd_6334539 := by
    simpa [prefixWord, tailWord_6334539, baseEnd_6334539] using wordTrace_append hprefix tailTrace_6334539
  have hstable : (prefixWord ++ tailWord_6334539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334539).length < 2 ^ (prefixWord ++ tailWord_6334539).sum := by decide
  have hdescent : baseEnd_6334539 < baseStart_6334539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334557 : List Nat := [1, 4, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_6334557 : Nat := 118140960795 + 6334557 * 2 ^ 59
def prefixEnd_6334557 : Nat := 4983230072969 + 3 ^ 40 * 6334557 * 2
def baseEnd_6334557 : Nat := 1084224158100959250101803

theorem tailTrace_6334557 : CollatzResearch.WordTrace tailWord_6334557 prefixEnd_6334557 1084224158100959250101803 := by
  unfold tailWord_6334557
  simp only [CollatzResearch.WordTrace]
  refine ⟨231040274511989320049737925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154026849674659546699825283 231040274511989320049737925)
  ·
    refine ⟨43320051470997997509325861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231040274511989320049737925 43320051470997997509325861)
    ·
      refine ⟨8122509650812124532998599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43320051470997997509325861 8122509650812124532998599)
      ·
        refine ⟨12183764476218186799497899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8122509650812124532998599 12183764476218186799497899)
        ·
          refine ⟨18275646714327280199246849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12183764476218186799497899 18275646714327280199246849)
          ·
            refine ⟨13706735035745460149435137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18275646714327280199246849 13706735035745460149435137)
            ·
              refine ⟨10280051276809095112076353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13706735035745460149435137 10280051276809095112076353)
              ·
                refine ⟨7710038457606821334057265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10280051276809095112076353 7710038457606821334057265)
                ·
                  refine ⟨5782528843205116000542949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7710038457606821334057265 5782528843205116000542949)
                  ·
                    refine ⟨1084224158100959250101803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5782528843205116000542949 1084224158100959250101803)
                    ·
                      rfl

theorem cell23_6334557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_6334557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334557 prefixEnd_6334557 := by exact prefixLift 6334557
  have htrace : WordTrace (prefixWord ++ tailWord_6334557) baseStart_6334557 baseEnd_6334557 := by
    simpa [prefixWord, tailWord_6334557, baseEnd_6334557] using wordTrace_append hprefix tailTrace_6334557
  have hstable : (prefixWord ++ tailWord_6334557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334557).length < 2 ^ (prefixWord ++ tailWord_6334557).sum := by decide
  have hdescent : baseEnd_6334557 < baseStart_6334557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334563 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 4, 1, 3]
def baseStart_6334563 : Nat := 118140960795 + 6334563 * 2 ^ 59
def prefixEnd_6334563 : Nat := 4983230072969 + 3 ^ 40 * 6334563 * 2
def baseEnd_6334563 : Nat := 3252675555186804726830381

theorem tailTrace_6334563 : CollatzResearch.WordTrace tailWord_6334563 prefixEnd_6334563 3252675555186804726830381 := by
  unfold tailWord_6334563
  simp only [CollatzResearch.WordTrace]
  refine ⟨231040493349967583074456343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154026995566645055382970895 231040493349967583074456343)
  ·
    refine ⟨346560740024951374611684515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231040493349967583074456343 346560740024951374611684515)
    ·
      refine ⟨519841110037427061917526773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346560740024951374611684515 519841110037427061917526773)
      ·
        refine ⟨48735104066008787054768135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 519841110037427061917526773 48735104066008787054768135)
        ·
          refine ⟨73102656099013180582152203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48735104066008787054768135 73102656099013180582152203)
          ·
            refine ⟨109653984148519770873228305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73102656099013180582152203 109653984148519770873228305)
            ·
              refine ⟨82240488111389828154921229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109653984148519770873228305 82240488111389828154921229)
              ·
                refine ⟨30840183041771185558095461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82240488111389828154921229 30840183041771185558095461)
                ·
                  refine ⟨5782534320332097292142899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30840183041771185558095461 5782534320332097292142899)
                  ·
                    refine ⟨8673801480498145938214349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5782534320332097292142899 8673801480498145938214349)
                    ·
                      refine ⟨3252675555186804726830381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8673801480498145938214349 3252675555186804726830381)
                      ·
                        rfl

theorem cell23_6334563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_6334563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334563 prefixEnd_6334563 := by exact prefixLift 6334563
  have htrace : WordTrace (prefixWord ++ tailWord_6334563) baseStart_6334563 baseEnd_6334563 := by
    simpa [prefixWord, tailWord_6334563, baseEnd_6334563] using wordTrace_append hprefix tailTrace_6334563
  have hstable : (prefixWord ++ tailWord_6334563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334563).length < 2 ^ (prefixWord ++ tailWord_6334563).sum := by decide
  have hdescent : baseEnd_6334563 < baseStart_6334563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334564 : List Nat := [2, 3, 1, 1, 2, 1, 6, 2, 1, 2, 2]
def baseStart_6334564 : Nat := 118140960795 + 6334564 * 2 ^ 59
def prefixEnd_6334564 : Nat := 4983230072969 + 3 ^ 40 * 6334564 * 2
def baseEnd_6334564 : Nat := 3252676068667459222917877

theorem tailTrace_6334564 : CollatzResearch.WordTrace tailWord_6334564 prefixEnd_6334564 3252676068667459222917877 := by
  unfold tailWord_6334564
  simp only [CollatzResearch.WordTrace]
  refine ⟨115520264911481980122621373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154027019881975973496828497 115520264911481980122621373)
  ·
    refine ⟨43320099341805742545983015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115520264911481980122621373 43320099341805742545983015)
    ·
      refine ⟨64980149012708613818974523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43320099341805742545983015 64980149012708613818974523)
      ·
        refine ⟨97470223519062920728461785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64980149012708613818974523 97470223519062920728461785)
        ·
          refine ⟨73102667639297190546346339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97470223519062920728461785 73102667639297190546346339)
          ·
            refine ⟨109654001458945785819519509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73102667639297190546346339 109654001458945785819519509)
            ·
              refine ⟨5140031318388083710289977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109654001458945785819519509 5140031318388083710289977)
              ·
                refine ⟨3855023488791062782717483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5140031318388083710289977 3855023488791062782717483)
                ·
                  refine ⟨5782535233186594174076225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855023488791062782717483 5782535233186594174076225)
                  ·
                    refine ⟨4336901424889945630557169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5782535233186594174076225 4336901424889945630557169)
                    ·
                      refine ⟨3252676068667459222917877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4336901424889945630557169 3252676068667459222917877)
                      ·
                        rfl

theorem cell23_6334564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_6334564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334564 prefixEnd_6334564 := by exact prefixLift 6334564
  have htrace : WordTrace (prefixWord ++ tailWord_6334564) baseStart_6334564 baseEnd_6334564 := by
    simpa [prefixWord, tailWord_6334564, baseEnd_6334564] using wordTrace_append hprefix tailTrace_6334564
  have hstable : (prefixWord ++ tailWord_6334564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334564).length < 2 ^ (prefixWord ++ tailWord_6334564).sum := by decide
  have hdescent : baseEnd_6334564 < baseStart_6334564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334570 : List Nat := [3, 1, 3, 2, 4, 1, 1, 8]
def baseStart_6334570 : Nat := 118140960795 + 6334570 * 2 ^ 59
def prefixEnd_6334570 : Nat := 4983230072969 + 3 ^ 40 * 6334570 * 2
def baseEnd_6334570 : Nat := 120469598131532822201587

theorem tailTrace_6334570 : CollatzResearch.WordTrace tailWord_6334570 prefixEnd_6334570 120469598131532822201587 := by
  unfold tailWord_6334570
  simp only [CollatzResearch.WordTrace]
  refine ⟨57760187165235555817490291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154027165773961482179974109 57760187165235555817490291)
  ·
    refine ⟨86640280747853333726235437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57760187165235555817490291 86640280747853333726235437)
    ·
      refine ⟨32490105280445000147338289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86640280747853333726235437 32490105280445000147338289)
      ·
        refine ⟨24367578960333750110503717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32490105280445000147338289 24367578960333750110503717)
        ·
          refine ⟨4568921055062578145719447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24367578960333750110503717 4568921055062578145719447)
          ·
            refine ⟨6853381582593867218579171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4568921055062578145719447 6853381582593867218579171)
            ·
              refine ⟨10280072373890800827868757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6853381582593867218579171 10280072373890800827868757)
              ·
                refine ⟨120469598131532822201587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10280072373890800827868757 120469598131532822201587)
                ·
                  rfl

theorem cell23_6334570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 8].length) (baseStart_6334570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334570 prefixEnd_6334570 := by exact prefixLift 6334570
  have htrace : WordTrace (prefixWord ++ tailWord_6334570) baseStart_6334570 baseEnd_6334570 := by
    simpa [prefixWord, tailWord_6334570, baseEnd_6334570] using wordTrace_append hprefix tailTrace_6334570
  have hstable : (prefixWord ++ tailWord_6334570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334570).length < 2 ^ (prefixWord ++ tailWord_6334570).sum := by decide
  have hdescent : baseEnd_6334570 < baseStart_6334570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334596 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_6334596 : Nat := 118140960795 + 6334596 * 2 ^ 59
def prefixEnd_6334596 : Nat := 4983230072969 + 3 ^ 40 * 6334596 * 2
def baseEnd_6334596 : Nat := 1084230833349467699239243

theorem tailTrace_6334596 : CollatzResearch.WordTrace tailWord_6334596 prefixEnd_6334596 1084230833349467699239243 := by
  unfold tailWord_6334596
  simp only [CollatzResearch.WordTrace]
  refine ⟨115520848479424014855203821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154027797972565353140271761 115520848479424014855203821)
  ·
    refine ⟨43320318179784005570701433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115520848479424014855203821 43320318179784005570701433)
    ·
      refine ⟨32490238634838004178026075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43320318179784005570701433 32490238634838004178026075)
      ·
        refine ⟨48735357952257006267039113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32490238634838004178026075 48735357952257006267039113)
        ·
          refine ⟨36551518464192754700279335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48735357952257006267039113 36551518464192754700279335)
          ·
            refine ⟨54827277696289132050419003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36551518464192754700279335 54827277696289132050419003)
            ·
              refine ⟨82240916544433698075628505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54827277696289132050419003 82240916544433698075628505)
              ·
                refine ⟨61680687408325273556721379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82240916544433698075628505 61680687408325273556721379)
                ·
                  refine ⟨92521031112487910335082069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61680687408325273556721379 92521031112487910335082069)
                  ·
                    refine ⟨1084230833349467699239243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92521031112487910335082069 1084230833349467699239243)
                    ·
                      rfl

theorem cell23_6334596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_6334596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334596 prefixEnd_6334596 := by exact prefixLift 6334596
  have htrace : WordTrace (prefixWord ++ tailWord_6334596) baseStart_6334596 baseEnd_6334596 := by
    simpa [prefixWord, tailWord_6334596, baseEnd_6334596] using wordTrace_append hprefix tailTrace_6334596
  have hstable : (prefixWord ++ tailWord_6334596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334596).length < 2 ^ (prefixWord ++ tailWord_6334596).sum := by decide
  have hdescent : baseEnd_6334596 < baseStart_6334596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334637 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_6334637 : Nat := 118140960795 + 6334637 * 2 ^ 59
def prefixEnd_6334637 : Nat := 4983230072969 + 3 ^ 40 * 6334637 * 2
def baseEnd_6334637 : Nat := 3252713552755237437305041

theorem tailTrace_6334637 : CollatzResearch.WordTrace tailWord_6334637 prefixEnd_6334637 3252713552755237437305041 := by
  unfold tailWord_6334637
  simp only [CollatzResearch.WordTrace]
  refine ⟨231043192351699493712650165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154028794901132995808433443 231043192351699493712650165)
  ·
    refine ⟨21660299282971827535560953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231043192351699493712650165 21660299282971827535560953)
    ·
      refine ⟨16245224462228870651670715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21660299282971827535560953 16245224462228870651670715)
      ·
        refine ⟨24367836693343305977506073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16245224462228870651670715 24367836693343305977506073)
        ·
          refine ⟨18275877520007479483129555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24367836693343305977506073 18275877520007479483129555)
          ·
            refine ⟨27413816280011219224694333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18275877520007479483129555 27413816280011219224694333)
            ·
              refine ⟨10280181105004207209260375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27413816280011219224694333 10280181105004207209260375)
              ·
                refine ⟨15420271657506310813890563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10280181105004207209260375 15420271657506310813890563)
                ·
                  refine ⟨23130407486259466220835845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15420271657506310813890563 23130407486259466220835845)
                  ·
                    refine ⟨4336951403673649916406721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23130407486259466220835845 4336951403673649916406721)
                    ·
                      refine ⟨3252713552755237437305041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4336951403673649916406721 3252713552755237437305041)
                      ·
                        rfl

theorem cell23_6334637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_6334637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334637 prefixEnd_6334637 := by exact prefixLift 6334637
  have htrace : WordTrace (prefixWord ++ tailWord_6334637) baseStart_6334637 baseEnd_6334637 := by
    simpa [prefixWord, tailWord_6334637, baseEnd_6334637] using wordTrace_append hprefix tailTrace_6334637
  have hstable : (prefixWord ++ tailWord_6334637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334637).length < 2 ^ (prefixWord ++ tailWord_6334637).sum := by decide
  have hdescent : baseEnd_6334637 < baseStart_6334637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334663 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 3, 7, 2]
def baseStart_6334663 : Nat := 118140960795 + 6334663 * 2 ^ 59
def prefixEnd_6334663 : Nat := 4983230072969 + 3 ^ 40 * 6334663 * 2
def baseEnd_6334663 : Nat := 3252726903252254335579921

theorem tailTrace_6334663 : CollatzResearch.WordTrace tailWord_6334663 prefixEnd_6334663 3252726903252254335579921 := by
  unfold tailWord_6334663
  simp only [CollatzResearch.WordTrace]
  refine ⟨231044140649605300153096643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154029427099736866768731095 231044140649605300153096643)
  ·
    refine ⟨346566210974407950229644965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231044140649605300153096643 346566210974407950229644965)
    ·
      refine ⟨64981164557701490668058431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346566210974407950229644965 64981164557701490668058431)
      ·
        refine ⟨97471746836552236002087647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64981164557701490668058431 97471746836552236002087647)
        ·
          refine ⟨146207620254828354003131471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97471746836552236002087647 146207620254828354003131471)
          ·
            refine ⟨219311430382242531004697207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146207620254828354003131471 219311430382242531004697207)
            ·
              refine ⟨328967145573363796507045811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219311430382242531004697207 328967145573363796507045811)
              ·
                refine ⟨493450718360045694760568717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328967145573363796507045811 493450718360045694760568717)
                ·
                  refine ⟨185044019385017135535213269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493450718360045694760568717 185044019385017135535213269)
                  ·
                    refine ⟨4336969204336339114106561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 185044019385017135535213269 4336969204336339114106561)
                    ·
                      refine ⟨3252726903252254335579921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4336969204336339114106561 3252726903252254335579921)
                      ·
                        rfl

theorem cell23_6334663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_6334663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334663 prefixEnd_6334663 := by exact prefixLift 6334663
  have htrace : WordTrace (prefixWord ++ tailWord_6334663) baseStart_6334663 baseEnd_6334663 := by
    simpa [prefixWord, tailWord_6334663, baseEnd_6334663] using wordTrace_append hprefix tailTrace_6334663
  have hstable : (prefixWord ++ tailWord_6334663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334663).length < 2 ^ (prefixWord ++ tailWord_6334663).sum := by decide
  have hdescent : baseEnd_6334663 < baseStart_6334663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334677 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 7]
def baseStart_6334677 : Nat := 118140960795 + 6334677 * 2 ^ 59
def prefixEnd_6334677 : Nat := 4983230072969 + 3 ^ 40 * 6334677 * 2
def baseEnd_6334677 : Nat := 361414899109046364533873

theorem tailTrace_6334677 : CollatzResearch.WordTrace tailWord_6334677 prefixEnd_6334677 361414899109046364533873 := by
  unfold tailWord_6334677
  simp only [CollatzResearch.WordTrace]
  refine ⟨231044651271554580544106285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154029767514369720362737523 231044651271554580544106285)
  ·
    refine ⟨86641744226832967704039857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231044651271554580544106285 86641744226832967704039857)
    ·
      refine ⟨64981308170124725778029893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86641744226832967704039857 64981308170124725778029893)
      ·
        refine ⟨12183995281898386083380605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64981308170124725778029893 12183995281898386083380605)
        ·
          refine ⟨4568998230711894781267727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12183995281898386083380605 4568998230711894781267727)
          ·
            refine ⟨6853497346067842171901591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4568998230711894781267727 6853497346067842171901591)
            ·
              refine ⟨10280246019101763257852387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6853497346067842171901591 10280246019101763257852387)
              ·
                refine ⟨15420369028652644886778581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10280246019101763257852387 15420369028652644886778581)
                ·
                  refine ⟨361414899109046364533873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15420369028652644886778581 361414899109046364533873)
                  ·
                    rfl

theorem cell23_6334677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 7].length) (baseStart_6334677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334677 prefixEnd_6334677 := by exact prefixLift 6334677
  have htrace : WordTrace (prefixWord ++ tailWord_6334677) baseStart_6334677 baseEnd_6334677 := by
    simpa [prefixWord, tailWord_6334677, baseEnd_6334677] using wordTrace_append hprefix tailTrace_6334677
  have hstable : (prefixWord ++ tailWord_6334677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334677).length < 2 ^ (prefixWord ++ tailWord_6334677).sum := by decide
  have hdescent : baseEnd_6334677 < baseStart_6334677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334710 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_6334710 : Nat := 118140960795 + 6334710 * 2 ^ 59
def prefixEnd_6334710 : Nat := 4983230072969 + 3 ^ 40 * 6334710 * 2
def baseEnd_6334710 : Nat := 3252751036843015651692205

theorem tailTrace_6334710 : CollatzResearch.WordTrace tailWord_6334710 prefixEnd_6334710 3252751036843015651692205 := by
  unfold tailWord_6334710
  simp only [CollatzResearch.WordTrace]
  refine ⟨14440365930027189198753599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154030569920290018120038389 14440365930027189198753599)
  ·
    refine ⟨21660548895040783798130399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14440365930027189198753599 21660548895040783798130399)
    ·
      refine ⟨32490823342561175697195599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21660548895040783798130399 32490823342561175697195599)
      ·
        refine ⟨48736235013841763545793399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32490823342561175697195599 48736235013841763545793399)
        ·
          refine ⟨73104352520762645318690099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48736235013841763545793399 73104352520762645318690099)
          ·
            refine ⟨109656528781143967978035149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73104352520762645318690099 109656528781143967978035149)
            ·
              refine ⟨41121198292928987991763181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109656528781143967978035149 41121198292928987991763181)
              ·
                refine ⟨15420449359848370496911193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41121198292928987991763181 15420449359848370496911193)
                ·
                  refine ⟨11565337019886277872683395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15420449359848370496911193 11565337019886277872683395)
                  ·
                    refine ⟨17348005529829416809025093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11565337019886277872683395 17348005529829416809025093)
                    ·
                      refine ⟨3252751036843015651692205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17348005529829416809025093 3252751036843015651692205)
                      ·
                        rfl

theorem cell23_6334710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_6334710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334710 prefixEnd_6334710 := by exact prefixLift 6334710
  have htrace : WordTrace (prefixWord ++ tailWord_6334710) baseStart_6334710 baseEnd_6334710 := by
    simpa [prefixWord, tailWord_6334710, baseEnd_6334710] using wordTrace_append hprefix tailTrace_6334710
  have hstable : (prefixWord ++ tailWord_6334710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334710).length < 2 ^ (prefixWord ++ tailWord_6334710).sum := by decide
  have hdescent : baseEnd_6334710 < baseStart_6334710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334730 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_6334730 : Nat := 118140960795 + 6334730 * 2 ^ 59
def prefixEnd_6334730 : Nat := 4983230072969 + 3 ^ 40 * 6334730 * 2
def baseEnd_6334730 : Nat := 3252761306456105573442113

theorem tailTrace_6334730 : CollatzResearch.WordTrace tailWord_6334730 prefixEnd_6334730 3252761306456105573442113 := by
  unfold tailWord_6334730
  simp only [CollatzResearch.WordTrace]
  refine ⟨57761646085090642648946411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154031056226908380397190429 57761646085090642648946411)
  ·
    refine ⟨86642469127635963973419617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57761646085090642648946411 86642469127635963973419617)
    ·
      refine ⟨64981851845726972980064713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86642469127635963973419617 64981851845726972980064713)
      ·
        refine ⟨48736388884295229735048535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64981851845726972980064713 48736388884295229735048535)
        ·
          refine ⟨73104583326442844602572803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48736388884295229735048535 73104583326442844602572803)
          ·
            refine ⟨109656874989664266903859205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73104583326442844602572803 109656874989664266903859205)
            ·
              refine ⟨20560664060562050044473601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109656874989664266903859205 20560664060562050044473601)
              ·
                refine ⟨15420498045421537533355201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20560664060562050044473601 15420498045421537533355201)
                ·
                  refine ⟨11565373534066153150016401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15420498045421537533355201 11565373534066153150016401)
                  ·
                    refine ⟨8674030150549614862512301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11565373534066153150016401 8674030150549614862512301)
                    ·
                      refine ⟨3252761306456105573442113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8674030150549614862512301 3252761306456105573442113)
                      ·
                        rfl

theorem cell23_6334730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_6334730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334730 prefixEnd_6334730 := by exact prefixLift 6334730
  have htrace : WordTrace (prefixWord ++ tailWord_6334730) baseStart_6334730 baseEnd_6334730 := by
    simpa [prefixWord, tailWord_6334730, baseEnd_6334730] using wordTrace_append hprefix tailTrace_6334730
  have hstable : (prefixWord ++ tailWord_6334730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334730).length < 2 ^ (prefixWord ++ tailWord_6334730).sum := by decide
  have hdescent : baseEnd_6334730 < baseStart_6334730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334737 : List Nat := [1, 2, 2, 1, 1, 6, 1, 4, 1, 4]
def baseStart_6334737 : Nat := 118140960795 + 6334737 * 2 ^ 59
def prefixEnd_6334737 : Nat := 4983230072969 + 3 ^ 40 * 6334737 * 2
def baseEnd_6334737 : Nat := 1084254966940229015351527

theorem tailTrace_6334737 : CollatzResearch.WordTrace tailWord_6334737 prefixEnd_6334737 1084254966940229015351527 := by
  unfold tailWord_6334737
  simp only [CollatzResearch.WordTrace]
  refine ⟨231046839651337210791290465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154031226434224807194193643 231046839651337210791290465)
  ·
    refine ⟨173285129738502908093467849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231046839651337210791290465 173285129738502908093467849)
    ·
      refine ⟨129963847303877181070100887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173285129738502908093467849 129963847303877181070100887)
      ·
        refine ⟨194945770955815771605151331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129963847303877181070100887 194945770955815771605151331)
        ·
          refine ⟨292418656433723657407726997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194945770955815771605151331 292418656433723657407726997)
          ·
            refine ⟨13707124520330796440987203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 292418656433723657407726997 13707124520330796440987203)
            ·
              refine ⟨20560686780496194661480805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13707124520330796440987203 20560686780496194661480805)
              ·
                refine ⟨3855128771343036499027651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20560686780496194661480805 3855128771343036499027651)
                ·
                  refine ⟨5782693157014554748541477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855128771343036499027651 5782693157014554748541477)
                  ·
                    refine ⟨1084254966940229015351527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5782693157014554748541477 1084254966940229015351527)
                    ·
                      rfl

theorem cell23_6334737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_6334737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334737 prefixEnd_6334737 := by exact prefixLift 6334737
  have htrace : WordTrace (prefixWord ++ tailWord_6334737) baseStart_6334737 baseEnd_6334737 := by
    simpa [prefixWord, tailWord_6334737, baseEnd_6334737] using wordTrace_append hprefix tailTrace_6334737
  have hstable : (prefixWord ++ tailWord_6334737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334737).length < 2 ^ (prefixWord ++ tailWord_6334737).sum := by decide
  have hdescent : baseEnd_6334737 < baseStart_6334737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334780 : List Nat := [2, 2, 2, 2, 1, 2, 3, 3, 1, 5]
def baseStart_6334780 : Nat := 118140960795 + 6334780 * 2 ^ 59
def prefixEnd_6334780 : Nat := 4983230072969 + 3 ^ 40 * 6334780 * 2
def baseEnd_6334780 : Nat := 1084262326829610125938961

theorem tailTrace_6334780 : CollatzResearch.WordTrace tailWord_6334780 prefixEnd_6334780 1084262326829610125938961 := by
  unfold tailWord_6334780
  simp only [CollatzResearch.WordTrace]
  refine ⟨115524203995090714567552897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154032271993454286090070529 115524203995090714567552897)
  ·
    refine ⟨86643152996318035925664673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115524203995090714567552897 86643152996318035925664673)
    ·
      refine ⟨64982364747238526944248505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86643152996318035925664673 64982364747238526944248505)
      ·
        refine ⟨48736773560428895208186379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64982364747238526944248505 48736773560428895208186379)
        ·
          refine ⟨73105160340643342812279569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48736773560428895208186379 73105160340643342812279569)
          ·
            refine ⟨54828870255482507109209677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73105160340643342812279569 54828870255482507109209677)
            ·
              refine ⟨20560826345805940165953629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54828870255482507109209677 20560826345805940165953629)
              ·
                refine ⟨7710309879677227562232611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20560826345805940165953629 7710309879677227562232611)
                ·
                  refine ⟨11565464819515841343348917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7710309879677227562232611 11565464819515841343348917)
                  ·
                    refine ⟨1084262326829610125938961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11565464819515841343348917 1084262326829610125938961)
                    ·
                      rfl

theorem cell23_6334780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_6334780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334780 prefixEnd_6334780 := by exact prefixLift 6334780
  have htrace : WordTrace (prefixWord ++ tailWord_6334780) baseStart_6334780 baseEnd_6334780 := by
    simpa [prefixWord, tailWord_6334780, baseEnd_6334780] using wordTrace_append hprefix tailTrace_6334780
  have hstable : (prefixWord ++ tailWord_6334780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334780).length < 2 ^ (prefixWord ++ tailWord_6334780).sum := by decide
  have hdescent : baseEnd_6334780 < baseStart_6334780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334803 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 3]
def baseStart_6334803 : Nat := 118140960795 + 6334803 * 2 ^ 59
def prefixEnd_6334803 : Nat := 4983230072969 + 3 ^ 40 * 6334803 * 2
def baseEnd_6334803 : Nat := 3252798790543883787829277

theorem tailTrace_6334803 : CollatzResearch.WordTrace tailWord_6334803 prefixEnd_6334803 3252798790543883787829277 := by
  unfold tailWord_6334803
  simp only [CollatzResearch.WordTrace]
  refine ⟨231049246869098104063193063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154032831246065402708795375 231049246869098104063193063)
  ·
    refine ⟨346573870303647156094789595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231049246869098104063193063 346573870303647156094789595)
    ·
      refine ⟨519860805455470734142184393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346573870303647156094789595 519860805455470734142184393)
      ·
        refine ⟨389895604091603050606638295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519860805455470734142184393 389895604091603050606638295)
        ·
          refine ⟨584843406137404575909957443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389895604091603050606638295 584843406137404575909957443)
          ·
            refine ⟨877265109206106863864936165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584843406137404575909957443 877265109206106863864936165)
            ·
              refine ⟨164487207976145036974675531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 877265109206106863864936165 164487207976145036974675531)
              ·
                refine ⟨246730811964217555462013297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164487207976145036974675531 246730811964217555462013297)
                ·
                  refine ⟨185048108973163166596509973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246730811964217555462013297 185048108973163166596509973)
                  ·
                    refine ⟨8674130108117023434211405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 185048108973163166596509973 8674130108117023434211405)
                    ·
                      refine ⟨3252798790543883787829277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8674130108117023434211405 3252798790543883787829277)
                      ·
                        rfl

theorem cell23_6334803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 3].length) (baseStart_6334803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334803 prefixEnd_6334803 := by exact prefixLift 6334803
  have htrace : WordTrace (prefixWord ++ tailWord_6334803) baseStart_6334803 baseEnd_6334803 := by
    simpa [prefixWord, tailWord_6334803, baseEnd_6334803] using wordTrace_append hprefix tailTrace_6334803
  have hstable : (prefixWord ++ tailWord_6334803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334803).length < 2 ^ (prefixWord ++ tailWord_6334803).sum := by decide
  have hdescent : baseEnd_6334803 < baseStart_6334803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334828 : List Nat := [2, 2, 1, 1, 7, 1, 1, 3, 1, 1, 3]
def baseStart_6334828 : Nat := 118140960795 + 6334828 * 2 ^ 59
def prefixEnd_6334828 : Nat := 4983230072969 + 3 ^ 40 * 6334828 * 2
def baseEnd_6334828 : Nat := 3252811627560246190016663

theorem tailTrace_6334828 : CollatzResearch.WordTrace tailWord_6334828 prefixEnd_6334828 3252811627560246190016663 := by
  unfold tailWord_6334828
  simp only [CollatzResearch.WordTrace]
  refine ⟨115525079347003766666426569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154033439129338355555235425 115525079347003766666426569)
  ·
    refine ⟨86643809510252824999819927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115525079347003766666426569 86643809510252824999819927)
    ·
      refine ⟨129965714265379237499729891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86643809510252824999819927 129965714265379237499729891)
      ·
        refine ⟨194948571398068856249594837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129965714265379237499729891 194948571398068856249594837)
        ·
          refine ⟨4569107142142238818349879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 194948571398068856249594837 4569107142142238818349879)
          ·
            refine ⟨6853660713213358227524819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569107142142238818349879 6853660713213358227524819)
            ·
              refine ⟨10280491069820037341287229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6853660713213358227524819 10280491069820037341287229)
              ·
                refine ⟨3855184151182514002982711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10280491069820037341287229 3855184151182514002982711)
                ·
                  refine ⟨5782776226773771004474067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855184151182514002982711 5782776226773771004474067)
                  ·
                    refine ⟨8674164340160656506711101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5782776226773771004474067 8674164340160656506711101)
                    ·
                      refine ⟨3252811627560246190016663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8674164340160656506711101 3252811627560246190016663)
                      ·
                        rfl

theorem cell23_6334828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 1, 1, 3].length) (baseStart_6334828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334828 prefixEnd_6334828 := by exact prefixLift 6334828
  have htrace : WordTrace (prefixWord ++ tailWord_6334828) baseStart_6334828 baseEnd_6334828 := by
    simpa [prefixWord, tailWord_6334828, baseEnd_6334828] using wordTrace_append hprefix tailTrace_6334828
  have hstable : (prefixWord ++ tailWord_6334828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334828).length < 2 ^ (prefixWord ++ tailWord_6334828).sum := by decide
  have hdescent : baseEnd_6334828 < baseStart_6334828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334837 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_6334837 : Nat := 118140960795 + 6334837 * 2 ^ 59
def prefixEnd_6334837 : Nat := 4983230072969 + 3 ^ 40 * 6334837 * 2
def baseEnd_6334837 : Nat := 3252816248886136654804121

theorem tailTrace_6334837 : CollatzResearch.WordTrace tailWord_6334837 prefixEnd_6334837 3252816248886136654804121 := by
  unfold tailWord_6334837
  simp only [CollatzResearch.WordTrace]
  refine ⟨231050486950974927869930765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154033657967316618579953843 231050486950974927869930765)
  ·
    refine ⟨86643932606615597951224037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231050486950974927869930765 86643932606615597951224037)
    ·
      refine ⟨16245737363740424615854507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86643932606615597951224037 16245737363740424615854507)
      ·
        refine ⟨24368606045610636923781761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16245737363740424615854507 24368606045610636923781761)
        ·
          refine ⟨18276454534207977692836321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24368606045610636923781761 18276454534207977692836321)
          ·
            refine ⟨13707340900655983269627241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18276454534207977692836321 13707340900655983269627241)
            ·
              refine ⟨10280505675491987452220431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13707340900655983269627241 10280505675491987452220431)
              ·
                refine ⟨15420758513237981178330647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10280505675491987452220431 15420758513237981178330647)
                ·
                  refine ⟨23131137769856971767495971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15420758513237981178330647 23131137769856971767495971)
                  ·
                    refine ⟨34696706654785457651243957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23131137769856971767495971 34696706654785457651243957)
                    ·
                      refine ⟨3252816248886136654804121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34696706654785457651243957 3252816248886136654804121)
                      ·
                        rfl

theorem cell23_6334837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_6334837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334837 prefixEnd_6334837 := by exact prefixLift 6334837
  have htrace : WordTrace (prefixWord ++ tailWord_6334837) baseStart_6334837 baseEnd_6334837 := by
    simpa [prefixWord, tailWord_6334837, baseEnd_6334837] using wordTrace_append hprefix tailTrace_6334837
  have hstable : (prefixWord ++ tailWord_6334837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334837).length < 2 ^ (prefixWord ++ tailWord_6334837).sum := by decide
  have hdescent : baseEnd_6334837 < baseStart_6334837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334851 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 3, 2, 2]
def baseStart_6334851 : Nat := 118140960795 + 6334851 * 2 ^ 59
def prefixEnd_6334851 : Nat := 4983230072969 + 3 ^ 40 * 6334851 * 2
def baseEnd_6334851 : Nat := 3252823437615299600029057

theorem tailTrace_6334851 : CollatzResearch.WordTrace tailWord_6334851 prefixEnd_6334851 3252823437615299600029057 := by
  unfold tailWord_6334851
  simp only [CollatzResearch.WordTrace]
  refine ⟨231050997572924208260940407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154033998381949472173960271 231050997572924208260940407)
  ·
    refine ⟨346576496359386312391410611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231050997572924208260940407 346576496359386312391410611)
    ·
      refine ⟨519864744539079468587115917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346576496359386312391410611 519864744539079468587115917)
      ·
        refine ⟨194949279202154800720168469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 519864744539079468587115917 194949279202154800720168469)
        ·
          refine ⟨9138247462601006283757897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 194949279202154800720168469 9138247462601006283757897)
          ·
            refine ⟨6853685596950754712818423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9138247462601006283757897 6853685596950754712818423)
            ·
              refine ⟨10280528395426132069227635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6853685596950754712818423 10280528395426132069227635)
              ·
                refine ⟨15420792593139198103841453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10280528395426132069227635 15420792593139198103841453)
                ·
                  refine ⟨5782797222427199288940545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15420792593139198103841453 5782797222427199288940545)
                  ·
                    refine ⟨4337097916820399466705409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5782797222427199288940545 4337097916820399466705409)
                    ·
                      refine ⟨3252823437615299600029057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4337097916820399466705409 3252823437615299600029057)
                      ·
                        rfl

theorem cell23_6334851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 2, 2].length) (baseStart_6334851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334851 prefixEnd_6334851 := by exact prefixLift 6334851
  have htrace : WordTrace (prefixWord ++ tailWord_6334851) baseStart_6334851 baseEnd_6334851 := by
    simpa [prefixWord, tailWord_6334851, baseEnd_6334851] using wordTrace_append hprefix tailTrace_6334851
  have hstable : (prefixWord ++ tailWord_6334851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334851).length < 2 ^ (prefixWord ++ tailWord_6334851).sum := by decide
  have hdescent : baseEnd_6334851 < baseStart_6334851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334853 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 2, 7]
def baseStart_6334853 : Nat := 118140960795 + 6334853 * 2 ^ 59
def prefixEnd_6334853 : Nat := 4983230072969 + 3 ^ 40 * 6334853 * 2
def baseEnd_6334853 : Nat := 1084274821525536197401349

theorem tailTrace_6334853 : CollatzResearch.WordTrace tailWord_6334853 prefixEnd_6334853 1084274821525536197401349 := by
  unfold tailWord_6334853
  simp only [CollatzResearch.WordTrace]
  refine ⟨231051070518916962602513213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154034047012611308401675475 231051070518916962602513213)
  ·
    refine ⟨86644151444593860975942455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231051070518916962602513213 86644151444593860975942455)
    ·
      refine ⟨129966227166890791463913683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86644151444593860975942455 129966227166890791463913683)
      ·
        refine ⟨194949340750336187195870525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129966227166890791463913683 194949340750336187195870525)
        ·
          refine ⟨73106002781376070198451447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194949340750336187195870525 73106002781376070198451447)
          ·
            refine ⟨109659004172064105297677171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73106002781376070198451447 109659004172064105297677171)
            ·
              refine ⟨164488506258096157946515757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109659004172064105297677171 164488506258096157946515757)
              ·
                refine ⟨61683189846786059229943409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164488506258096157946515757 61683189846786059229943409)
                ·
                  refine ⟨46262392385089544422457557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61683189846786059229943409 46262392385089544422457557)
                  ·
                    refine ⟨1084274821525536197401349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46262392385089544422457557 1084274821525536197401349)
                    ·
                      rfl

theorem cell23_6334853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_6334853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334853 prefixEnd_6334853 := by exact prefixLift 6334853
  have htrace : WordTrace (prefixWord ++ tailWord_6334853) baseStart_6334853 baseEnd_6334853 := by
    simpa [prefixWord, tailWord_6334853, baseEnd_6334853] using wordTrace_append hprefix tailTrace_6334853
  have hstable : (prefixWord ++ tailWord_6334853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334853).length < 2 ^ (prefixWord ++ tailWord_6334853).sum := by decide
  have hdescent : baseEnd_6334853 < baseStart_6334853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334901 : List Nat := [1, 3, 3, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_6334901 : Nat := 118140960795 + 6334901 * 2 ^ 59
def prefixEnd_6334901 : Nat := 4983230072969 + 3 ^ 40 * 6334901 * 2
def baseEnd_6334901 : Nat := 3252849111648024404403827

theorem tailTrace_6334901 : CollatzResearch.WordTrace tailWord_6334901 prefixEnd_6334901 3252849111648024404403827 := by
  unfold tailWord_6334901
  simp only [CollatzResearch.WordTrace]
  refine ⟨231052821222743066800260557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154035214148495377866840371 231052821222743066800260557)
  ·
    refine ⟨86644807958528650050097709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231052821222743066800260557 86644807958528650050097709)
    ·
      refine ⟨32491802984448243768786641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86644807958528650050097709 32491802984448243768786641)
      ·
        refine ⟨24368852238336182826589981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32491802984448243768786641 24368852238336182826589981)
        ·
          refine ⟨9138319589376068559971243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24368852238336182826589981 9138319589376068559971243)
          ·
            refine ⟨13707479384064102839956865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9138319589376068559971243 13707479384064102839956865)
            ·
              refine ⟨10280609538048077129967649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13707479384064102839956865 10280609538048077129967649)
              ·
                refine ⟨7710457153536057847475737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10280609538048077129967649 7710457153536057847475737)
                ·
                  refine ⟨5782842865152043385606803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7710457153536057847475737 5782842865152043385606803)
                  ·
                    refine ⟨8674264297728065078410205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5782842865152043385606803 8674264297728065078410205)
                    ·
                      refine ⟨3252849111648024404403827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8674264297728065078410205 3252849111648024404403827)
                      ·
                        rfl

theorem cell23_6334901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_6334901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334901 prefixEnd_6334901 := by exact prefixLift 6334901
  have htrace : WordTrace (prefixWord ++ tailWord_6334901) baseStart_6334901 baseEnd_6334901 := by
    simpa [prefixWord, tailWord_6334901, baseEnd_6334901] using wordTrace_append hprefix tailTrace_6334901
  have hstable : (prefixWord ++ tailWord_6334901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334901).length < 2 ^ (prefixWord ++ tailWord_6334901).sum := by decide
  have hdescent : baseEnd_6334901 < baseStart_6334901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334910 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_6334910 : Nat := 118140960795 + 6334910 * 2 ^ 59
def prefixEnd_6334910 : Nat := 4983230072969 + 3 ^ 40 * 6334910 * 2
def baseEnd_6334910 : Nat := 3252853732973914869191285

theorem tailTrace_6334910 : CollatzResearch.WordTrace tailWord_6334910 prefixEnd_6334910 3252853732973914869191285 := by
  unfold tailWord_6334910
  simp only [CollatzResearch.WordTrace]
  refine ⟨28881643684963807667167273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154035432986473640891558789 28881643684963807667167273)
  ·
    refine ⟨21661232763722855750375455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28881643684963807667167273 21661232763722855750375455)
    ·
      refine ⟨32491849145584283625563183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21661232763722855750375455 32491849145584283625563183)
      ·
        refine ⟨48737773718376425438344775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32491849145584283625563183 48737773718376425438344775)
        ·
          refine ⟨73106660577564638157517163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48737773718376425438344775 73106660577564638157517163)
          ·
            refine ⟨109659990866346957236275745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73106660577564638157517163 109659990866346957236275745)
            ·
              refine ⟨82244993149760217927206809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109659990866346957236275745 82244993149760217927206809)
              ·
                refine ⟨61683744862320163445405107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82244993149760217927206809 61683744862320163445405107)
                ·
                  refine ⟨92525617293480245168107661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61683744862320163445405107 92525617293480245168107661)
                  ·
                    refine ⟨34697106485055091938040373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92525617293480245168107661 34697106485055091938040373)
                    ·
                      refine ⟨3252853732973914869191285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34697106485055091938040373 3252853732973914869191285)
                      ·
                        rfl

theorem cell23_6334910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_6334910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334910 prefixEnd_6334910 := by exact prefixLift 6334910
  have htrace : WordTrace (prefixWord ++ tailWord_6334910) baseStart_6334910 baseEnd_6334910 := by
    simpa [prefixWord, tailWord_6334910, baseEnd_6334910] using wordTrace_append hprefix tailTrace_6334910
  have hstable : (prefixWord ++ tailWord_6334910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334910).length < 2 ^ (prefixWord ++ tailWord_6334910).sum := by decide
  have hdescent : baseEnd_6334910 < baseStart_6334910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334920 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_6334920 : Nat := 118140960795 + 6334920 * 2 ^ 59
def prefixEnd_6334920 : Nat := 4983230072969 + 3 ^ 40 * 6334920 * 2
def baseEnd_6334920 : Nat := 3252858867780459830066239

theorem tailTrace_6334920 : CollatzResearch.WordTrace tailWord_6334920 prefixEnd_6334920 3252858867780459830066239 := by
  unfold tailWord_6334920
  simp only [CollatzResearch.WordTrace]
  refine ⟨115526757104837116522601107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154035676139782822030134809 115526757104837116522601107)
  ·
    refine ⟨173290135657255674783901661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115526757104837116522601107 173290135657255674783901661)
    ·
      refine ⟨64983800871470878043963123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173290135657255674783901661 64983800871470878043963123)
      ·
        refine ⟨97475701307206317065944685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64983800871470878043963123 97475701307206317065944685)
        ·
          refine ⟨36553387990202368899729257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97475701307206317065944685 36553387990202368899729257)
          ·
            refine ⟨27415040992651776674796943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36553387990202368899729257 27415040992651776674796943)
            ·
              refine ⟨41122561488977665012195415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27415040992651776674796943 41122561488977665012195415)
              ·
                refine ⟨61683842233466497518293123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41122561488977665012195415 61683842233466497518293123)
                ·
                  refine ⟨92525763350199746277439685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61683842233466497518293123 92525763350199746277439685)
                  ·
                    refine ⟨17348580628162452427019941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92525763350199746277439685 17348580628162452427019941)
                    ·
                      refine ⟨3252858867780459830066239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17348580628162452427019941 3252858867780459830066239)
                      ·
                        rfl

theorem cell23_6334920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_6334920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334920 prefixEnd_6334920 := by exact prefixLift 6334920
  have htrace : WordTrace (prefixWord ++ tailWord_6334920) baseStart_6334920 baseEnd_6334920 := by
    simpa [prefixWord, tailWord_6334920, baseEnd_6334920] using wordTrace_append hprefix tailTrace_6334920
  have hstable : (prefixWord ++ tailWord_6334920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334920).length < 2 ^ (prefixWord ++ tailWord_6334920).sum := by decide
  have hdescent : baseEnd_6334920 < baseStart_6334920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334958 : List Nat := [4, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_6334958 : Nat := 118140960795 + 6334958 * 2 ^ 59
def prefixEnd_6334958 : Nat := 4983230072969 + 3 ^ 40 * 6334958 * 2
def baseEnd_6334958 : Nat := 3252878380045330681391065

theorem tailTrace_6334958 : CollatzResearch.WordTrace tailWord_6334958 prefixEnd_6334958 3252878380045330681391065 := by
  unfold tailWord_6334958
  simp only [CollatzResearch.WordTrace]
  refine ⟨28881862522942070691885691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154036600122357710356723685 28881862522942070691885691)
  ·
    refine ⟨43322793784413106037828537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28881862522942070691885691 43322793784413106037828537)
    ·
      refine ⟨32492095338309829528371403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43322793784413106037828537 32492095338309829528371403)
      ·
        refine ⟨48738143007464744292557105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32492095338309829528371403 48738143007464744292557105)
        ·
          refine ⟨36553607255598558219417829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48738143007464744292557105 36553607255598558219417829)
          ·
            refine ⟨6853801360424729666140843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36553607255598558219417829 6853801360424729666140843)
            ·
              refine ⟨10280702040637094499211265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6853801360424729666140843 10280702040637094499211265)
              ·
                refine ⟨7710526530477820874408449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10280702040637094499211265 7710526530477820874408449)
                ·
                  refine ⟨5782894897858365655806337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7710526530477820874408449 5782894897858365655806337)
                  ·
                    refine ⟨4337171173393774241854753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5782894897858365655806337 4337171173393774241854753)
                    ·
                      refine ⟨3252878380045330681391065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4337171173393774241854753 3252878380045330681391065)
                      ·
                        rfl

theorem cell23_6334958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_6334958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334958 prefixEnd_6334958 := by exact prefixLift 6334958
  have htrace : WordTrace (prefixWord ++ tailWord_6334958) baseStart_6334958 baseEnd_6334958 := by
    simpa [prefixWord, tailWord_6334958, baseEnd_6334958] using wordTrace_append hprefix tailTrace_6334958
  have hstable : (prefixWord ++ tailWord_6334958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334958).length < 2 ^ (prefixWord ++ tailWord_6334958).sum := by decide
  have hdescent : baseEnd_6334958 < baseStart_6334958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334960 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 4, 5]
def baseStart_6334960 : Nat := 118140960795 + 6334960 * 2 ^ 59
def prefixEnd_6334960 : Nat := 4983230072969 + 3 ^ 40 * 6334960 * 2
def baseEnd_6334960 : Nat := 1084293135668879891188685

theorem tailTrace_6334960 : CollatzResearch.WordTrace tailWord_6334960 prefixEnd_6334960 1084293135668879891188685 := by
  unfold tailWord_6334960
  simp only [CollatzResearch.WordTrace]
  refine ⟨115527486564764659938329167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154036648753019546584438889 115527486564764659938329167)
  ·
    refine ⟨173291229847146989907493751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115527486564764659938329167 173291229847146989907493751)
    ·
      refine ⟨259936844770720484861240627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173291229847146989907493751 259936844770720484861240627)
      ·
        refine ⟨389905267156080727291860941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259936844770720484861240627 389905267156080727291860941)
        ·
          refine ⟨146214475183530272734447853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389905267156080727291860941 146214475183530272734447853)
          ·
            refine ⟨54830428193823852275417945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146214475183530272734447853 54830428193823852275417945)
            ·
              refine ⟨41122821145367889206563459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54830428193823852275417945 41122821145367889206563459)
              ·
                refine ⟨61684231718051833809845189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41122821145367889206563459 61684231718051833809845189)
                ·
                  refine ⟨11565793447134718839345973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61684231718051833809845189 11565793447134718839345973)
                  ·
                    refine ⟨1084293135668879891188685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11565793447134718839345973 1084293135668879891188685)
                    ·
                      rfl

theorem cell23_6334960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4, 5].length) (baseStart_6334960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334960 prefixEnd_6334960 := by exact prefixLift 6334960
  have htrace : WordTrace (prefixWord ++ tailWord_6334960) baseStart_6334960 baseEnd_6334960 := by
    simpa [prefixWord, tailWord_6334960, baseEnd_6334960] using wordTrace_append hprefix tailTrace_6334960
  have hstable : (prefixWord ++ tailWord_6334960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334960).length < 2 ^ (prefixWord ++ tailWord_6334960).sum := by decide
  have hdescent : baseEnd_6334960 < baseStart_6334960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6334997 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_6334997 : Nat := 118140960795 + 6334997 * 2 ^ 59
def prefixEnd_6334997 : Nat := 4983230072969 + 3 ^ 40 * 6334997 * 2
def baseEnd_6334997 : Nat := 3252898405790856028803385

theorem tailTrace_6334997 : CollatzResearch.WordTrace tailWord_6334997 prefixEnd_6334997 3252898405790856028803385 := by
  unfold tailWord_6334997
  simp only [CollatzResearch.WordTrace]
  refine ⟨231056322630395275195755245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154037548420263516797170163 231056322630395275195755245)
  ·
    refine ⟨86646120986398228198408217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231056322630395275195755245 86646120986398228198408217)
    ·
      refine ⟨64984590739798671148806163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86646120986398228198408217 64984590739798671148806163)
      ·
        refine ⟨97476886109698006723209245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64984590739798671148806163 97476886109698006723209245)
        ·
          refine ⟨36553832291136752521203467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97476886109698006723209245 36553832291136752521203467)
          ·
            refine ⟨54830748436705128781805201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36553832291136752521203467 54830748436705128781805201)
            ·
              refine ⟨41123061327528846586353901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54830748436705128781805201 41123061327528846586353901)
              ·
                refine ⟨15421147997823317469882713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41123061327528846586353901 15421147997823317469882713)
                ·
                  refine ⟨11565860998367488102412035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15421147997823317469882713 11565860998367488102412035)
                  ·
                    refine ⟨17348791497551232153618053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11565860998367488102412035 17348791497551232153618053)
                    ·
                      refine ⟨3252898405790856028803385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17348791497551232153618053 3252898405790856028803385)
                      ·
                        rfl

theorem cell23_6334997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_6334997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6334997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6334997 prefixEnd_6334997 := by exact prefixLift 6334997
  have htrace : WordTrace (prefixWord ++ tailWord_6334997) baseStart_6334997 baseEnd_6334997 := by
    simpa [prefixWord, tailWord_6334997, baseEnd_6334997] using wordTrace_append hprefix tailTrace_6334997
  have hstable : (prefixWord ++ tailWord_6334997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6334997).length < 2 ^ (prefixWord ++ tailWord_6334997).sum := by decide
  have hdescent : baseEnd_6334997 < baseStart_6334997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6334997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335024 : List Nat := [2, 1, 1, 1, 2, 3, 2, 6, 1, 4]
def baseStart_6335024 : Nat := 118140960795 + 6335024 * 2 ^ 59
def prefixEnd_6335024 : Nat := 4983230072969 + 3 ^ 40 * 6335024 * 2
def baseEnd_6335024 : Nat := 1084304089922842474388587

theorem tailTrace_6335024 : CollatzResearch.WordTrace tailWord_6335024 prefixEnd_6335024 1084304089922842474388587 := by
  unfold tailWord_6335024
  simp only [CollatzResearch.WordTrace]
  refine ⟨115528653700648729403494063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154038204934198305871325417 115528653700648729403494063)
  ·
    refine ⟨173292980550973094105241095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115528653700648729403494063 173292980550973094105241095)
    ·
      refine ⟨259939470826459641157861643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173292980550973094105241095 259939470826459641157861643)
      ·
        refine ⟨389909206239689461736792465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259939470826459641157861643 389909206239689461736792465)
        ·
          refine ⟨292431904679767096302594349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389909206239689461736792465 292431904679767096302594349)
          ·
            refine ⟨109661964254912661113472881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292431904679767096302594349 109661964254912661113472881)
            ·
              refine ⟨82246473191184495835104661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109661964254912661113472881 82246473191184495835104661)
              ·
                refine ⟨3855303430836773242270531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82246473191184495835104661 3855303430836773242270531)
                ·
                  refine ⟨5782955146255159863405797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855303430836773242270531 5782955146255159863405797)
                  ·
                    refine ⟨1084304089922842474388587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5782955146255159863405797 1084304089922842474388587)
                    ·
                      rfl

theorem cell23_6335024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 1, 4].length) (baseStart_6335024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335024 prefixEnd_6335024 := by exact prefixLift 6335024
  have htrace : WordTrace (prefixWord ++ tailWord_6335024) baseStart_6335024 baseEnd_6335024 := by
    simpa [prefixWord, tailWord_6335024, baseEnd_6335024] using wordTrace_append hprefix tailTrace_6335024
  have hstable : (prefixWord ++ tailWord_6335024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335024).length < 2 ^ (prefixWord ++ tailWord_6335024).sum := by decide
  have hdescent : baseEnd_6335024 < baseStart_6335024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335040 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 6]
def baseStart_6335040 : Nat := 118140960795 + 6335040 * 2 ^ 59
def prefixEnd_6335040 : Nat := 4983230072969 + 3 ^ 40 * 6335040 * 2
def baseEnd_6335040 : Nat := 3252920485458999360565687

theorem tailTrace_6335040 : CollatzResearch.WordTrace tailWord_6335040 prefixEnd_6335040 3252920485458999360565687 := by
  unfold tailWord_6335040
  simp only [CollatzResearch.WordTrace]
  refine ⟨115528945484619746769785287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154038593979492995693047049 115528945484619746769785287)
  ·
    refine ⟨173293418226929620154677931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115528945484619746769785287 173293418226929620154677931)
    ·
      refine ⟨259940127340394430232016897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173293418226929620154677931 259940127340394430232016897)
      ·
        refine ⟨194955095505295822674012673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259940127340394430232016897 194955095505295822674012673)
        ·
          refine ⟨146216321628971867005509505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194955095505295822674012673 146216321628971867005509505)
          ·
            refine ⟨109662241221728900254132129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146216321628971867005509505 109662241221728900254132129)
            ·
              refine ⟨82246680916296675190599097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109662241221728900254132129 82246680916296675190599097)
              ·
                refine ⟨61685010687222506392949323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82246680916296675190599097 61685010687222506392949323)
                ·
                  refine ⟨92527516030833759589423985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61685010687222506392949323 92527516030833759589423985)
                  ·
                    refine ⟨69395637023125319692067989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92527516030833759589423985 69395637023125319692067989)
                    ·
                      refine ⟨3252920485458999360565687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69395637023125319692067989 3252920485458999360565687)
                      ·
                        rfl

theorem cell23_6335040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_6335040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335040 prefixEnd_6335040 := by exact prefixLift 6335040
  have htrace : WordTrace (prefixWord ++ tailWord_6335040) baseStart_6335040 baseEnd_6335040 := by
    simpa [prefixWord, tailWord_6335040, baseEnd_6335040] using wordTrace_append hprefix tailTrace_6335040
  have hstable : (prefixWord ++ tailWord_6335040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335040).length < 2 ^ (prefixWord ++ tailWord_6335040).sum := by decide
  have hdescent : baseEnd_6335040 < baseStart_6335040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335087 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 4]
def baseStart_6335087 : Nat := 118140960795 + 6335087 * 2 ^ 59
def prefixEnd_6335087 : Nat := 4983230072969 + 3 ^ 40 * 6335087 * 2
def baseEnd_6335087 : Nat := 3252944619049760676677971

theorem tailTrace_6335087 : CollatzResearch.WordTrace tailWord_6335087 prefixEnd_6335087 3252944619049760676677971 := by
  unfold tailWord_6335087
  simp only [CollatzResearch.WordTrace]
  refine ⟨231059605200069220566531515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154039736800046147044354343 231059605200069220566531515)
  ·
    refine ⟨346589407800103830849797273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231059605200069220566531515 346589407800103830849797273)
    ·
      refine ⟨259942055850077873137347955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346589407800103830849797273 259942055850077873137347955)
      ·
        refine ⟨389913083775116809706021933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259942055850077873137347955 389913083775116809706021933)
        ·
          refine ⟨146217406415668803639758225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389913083775116809706021933 146217406415668803639758225)
          ·
            refine ⟨109663054811751602729818669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146217406415668803639758225 109663054811751602729818669)
            ·
              refine ⟨41123645554406851023682001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109663054811751602729818669 41123645554406851023682001)
              ·
                refine ⟨30842734165805138267761501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41123645554406851023682001 30842734165805138267761501)
                ·
                  refine ⟨11566025312176926850410563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30842734165805138267761501 11566025312176926850410563)
                  ·
                    refine ⟨17349037968265390275615845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11566025312176926850410563 17349037968265390275615845)
                    ·
                      refine ⟨3252944619049760676677971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17349037968265390275615845 3252944619049760676677971)
                      ·
                        rfl

theorem cell23_6335087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_6335087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335087 prefixEnd_6335087 := by exact prefixLift 6335087
  have htrace : WordTrace (prefixWord ++ tailWord_6335087) baseStart_6335087 baseEnd_6335087 := by
    simpa [prefixWord, tailWord_6335087, baseEnd_6335087] using wordTrace_append hprefix tailTrace_6335087
  have hstable : (prefixWord ++ tailWord_6335087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335087).length < 2 ^ (prefixWord ++ tailWord_6335087).sum := by decide
  have hdescent : baseEnd_6335087 < baseStart_6335087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335097 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 1, 6]
def baseStart_6335097 : Nat := 118140960795 + 6335097 * 2 ^ 59
def prefixEnd_6335097 : Nat := 4983230072969 + 3 ^ 40 * 6335097 * 2
def baseEnd_6335097 : Nat := 1084316584618768545850975

theorem tailTrace_6335097 : CollatzResearch.WordTrace tailWord_6335097 prefixEnd_6335097 1084316584618768545850975 := by
  unfold tailWord_6335097
  simp only [CollatzResearch.WordTrace]
  refine ⟨231059969930032992274395545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154039979953355328182930363 231059969930032992274395545)
  ·
    refine ⟨173294977447524744205796659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231059969930032992274395545 173294977447524744205796659)
    ·
      refine ⟨259942466171287116308694989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173294977447524744205796659 259942466171287116308694989)
      ·
        refine ⟨97478424814232668615760621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259942466171287116308694989 97478424814232668615760621)
        ·
          refine ⟨36554409305337250730910233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97478424814232668615760621 36554409305337250730910233)
          ·
            refine ⟨27415806979002938048182675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36554409305337250730910233 27415806979002938048182675)
            ·
              refine ⟨41123710468504407072274013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27415806979002938048182675 41123710468504407072274013)
              ·
                refine ⟨15421391425689152652102755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41123710468504407072274013 15421391425689152652102755)
                ·
                  refine ⟨23132087138533728978154133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15421391425689152652102755 23132087138533728978154133)
                  ·
                    refine ⟨1084316584618768545850975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23132087138533728978154133 1084316584618768545850975)
                    ·
                      rfl

theorem cell23_6335097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 6].length) (baseStart_6335097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335097 prefixEnd_6335097 := by exact prefixLift 6335097
  have htrace : WordTrace (prefixWord ++ tailWord_6335097) baseStart_6335097 baseEnd_6335097 := by
    simpa [prefixWord, tailWord_6335097, baseEnd_6335097] using wordTrace_append hprefix tailTrace_6335097
  have hstable : (prefixWord ++ tailWord_6335097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335097).length < 2 ^ (prefixWord ++ tailWord_6335097).sum := by decide
  have hdescent : baseEnd_6335097 < baseStart_6335097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335108 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_6335108 : Nat := 118140960795 + 6335108 * 2 ^ 59
def prefixEnd_6335108 : Nat := 4983230072969 + 3 ^ 40 * 6335108 * 2
def baseEnd_6335108 : Nat := 3252955402143505094515375

theorem tailTrace_6335108 : CollatzResearch.WordTrace tailWord_6335108 prefixEnd_6335108 3252955402143505094515375 := by
  unfold tailWord_6335108
  simp only [CollatzResearch.WordTrace]
  refine ⟨115530185566496570576522989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154040247421995427435363985 115530185566496570576522989)
  ·
    refine ⟨43323819587436213966196121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115530185566496570576522989 43323819587436213966196121)
    ·
      refine ⟨32492864690577160474647091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43323819587436213966196121 32492864690577160474647091)
      ·
        refine ⟨48739297035865740711970637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32492864690577160474647091 48739297035865740711970637)
        ·
          refine ⟨18277236388449652766988989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48739297035865740711970637 18277236388449652766988989)
          ·
            refine ⟨6853963645668619787620871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18277236388449652766988989 6853963645668619787620871)
            ·
              refine ⟨10280945468502929681431307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6853963645668619787620871 10280945468502929681431307)
              ·
                refine ⟨15421418202754394522146961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10280945468502929681431307 15421418202754394522146961)
                ·
                  refine ⟨11566063652065795891610221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15421418202754394522146961 11566063652065795891610221)
                  ·
                    refine ⟨4337273869524673459353833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11566063652065795891610221 4337273869524673459353833)
                    ·
                      refine ⟨3252955402143505094515375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4337273869524673459353833 3252955402143505094515375)
                      ·
                        rfl

theorem cell23_6335108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_6335108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335108 prefixEnd_6335108 := by exact prefixLift 6335108
  have htrace : WordTrace (prefixWord ++ tailWord_6335108) baseStart_6335108 baseEnd_6335108 := by
    simpa [prefixWord, tailWord_6335108, baseEnd_6335108] using wordTrace_append hprefix tailTrace_6335108
  have hstable : (prefixWord ++ tailWord_6335108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335108).length < 2 ^ (prefixWord ++ tailWord_6335108).sum := by decide
  have hdescent : baseEnd_6335108 < baseStart_6335108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335134 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_6335134 : Nat := 118140960795 + 6335134 * 2 ^ 59
def prefixEnd_6335134 : Nat := 4983230072969 + 3 ^ 40 * 6335134 * 2
def baseEnd_6335134 : Nat := 3252968752640521992790255

theorem tailTrace_6335134 : CollatzResearch.WordTrace tailWord_6335134 prefixEnd_6335134 3252968752640521992790255 := by
  unfold tailWord_6335134
  simp only [CollatzResearch.WordTrace]
  refine ⟨28882664928862368449186557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154040879620599298395661637 28882664928862368449186557)
  ·
    refine ⟨10830999348323388168444959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28882664928862368449186557 10830999348323388168444959)
    ·
      refine ⟨16246499022485082252667439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10830999348323388168444959 16246499022485082252667439)
      ·
        refine ⟨24369748533727623379001159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16246499022485082252667439 24369748533727623379001159)
        ·
          refine ⟨36554622800591435068501739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24369748533727623379001159 36554622800591435068501739)
          ·
            refine ⟨54831934200887152602752609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36554622800591435068501739 54831934200887152602752609)
            ·
              refine ⟨41123950650665364452064457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54831934200887152602752609 41123950650665364452064457)
              ·
                refine ⟨30842962987999023339048343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41123950650665364452064457 30842962987999023339048343)
                ·
                  refine ⟨46264444481998535008572515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30842962987999023339048343 46264444481998535008572515)
                  ·
                    refine ⟨69396666722997802512858773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46264444481998535008572515 69396666722997802512858773)
                    ·
                      refine ⟨3252968752640521992790255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69396666722997802512858773 3252968752640521992790255)
                      ·
                        rfl

theorem cell23_6335134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_6335134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335134 prefixEnd_6335134 := by exact prefixLift 6335134
  have htrace : WordTrace (prefixWord ++ tailWord_6335134) baseStart_6335134 baseEnd_6335134 := by
    simpa [prefixWord, tailWord_6335134, baseEnd_6335134] using wordTrace_append hprefix tailTrace_6335134
  have hstable : (prefixWord ++ tailWord_6335134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335134).length < 2 ^ (prefixWord ++ tailWord_6335134).sum := by decide
  have hdescent : baseEnd_6335134 < baseStart_6335134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335167 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 5]
def baseStart_6335167 : Nat := 118140960795 + 6335167 * 2 ^ 59
def prefixEnd_6335167 : Nat := 4983230072969 + 3 ^ 40 * 6335167 * 2
def baseEnd_6335167 : Nat := 3252985697502120363677603

theorem tailTrace_6335167 : CollatzResearch.WordTrace tailWord_6335167 prefixEnd_6335167 3252985697502120363677603 := by
  unfold tailWord_6335167
  simp only [CollatzResearch.WordTrace]
  refine ⟨231062523039779394229443755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154041682026519596152962503 231062523039779394229443755)
  ·
    refine ⟨346593784559669091344165633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231062523039779394229443755 346593784559669091344165633)
    ·
      refine ⟨259945338419751818508124225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346593784559669091344165633 259945338419751818508124225)
      ·
        refine ⟨194959003814813863881093169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259945338419751818508124225 194959003814813863881093169)
        ·
          refine ⟨146219252861110397910819877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194959003814813863881093169 146219252861110397910819877)
          ·
            refine ⟨27416109911458199608278727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146219252861110397910819877 27416109911458199608278727)
            ·
              refine ⟨41124164867187299412418091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27416109911458199608278727 41124164867187299412418091)
              ·
                refine ⟨61686247300780949118627137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41124164867187299412418091 61686247300780949118627137)
                ·
                  refine ⟨46264685475585711838970353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61686247300780949118627137 46264685475585711838970353)
                  ·
                    refine ⟨34698514106689283879227765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46264685475585711838970353 34698514106689283879227765)
                    ·
                      refine ⟨3252985697502120363677603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34698514106689283879227765 3252985697502120363677603)
                      ·
                        rfl

theorem cell23_6335167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_6335167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335167 prefixEnd_6335167 := by exact prefixLift 6335167
  have htrace : WordTrace (prefixWord ++ tailWord_6335167) baseStart_6335167 baseEnd_6335167 := by
    simpa [prefixWord, tailWord_6335167, baseEnd_6335167] using wordTrace_append hprefix tailTrace_6335167
  have hstable : (prefixWord ++ tailWord_6335167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335167).length < 2 ^ (prefixWord ++ tailWord_6335167).sum := by decide
  have hdescent : baseEnd_6335167 < baseStart_6335167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335172 : List Nat := [2, 3, 3, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_6335172 : Nat := 118140960795 + 6335172 * 2 ^ 59
def prefixEnd_6335172 : Nat := 4983230072969 + 3 ^ 40 * 6335172 * 2
def baseEnd_6335172 : Nat := 3252988264905392844115081

theorem tailTrace_6335172 : CollatzResearch.WordTrace tailWord_6335172 prefixEnd_6335172 3252988264905392844115081 := by
  unfold tailWord_6335172
  simp only [CollatzResearch.WordTrace]
  refine ⟨115531352702380640041687885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154041803603174186722250513 115531352702380640041687885)
  ·
    refine ⟨43324257263392740015632957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115531352702380640041687885 43324257263392740015632957)
    ·
      refine ⟨16246596473772277505862359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43324257263392740015632957 16246596473772277505862359)
      ·
        refine ⟨24369894710658416258793539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16246596473772277505862359 24369894710658416258793539)
        ·
          refine ⟨36554842065987624388190309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24369894710658416258793539 36554842065987624388190309)
          ·
            refine ⟨6854032887372679572785683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36554842065987624388190309 6854032887372679572785683)
            ·
              refine ⟨10281049331059019359178525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6854032887372679572785683 10281049331059019359178525)
              ·
                refine ⟨3855393499147132259691947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10281049331059019359178525 3855393499147132259691947)
                ·
                  refine ⟨5783090248720698389537921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855393499147132259691947 5783090248720698389537921)
                  ·
                    refine ⟨4337317686540523792153441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5783090248720698389537921 4337317686540523792153441)
                    ·
                      refine ⟨3252988264905392844115081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4337317686540523792153441 3252988264905392844115081)
                      ·
                        rfl

theorem cell23_6335172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_6335172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335172 prefixEnd_6335172 := by exact prefixLift 6335172
  have htrace : WordTrace (prefixWord ++ tailWord_6335172) baseStart_6335172 baseEnd_6335172 := by
    simpa [prefixWord, tailWord_6335172, baseEnd_6335172] using wordTrace_append hprefix tailTrace_6335172
  have hstable : (prefixWord ++ tailWord_6335172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335172).length < 2 ^ (prefixWord ++ tailWord_6335172).sum := by decide
  have hdescent : baseEnd_6335172 < baseStart_6335172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335189 : List Nat := [1, 3, 2, 5, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6335189 : Nat := 118140960795 + 6335189 * 2 ^ 59
def prefixEnd_6335189 : Nat := 4983230072969 + 3 ^ 40 * 6335189 * 2
def baseEnd_6335189 : Nat := 3252996994076519277602503

theorem tailTrace_6335189 : CollatzResearch.WordTrace tailWord_6335189 prefixEnd_6335189 3252996994076519277602503 := by
  unfold tailWord_6335189
  simp only [CollatzResearch.WordTrace]
  refine ⟨231063325445699691986744621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154042216963799794657829747 231063325445699691986744621)
  ·
    refine ⟨86648747042137384495029233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231063325445699691986744621 86648747042137384495029233)
    ·
      refine ⟨64986560281603038371271925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86648747042137384495029233 64986560281603038371271925)
      ·
        refine ⟨6092490026400284847306743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64986560281603038371271925 6092490026400284847306743)
        ·
          refine ⟨9138735039600427270960115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6092490026400284847306743 9138735039600427270960115)
          ·
            refine ⟨13708102559400640906440173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9138735039600427270960115 13708102559400640906440173)
            ·
              refine ⟨5140538459775240339915065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13708102559400640906440173 5140538459775240339915065)
              ·
                refine ⟨3855403844831430254936299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5140538459775240339915065 3855403844831430254936299)
                ·
                  refine ⟨5783105767247145382404449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855403844831430254936299 5783105767247145382404449)
                  ·
                    refine ⟨4337329325435359036803337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5783105767247145382404449 4337329325435359036803337)
                    ·
                      refine ⟨3252996994076519277602503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4337329325435359036803337 3252996994076519277602503)
                      ·
                        rfl

theorem cell23_6335189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6335189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335189 prefixEnd_6335189 := by exact prefixLift 6335189
  have htrace : WordTrace (prefixWord ++ tailWord_6335189) baseStart_6335189 baseEnd_6335189 := by
    simpa [prefixWord, tailWord_6335189, baseEnd_6335189] using wordTrace_append hprefix tailTrace_6335189
  have hstable : (prefixWord ++ tailWord_6335189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335189).length < 2 ^ (prefixWord ++ tailWord_6335189).sum := by decide
  have hdescent : baseEnd_6335189 < baseStart_6335189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335205 : List Nat := [1, 3, 1, 4, 1, 4, 2, 1, 2, 1, 3]
def baseStart_6335205 : Nat := 118140960795 + 6335205 * 2 ^ 59
def prefixEnd_6335205 : Nat := 4983230072969 + 3 ^ 40 * 6335205 * 2
def baseEnd_6335205 : Nat := 3253005209766991215002429

theorem tailTrace_6335205 : CollatzResearch.WordTrace tailWord_6335205 prefixEnd_6335205 3253005209766991215002429 := by
  unfold tailWord_6335205
  simp only [CollatzResearch.WordTrace]
  refine ⟨231063909013641726719327069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154042606009094484479551379 231063909013641726719327069)
  ·
    refine ⟨86648965880115647519747651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231063909013641726719327069 86648965880115647519747651)
    ·
      refine ⟨129973448820173471279621477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86648965880115647519747651 129973448820173471279621477)
      ·
        refine ⟨24370021653782525864929027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129973448820173471279621477 24370021653782525864929027)
        ·
          refine ⟨36555032480673788797393541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24370021653782525864929027 36555032480673788797393541)
          ·
            refine ⟨6854068590126335399511289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36555032480673788797393541 6854068590126335399511289)
            ·
              refine ⟨5140551442594751549633467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6854068590126335399511289 5140551442594751549633467)
              ·
                refine ⟨7710827163892127324450201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5140551442594751549633467 7710827163892127324450201)
                ·
                  refine ⟨5783120372919095493337651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7710827163892127324450201 5783120372919095493337651)
                  ·
                    refine ⟨8674680559378643240006477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5783120372919095493337651 8674680559378643240006477)
                    ·
                      refine ⟨3253005209766991215002429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8674680559378643240006477 3253005209766991215002429)
                      ·
                        rfl

theorem cell23_6335205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_6335205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335205 prefixEnd_6335205 := by exact prefixLift 6335205
  have htrace : WordTrace (prefixWord ++ tailWord_6335205) baseStart_6335205 baseEnd_6335205 := by
    simpa [prefixWord, tailWord_6335205, baseEnd_6335205] using wordTrace_append hprefix tailTrace_6335205
  have hstable : (prefixWord ++ tailWord_6335205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335205).length < 2 ^ (prefixWord ++ tailWord_6335205).sum := by decide
  have hdescent : baseEnd_6335205 < baseStart_6335205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335214 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_6335214 : Nat := 118140960795 + 6335214 * 2 ^ 59
def prefixEnd_6335214 : Nat := 4983230072969 + 3 ^ 40 * 6335214 * 2
def baseEnd_6335214 : Nat := 3253009831092881679789887

theorem tailTrace_6335214 : CollatzResearch.WordTrace tailWord_6335214 prefixEnd_6335214 3253009831092881679789887 := by
  unfold tailWord_6335214
  simp only [CollatzResearch.WordTrace]
  refine ⟨28883029658826140157050587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154042824847072747504269797 28883029658826140157050587)
  ·
    refine ⟨43324544488239210235575881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28883029658826140157050587 43324544488239210235575881)
    ·
      refine ⟨32493408366179407676681911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43324544488239210235575881 32493408366179407676681911)
      ·
        refine ⟨48740112549269111515022867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32493408366179407676681911 48740112549269111515022867)
        ·
          refine ⟨73110168823903667272534301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48740112549269111515022867 73110168823903667272534301)
          ·
            refine ⟨27416313308963875227200363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73110168823903667272534301 27416313308963875227200363)
            ·
              refine ⟨41124469963445812840800545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27416313308963875227200363 41124469963445812840800545)
              ·
                refine ⟨30843352472584359630600409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41124469963445812840800545 30843352472584359630600409)
                ·
                  refine ⟨23132514354438269722950307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30843352472584359630600409 23132514354438269722950307)
                  ·
                    refine ⟨34698771531657404584425461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23132514354438269722950307 34698771531657404584425461)
                    ·
                      refine ⟨3253009831092881679789887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34698771531657404584425461 3253009831092881679789887)
                      ·
                        rfl

theorem cell23_6335214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_6335214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335214 prefixEnd_6335214 := by exact prefixLift 6335214
  have htrace : WordTrace (prefixWord ++ tailWord_6335214) baseStart_6335214 baseEnd_6335214 := by
    simpa [prefixWord, tailWord_6335214, baseEnd_6335214] using wordTrace_append hprefix tailTrace_6335214
  have hstable : (prefixWord ++ tailWord_6335214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335214).length < 2 ^ (prefixWord ++ tailWord_6335214).sum := by decide
  have hdescent : baseEnd_6335214 < baseStart_6335214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335217 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 9]
def baseStart_6335217 : Nat := 118140960795 + 6335217 * 2 ^ 59
def prefixEnd_6335217 : Nat := 4983230072969 + 3 ^ 40 * 6335217 * 2
def baseEnd_6335217 : Nat := 361445707948316129783597

theorem tailTrace_6335217 : CollatzResearch.WordTrace tailWord_6335217 prefixEnd_6335217 361445707948316129783597 := by
  unfold tailWord_6335217
  simp only [CollatzResearch.WordTrace]
  refine ⟨231064346689598252768763905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154042897793065501845842603 231064346689598252768763905)
  ·
    refine ⟨173298260017198689576572929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231064346689598252768763905 173298260017198689576572929)
    ·
      refine ⟨129973695012899017182429697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173298260017198689576572929 129973695012899017182429697)
      ·
        refine ⟨97480271259674262886822273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129973695012899017182429697 97480271259674262886822273)
        ·
          refine ⟨73110203444755697165116705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97480271259674262886822273 73110203444755697165116705)
          ·
            refine ⟨54832652583566772873837529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73110203444755697165116705 54832652583566772873837529)
            ·
              refine ⟨41124489437675079655378147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54832652583566772873837529 41124489437675079655378147)
              ·
                refine ⟨61686734156512619483067221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41124489437675079655378147 61686734156512619483067221)
                ·
                  refine ⟨361445707948316129783597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61686734156512619483067221 361445707948316129783597)
                  ·
                    rfl

theorem cell23_6335217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 9].length) (baseStart_6335217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335217 prefixEnd_6335217 := by exact prefixLift 6335217
  have htrace : WordTrace (prefixWord ++ tailWord_6335217) baseStart_6335217 baseEnd_6335217 := by
    simpa [prefixWord, tailWord_6335217, baseEnd_6335217] using wordTrace_append hprefix tailTrace_6335217
  have hstable : (prefixWord ++ tailWord_6335217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335217).length < 2 ^ (prefixWord ++ tailWord_6335217).sum := by decide
  have hdescent : baseEnd_6335217 < baseStart_6335217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335244 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 2, 3, 3]
def baseStart_6335244 : Nat := 118140960795 + 6335244 * 2 ^ 59
def prefixEnd_6335244 : Nat := 4983230072969 + 3 ^ 40 * 6335244 * 2
def baseEnd_6335244 : Nat := 3253025235512516562414749

theorem tailTrace_6335244 : CollatzResearch.WordTrace tailWord_6335244 prefixEnd_6335244 3253025235512516562414749 := by
  unfold tailWord_6335244
  simp only [CollatzResearch.WordTrace]
  refine ⟨115532665730250218189998393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154043554307000290919997857 115532665730250218189998393)
  ·
    refine ⟨86649499297687663642498795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115532665730250218189998393 86649499297687663642498795)
    ·
      refine ⟨129974248946531495463748193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86649499297687663642498795 129974248946531495463748193)
      ·
        refine ⟨97480686709898621597811145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129974248946531495463748193 97480686709898621597811145)
        ·
          refine ⟨73110515032423966198358359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97480686709898621597811145 73110515032423966198358359)
          ·
            refine ⟨109665772548635949297537539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73110515032423966198358359 109665772548635949297537539)
            ·
              refine ⟨164498658822953923946306309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109665772548635949297537539 164498658822953923946306309)
              ·
                refine ⟨30843498529303860739932433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164498658822953923946306309 30843498529303860739932433)
                ·
                  refine ⟨23132623896977895554949325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30843498529303860739932433 23132623896977895554949325)
                  ·
                    refine ⟨8674733961366710833105997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23132623896977895554949325 8674733961366710833105997)
                    ·
                      refine ⟨3253025235512516562414749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8674733961366710833105997 3253025235512516562414749)
                      ·
                        rfl

theorem cell23_6335244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_6335244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335244 prefixEnd_6335244 := by exact prefixLift 6335244
  have htrace : WordTrace (prefixWord ++ tailWord_6335244) baseStart_6335244 baseEnd_6335244 := by
    simpa [prefixWord, tailWord_6335244, baseEnd_6335244] using wordTrace_append hprefix tailTrace_6335244
  have hstable : (prefixWord ++ tailWord_6335244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335244).length < 2 ^ (prefixWord ++ tailWord_6335244).sum := by decide
  have hdescent : baseEnd_6335244 < baseStart_6335244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335257 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 7]
def baseStart_6335257 : Nat := 118140960795 + 6335257 * 2 ^ 59
def prefixEnd_6335257 : Nat := 4983230072969 + 3 ^ 40 * 6335257 * 2
def baseEnd_6335257 : Nat := 3253031910761025011552189

theorem tailTrace_6335257 : CollatzResearch.WordTrace tailWord_6335257 prefixEnd_6335257 3253031910761025011552189 := by
  unfold tailWord_6335257
  simp only [CollatzResearch.WordTrace]
  refine ⟨231065805609453339600220025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154043870406302226400146683 231065805609453339600220025)
  ·
    refine ⟨173299354207090004700165019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231065805609453339600220025 173299354207090004700165019)
    ·
      refine ⟨259949031310635007050247529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173299354207090004700165019 259949031310635007050247529)
      ·
        refine ⟨194961773482976255287685647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259949031310635007050247529 194961773482976255287685647)
        ·
          refine ⟨292442660224464382931528471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194961773482976255287685647 292442660224464382931528471)
          ·
            refine ⟨438663990336696574397292707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292442660224464382931528471 438663990336696574397292707)
            ·
              refine ⟨657995985505044861595939061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438663990336696574397292707 657995985505044861595939061)
              ·
                refine ⟨61687123641097955774619287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 657995985505044861595939061 61687123641097955774619287)
                ·
                  refine ⟨92530685461646933661928931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61687123641097955774619287 92530685461646933661928931)
                  ·
                    refine ⟨138796028192470400492893397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92530685461646933661928931 138796028192470400492893397)
                    ·
                      refine ⟨3253031910761025011552189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138796028192470400492893397 3253031910761025011552189)
                      ·
                        rfl

theorem cell23_6335257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_6335257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335257 prefixEnd_6335257 := by exact prefixLift 6335257
  have htrace : WordTrace (prefixWord ++ tailWord_6335257) baseStart_6335257 baseEnd_6335257 := by
    simpa [prefixWord, tailWord_6335257, baseEnd_6335257] using wordTrace_append hprefix tailTrace_6335257
  have hstable : (prefixWord ++ tailWord_6335257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335257).length < 2 ^ (prefixWord ++ tailWord_6335257).sum := by decide
  have hdescent : baseEnd_6335257 < baseStart_6335257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335314 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_6335314 : Nat := 118140960795 + 6335314 * 2 ^ 59
def prefixEnd_6335314 : Nat := 4983230072969 + 3 ^ 40 * 6335314 * 2
def baseEnd_6335314 : Nat := 3253061179158331288539427

theorem tailTrace_6335314 : CollatzResearch.WordTrace tailWord_6335314 prefixEnd_6335314 3253061179158331288539427 := by
  unfold tailWord_6335314
  simp only [CollatzResearch.WordTrace]
  refine ⟨57766971142561709583761249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154045256380164558890029997 57766971142561709583761249)
  ·
    refine ⟨43325228356921282187820937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57766971142561709583761249 43325228356921282187820937)
    ·
      refine ⟨32493921267690961640865703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43325228356921282187820937 32493921267690961640865703)
      ·
        refine ⟨48740881901536442461298555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32493921267690961640865703 48740881901536442461298555)
        ·
          refine ⟨73111322852304663691947833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48740881901536442461298555 73111322852304663691947833)
          ·
            refine ⟨54833492139228497768960875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73111322852304663691947833 54833492139228497768960875)
            ·
              refine ⟨82250238208842746653441313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54833492139228497768960875 82250238208842746653441313)
              ·
                refine ⟨61687678656632059990080985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82250238208842746653441313 61687678656632059990080985)
                ·
                  refine ⟨46265758992474044992560739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61687678656632059990080985 46265758992474044992560739)
                  ·
                    refine ⟨69398638488711067488841109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46265758992474044992560739 69398638488711067488841109)
                    ·
                      refine ⟨3253061179158331288539427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69398638488711067488841109 3253061179158331288539427)
                      ·
                        rfl

theorem cell23_6335314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_6335314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335314 prefixEnd_6335314 := by exact prefixLift 6335314
  have htrace : WordTrace (prefixWord ++ tailWord_6335314) baseStart_6335314 baseEnd_6335314 := by
    simpa [prefixWord, tailWord_6335314, baseEnd_6335314] using wordTrace_append hprefix tailTrace_6335314
  have hstable : (prefixWord ++ tailWord_6335314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335314).length < 2 ^ (prefixWord ++ tailWord_6335314).sum := by decide
  have hdescent : baseEnd_6335314 < baseStart_6335314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335345 : List Nat := [1, 2, 2, 2, 1, 6, 1, 3, 1, 4]
def baseStart_6335345 : Nat := 118140960795 + 6335345 * 2 ^ 59
def prefixEnd_6335345 : Nat := 4983230072969 + 3 ^ 40 * 6335345 * 2
def baseEnd_6335345 : Nat := 1084359032352873555750595

theorem tailTrace_6335345 : CollatzResearch.WordTrace tailWord_6335345 prefixEnd_6335345 1084359032352873555750595 := by
  unfold tailWord_6335345
  simp only [CollatzResearch.WordTrace]
  refine ⟨231069015233134530629423489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154046010155423020419615659 231069015233134530629423489)
  ·
    refine ⟨173301761424850897972067617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231069015233134530629423489 173301761424850897972067617)
    ·
      refine ⟨129976321068638173479050713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173301761424850897972067617 129976321068638173479050713)
      ·
        refine ⟨97482240801478630109288035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129976321068638173479050713 97482240801478630109288035)
        ·
          refine ⟨146223361202217945163932053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97482240801478630109288035 146223361202217945163932053)
          ·
            refine ⟨6854220056353966179559315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 146223361202217945163932053 6854220056353966179559315)
            ·
              refine ⟨10281330084530949269338973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6854220056353966179559315 10281330084530949269338973)
              ·
                refine ⟨3855498781699105976002115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10281330084530949269338973 3855498781699105976002115)
                ·
                  refine ⟨5783248172548658964003173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855498781699105976002115 5783248172548658964003173)
                  ·
                    refine ⟨1084359032352873555750595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5783248172548658964003173 1084359032352873555750595)
                    ·
                      rfl

theorem cell23_6335345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_6335345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335345 prefixEnd_6335345 := by exact prefixLift 6335345
  have htrace : WordTrace (prefixWord ++ tailWord_6335345) baseStart_6335345 baseEnd_6335345 := by
    simpa [prefixWord, tailWord_6335345, baseEnd_6335345] using wordTrace_append hprefix tailTrace_6335345
  have hstable : (prefixWord ++ tailWord_6335345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335345).length < 2 ^ (prefixWord ++ tailWord_6335345).sum := by decide
  have hdescent : baseEnd_6335345 < baseStart_6335345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335351 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 5, 1, 3]
def baseStart_6335351 : Nat := 118140960795 + 6335351 * 2 ^ 59
def prefixEnd_6335351 : Nat := 4983230072969 + 3 ^ 40 * 6335351 * 2
def baseEnd_6335351 : Nat := 3253080177942547643776757

theorem tailTrace_6335351 : CollatzResearch.WordTrace tailWord_6335351 prefixEnd_6335351 3253080177942547643776757 := by
  unfold tailWord_6335351
  simp only [CollatzResearch.WordTrace]
  refine ⟨231069234071112793654141907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154046156047408529102761271 231069234071112793654141907)
  ·
    refine ⟨346603851106669190481212861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231069234071112793654141907 346603851106669190481212861)
    ·
      refine ⟨129976444165000946430454823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346603851106669190481212861 129976444165000946430454823)
      ·
        refine ⟨194964666247501419645682235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129976444165000946430454823 194964666247501419645682235)
        ·
          refine ⟨292446999371252129468523353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194964666247501419645682235 292446999371252129468523353)
          ·
            refine ⟨219335249528439097101392515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292446999371252129468523353 219335249528439097101392515)
            ·
              refine ⟨329002874292658645652088773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219335249528439097101392515 329002874292658645652088773)
              ·
                refine ⟨61688038929873496059766645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329002874292658645652088773 61688038929873496059766645)
                ·
                  refine ⟨5783253649675640255603123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61688038929873496059766645 5783253649675640255603123)
                  ·
                    refine ⟨8674880474513460383404685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5783253649675640255603123 8674880474513460383404685)
                    ·
                      refine ⟨3253080177942547643776757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8674880474513460383404685 3253080177942547643776757)
                      ·
                        rfl

theorem cell23_6335351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_6335351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335351 prefixEnd_6335351 := by exact prefixLift 6335351
  have htrace : WordTrace (prefixWord ++ tailWord_6335351) baseStart_6335351 baseEnd_6335351 := by
    simpa [prefixWord, tailWord_6335351, baseEnd_6335351] using wordTrace_append hprefix tailTrace_6335351
  have hstable : (prefixWord ++ tailWord_6335351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335351).length < 2 ^ (prefixWord ++ tailWord_6335351).sum := by decide
  have hdescent : baseEnd_6335351 < baseStart_6335351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335354 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 5, 5]
def baseStart_6335354 : Nat := 118140960795 + 6335354 * 2 ^ 59
def prefixEnd_6335354 : Nat := 4983230072969 + 3 ^ 40 * 6335354 * 2
def baseEnd_6335354 : Nat := 1084360572794837044013081

theorem tailTrace_6335354 : CollatzResearch.WordTrace tailWord_6335354 prefixEnd_6335354 1084360572794837044013081 := by
  unfold tailWord_6335354
  simp only [CollatzResearch.WordTrace]
  refine ⟨57767335872525481291625279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154046228993401283444334077 57767335872525481291625279)
  ·
    refine ⟨86651003808788221937437919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57767335872525481291625279 86651003808788221937437919)
    ·
      refine ⟨129976505713182332906156879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86651003808788221937437919 129976505713182332906156879)
      ·
        refine ⟨194964758569773499359235319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129976505713182332906156879 194964758569773499359235319)
        ·
          refine ⟨292447137854660249038852979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194964758569773499359235319 292447137854660249038852979)
          ·
            refine ⟨438670706781990373558279469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292447137854660249038852979 438670706781990373558279469)
            ·
              refine ⟨164501515043246390084354801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 438670706781990373558279469 164501515043246390084354801)
              ·
                refine ⟨123376136282434792563266101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164501515043246390084354801 123376136282434792563266101)
                ·
                  refine ⟨11566512776478261802806197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123376136282434792563266101 11566512776478261802806197)
                  ·
                    refine ⟨1084360572794837044013081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11566512776478261802806197 1084360572794837044013081)
                    ·
                      rfl

theorem cell23_6335354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_6335354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335354 prefixEnd_6335354 := by exact prefixLift 6335354
  have htrace : WordTrace (prefixWord ++ tailWord_6335354) baseStart_6335354 baseEnd_6335354 := by
    simpa [prefixWord, tailWord_6335354, baseEnd_6335354] using wordTrace_append hprefix tailTrace_6335354
  have hstable : (prefixWord ++ tailWord_6335354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335354).length < 2 ^ (prefixWord ++ tailWord_6335354).sum := by decide
  have hdescent : baseEnd_6335354 < baseStart_6335354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335364 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_6335364 : Nat := 118140960795 + 6335364 * 2 ^ 59
def prefixEnd_6335364 : Nat := 4983230072969 + 3 ^ 40 * 6335364 * 2
def baseEnd_6335364 : Nat := 3253086853191056092914197

theorem tailTrace_6335364 : CollatzResearch.WordTrace tailWord_6335364 prefixEnd_6335364 3253086853191056092914197 := by
  unfold tailWord_6335364
  simp only [CollatzResearch.WordTrace]
  refine ⟨115534854110032848437182573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154046472146710464582910097 115534854110032848437182573)
  ·
    refine ⟨43325570291262318163943465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115534854110032848437182573 43325570291262318163943465)
    ·
      refine ⟨32494177718446738622957599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43325570291262318163943465 32494177718446738622957599)
      ·
        refine ⟨48741266577670107934436399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32494177718446738622957599 48741266577670107934436399)
        ·
          refine ⟨73111899866505161901654599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48741266577670107934436399 73111899866505161901654599)
          ·
            refine ⟨109667849799757742852481899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73111899866505161901654599 109667849799757742852481899)
            ·
              refine ⟨164501774699636614278722849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109667849799757742852481899 164501774699636614278722849)
              ·
                refine ⟨123376331024727460709042137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164501774699636614278722849 123376331024727460709042137)
                ·
                  refine ⟨92532248268545595531781603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123376331024727460709042137 92532248268545595531781603)
                  ·
                    refine ⟨138798372402818393297672405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92532248268545595531781603 138798372402818393297672405)
                    ·
                      refine ⟨3253086853191056092914197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138798372402818393297672405 3253086853191056092914197)
                      ·
                        rfl

theorem cell23_6335364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_6335364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335364 prefixEnd_6335364 := by exact prefixLift 6335364
  have htrace : WordTrace (prefixWord ++ tailWord_6335364) baseStart_6335364 baseEnd_6335364 := by
    simpa [prefixWord, tailWord_6335364, baseEnd_6335364] using wordTrace_append hprefix tailTrace_6335364
  have hstable : (prefixWord ++ tailWord_6335364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335364).length < 2 ^ (prefixWord ++ tailWord_6335364).sum := by decide
  have hdescent : baseEnd_6335364 < baseStart_6335364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335388 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 3, 5]
def baseStart_6335388 : Nat := 118140960795 + 6335388 * 2 ^ 59
def prefixEnd_6335388 : Nat := 4983230072969 + 3 ^ 40 * 6335388 * 2
def baseEnd_6335388 : Nat := 1084366392242254666338029

theorem tailTrace_6335388 : CollatzResearch.WordTrace tailWord_6335388 prefixEnd_6335388 1084366392242254666338029 := by
  unfold tailWord_6335388
  simp only [CollatzResearch.WordTrace]
  refine ⟨115535291785989374486619409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154047055714652499315492545 115535291785989374486619409)
  ·
    refine ⟨86651468839492030864964557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115535291785989374486619409 86651468839492030864964557)
    ·
      refine ⟨32494300814809511574361709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86651468839492030864964557 32494300814809511574361709)
      ·
        refine ⟨12185362805553566840385641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32494300814809511574361709 12185362805553566840385641)
        ·
          refine ⟨9139022104165175130289231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12185362805553566840385641 9139022104165175130289231)
          ·
            refine ⟨13708533156247762695433847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9139022104165175130289231 13708533156247762695433847)
            ·
              refine ⟨20562799734371644043150771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13708533156247762695433847 20562799734371644043150771)
              ·
                refine ⟨30844199601557466064726157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20562799734371644043150771 30844199601557466064726157)
                ·
                  refine ⟨11566574850584049774272309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30844199601557466064726157 11566574850584049774272309)
                  ·
                    refine ⟨1084366392242254666338029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11566574850584049774272309 1084366392242254666338029)
                    ·
                      rfl

theorem cell23_6335388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_6335388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335388 prefixEnd_6335388 := by exact prefixLift 6335388
  have htrace : WordTrace (prefixWord ++ tailWord_6335388) baseStart_6335388 baseEnd_6335388 := by
    simpa [prefixWord, tailWord_6335388, baseEnd_6335388] using wordTrace_append hprefix tailTrace_6335388
  have hstable : (prefixWord ++ tailWord_6335388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335388).length < 2 ^ (prefixWord ++ tailWord_6335388).sum := by decide
  have hdescent : baseEnd_6335388 < baseStart_6335388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335412 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_6335412 : Nat := 118140960795 + 6335412 * 2 ^ 59
def prefixEnd_6335412 : Nat := 4983230072969 + 3 ^ 40 * 6335412 * 2
def baseEnd_6335412 : Nat := 3253111500262471905113977

theorem tailTrace_6335412 : CollatzResearch.WordTrace tailWord_6335412 prefixEnd_6335412 3253111500262471905113977 := by
  unfold tailWord_6335412
  simp only [CollatzResearch.WordTrace]
  refine ⟨115535729461945900536056245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154047639282594534048074993 115535729461945900536056245)
  ·
    refine ⟨10831474637057428175255273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115535729461945900536056245 10831474637057428175255273)
    ·
      refine ⟨8123605977793071131441455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10831474637057428175255273 8123605977793071131441455)
      ·
        refine ⟨12185408966689606697162183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8123605977793071131441455 12185408966689606697162183)
        ·
          refine ⟨18278113450034410045743275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12185408966689606697162183 18278113450034410045743275)
          ·
            refine ⟨27417170175051615068614913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18278113450034410045743275 27417170175051615068614913)
            ·
              refine ⟨20562877631288711301461185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27417170175051615068614913 20562877631288711301461185)
              ·
                refine ⟨15422158223466533476095889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20562877631288711301461185 15422158223466533476095889)
                ·
                  refine ⟨11566618667599900107071917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15422158223466533476095889 11566618667599900107071917)
                  ·
                    refine ⟨4337482000349962540151969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11566618667599900107071917 4337482000349962540151969)
                    ·
                      refine ⟨3253111500262471905113977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4337482000349962540151969 3253111500262471905113977)
                      ·
                        rfl

theorem cell23_6335412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_6335412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335412 prefixEnd_6335412 := by exact prefixLift 6335412
  have htrace : WordTrace (prefixWord ++ tailWord_6335412) baseStart_6335412 baseEnd_6335412 := by
    simpa [prefixWord, tailWord_6335412, baseEnd_6335412] using wordTrace_append hprefix tailTrace_6335412
  have hstable : (prefixWord ++ tailWord_6335412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335412).length < 2 ^ (prefixWord ++ tailWord_6335412).sum := by decide
  have hdescent : baseEnd_6335412 < baseStart_6335412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335418 : List Nat := [3, 1, 1, 1, 2, 1, 6, 2, 2, 4]
def baseStart_6335418 : Nat := 118140960795 + 6335418 * 2 ^ 59
def prefixEnd_6335418 : Nat := 4983230072969 + 3 ^ 40 * 6335418 * 2
def baseEnd_6335418 : Nat := 1084371527048799627212983

theorem tailTrace_6335418 : CollatzResearch.WordTrace tailWord_6335418 prefixEnd_6335418 1084371527048799627212983 := by
  unfold tailWord_6335418
  simp only [CollatzResearch.WordTrace]
  refine ⟨57767919440467516024207727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154047785174580042731220605 57767919440467516024207727)
  ·
    refine ⟨86651879160701274036311591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57767919440467516024207727 86651879160701274036311591)
    ·
      refine ⟨129977818741051911054467387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86651879160701274036311591 129977818741051911054467387)
      ·
        refine ⟨194966728111577866581701081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129977818741051911054467387 194966728111577866581701081)
        ·
          refine ⟨146225046083683399936275811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194966728111577866581701081 146225046083683399936275811)
          ·
            refine ⟨219337569125525099904413717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146225046083683399936275811 219337569125525099904413717)
            ·
              refine ⟨10281448552758989058019393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 219337569125525099904413717 10281448552758989058019393)
              ·
                refine ⟨7711086414569241793514545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10281448552758989058019393 7711086414569241793514545)
                ·
                  refine ⟨5783314810926931345135909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7711086414569241793514545 5783314810926931345135909)
                  ·
                    refine ⟨1084371527048799627212983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5783314810926931345135909 1084371527048799627212983)
                    ·
                      rfl

theorem cell23_6335418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_6335418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335418 prefixEnd_6335418 := by exact prefixLift 6335418
  have htrace : WordTrace (prefixWord ++ tailWord_6335418) baseStart_6335418 baseEnd_6335418 := by
    simpa [prefixWord, tailWord_6335418, baseEnd_6335418] using wordTrace_append hprefix tailTrace_6335418
  have hstable : (prefixWord ++ tailWord_6335418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335418).length < 2 ^ (prefixWord ++ tailWord_6335418).sum := by decide
  have hdescent : baseEnd_6335418 < baseStart_6335418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335438 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_6335438 : Nat := 118140960795 + 6335438 * 2 ^ 59
def prefixEnd_6335438 : Nat := 4983230072969 + 3 ^ 40 * 6335438 * 2
def baseEnd_6335438 : Nat := 3253124850759488803388857

theorem tailTrace_6335438 : CollatzResearch.WordTrace tailWord_6335438 prefixEnd_6335438 3253124850759488803388857 := by
  unfold tailWord_6335438
  simp only [CollatzResearch.WordTrace]
  refine ⟨28884050902724700939069871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154048271481198405008372645 28884050902724700939069871)
  ·
    refine ⟨43326076354087051408604807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28884050902724700939069871 43326076354087051408604807)
    ·
      refine ⟨64989114531130577112907211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43326076354087051408604807 64989114531130577112907211)
      ·
        refine ⟨97483671796695865669360817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64989114531130577112907211 97483671796695865669360817)
        ·
          refine ⟨73112753847521899252020613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97483671796695865669360817 73112753847521899252020613)
          ·
            refine ⟨13708641346410356109753865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73112753847521899252020613 13708641346410356109753865)
            ·
              refine ⟨10281481009807767082315399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13708641346410356109753865 10281481009807767082315399)
              ·
                refine ⟨15422221514711650623473099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10281481009807767082315399 15422221514711650623473099)
                ·
                  refine ⟨23133332272067475935209649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15422221514711650623473099 23133332272067475935209649)
                  ·
                    refine ⟨17349999204050606951407237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23133332272067475935209649 17349999204050606951407237)
                    ·
                      refine ⟨3253124850759488803388857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17349999204050606951407237 3253124850759488803388857)
                      ·
                        rfl

theorem cell23_6335438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_6335438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335438 prefixEnd_6335438 := by exact prefixLift 6335438
  have htrace : WordTrace (prefixWord ++ tailWord_6335438) baseStart_6335438 baseEnd_6335438 := by
    simpa [prefixWord, tailWord_6335438, baseEnd_6335438] using wordTrace_append hprefix tailTrace_6335438
  have hstable : (prefixWord ++ tailWord_6335438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335438).length < 2 ^ (prefixWord ++ tailWord_6335438).sum := by decide
  have hdescent : baseEnd_6335438 < baseStart_6335438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335442 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_6335442 : Nat := 118140960795 + 6335442 * 2 ^ 59
def prefixEnd_6335442 : Nat := 4983230072969 + 3 ^ 40 * 6335442 * 2
def baseEnd_6335442 : Nat := 3253126904682106787738839

theorem tailTrace_6335442 : CollatzResearch.WordTrace tailWord_6335442 prefixEnd_6335442 3253126904682106787738839 := by
  unfold tailWord_6335442
  simp only [CollatzResearch.WordTrace]
  refine ⟨57768138278445779048926145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154048368742522077463803053 57768138278445779048926145)
  ·
    refine ⟨43326103708834334286694609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57768138278445779048926145 43326103708834334286694609)
    ·
      refine ⟨32494577781625750715020957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43326103708834334286694609 32494577781625750715020957)
      ·
        refine ⟨12185466668109656518132859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32494577781625750715020957 12185466668109656518132859)
        ·
          refine ⟨18278200002164484777199289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12185466668109656518132859 18278200002164484777199289)
          ·
            refine ⟨13708650001623363582899467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18278200002164484777199289 13708650001623363582899467)
            ·
              refine ⟨20562975002435045374349201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13708650001623363582899467 20562975002435045374349201)
              ·
                refine ⟨15422231251826284030761901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20562975002435045374349201 15422231251826284030761901)
                ·
                  refine ⟨5783336719434856511535713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15422231251826284030761901 5783336719434856511535713)
                  ·
                    refine ⟨4337502539576142383651785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5783336719434856511535713 4337502539576142383651785)
                    ·
                      refine ⟨3253126904682106787738839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4337502539576142383651785 3253126904682106787738839)
                      ·
                        rfl

theorem cell23_6335442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_6335442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335442 prefixEnd_6335442 := by exact prefixLift 6335442
  have htrace : WordTrace (prefixWord ++ tailWord_6335442) baseStart_6335442 baseEnd_6335442 := by
    simpa [prefixWord, tailWord_6335442, baseEnd_6335442] using wordTrace_append hprefix tailTrace_6335442
  have hstable : (prefixWord ++ tailWord_6335442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335442).length < 2 ^ (prefixWord ++ tailWord_6335442).sum := by decide
  have hdescent : baseEnd_6335442 < baseStart_6335442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335502 : List Nat := [4, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2]
def baseStart_6335502 : Nat := 118140960795 + 6335502 * 2 ^ 59
def prefixEnd_6335502 : Nat := 4983230072969 + 3 ^ 40 * 6335502 * 2
def baseEnd_6335502 : Nat := 3253157713521376552988563

theorem tailTrace_6335502 : CollatzResearch.WordTrace tailWord_6335502 prefixEnd_6335502 3253157713521376552988563 := by
  unfold tailWord_6335502
  simp only [CollatzResearch.WordTrace]
  refine ⟨28884342686695718305361095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154049827662377164295259173 28884342686695718305361095)
  ·
    refine ⟨43326514030043577458041643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28884342686695718305361095 43326514030043577458041643)
    ·
      refine ⟨64989771045065366187062465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43326514030043577458041643 64989771045065366187062465)
      ·
        refine ⟨48742328283799024640296849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64989771045065366187062465 48742328283799024640296849)
        ·
          refine ⟨36556746212849268480222637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48742328283799024640296849 36556746212849268480222637)
          ·
            refine ⟨13708779829818475680083489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36556746212849268480222637 13708779829818475680083489)
            ·
              refine ⟨10281584872363856760062617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13708779829818475680083489 10281584872363856760062617)
              ·
                refine ⟨7711188654272892570046963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10281584872363856760062617 7711188654272892570046963)
                ·
                  refine ⟨11566782981409338855070445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7711188654272892570046963 11566782981409338855070445)
                  ·
                    refine ⟨4337543618028502070651417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11566782981409338855070445 4337543618028502070651417)
                    ·
                      refine ⟨3253157713521376552988563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4337543618028502070651417 3253157713521376552988563)
                      ·
                        rfl

theorem cell23_6335502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_6335502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335502 prefixEnd_6335502 := by exact prefixLift 6335502
  have htrace : WordTrace (prefixWord ++ tailWord_6335502) baseStart_6335502 baseEnd_6335502 := by
    simpa [prefixWord, tailWord_6335502, baseEnd_6335502] using wordTrace_append hprefix tailTrace_6335502
  have hstable : (prefixWord ++ tailWord_6335502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335502).length < 2 ^ (prefixWord ++ tailWord_6335502).sum := by decide
  have hdescent : baseEnd_6335502 < baseStart_6335502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335549 : List Nat := [1, 4, 1, 3, 1, 2, 4, 1, 2, 2, 2]
def baseStart_6335549 : Nat := 118140960795 + 6335549 * 2 ^ 59
def prefixEnd_6335549 : Nat := 4983230072969 + 3 ^ 40 * 6335549 * 2
def baseEnd_6335549 : Nat := 3253181847112137869100847

theorem tailTrace_6335549 : CollatzResearch.WordTrace tailWord_6335549 prefixEnd_6335549 3253181847112137869100847 := by
  unfold tailWord_6335549
  simp only [CollatzResearch.WordTrace]
  refine ⟨231076455724395473469849701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154050970482930315646566467 231076455724395473469849701)
  ·
    refine ⟨43326835448324151275596819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231076455724395473469849701 43326835448324151275596819)
    ·
      refine ⟨64990253172486226913395229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43326835448324151275596819 64990253172486226913395229)
      ·
        refine ⟨24371344939682335092523211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64990253172486226913395229 24371344939682335092523211)
        ·
          refine ⟨36557017409523502638784817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24371344939682335092523211 36557017409523502638784817)
          ·
            refine ⟨27417763057142626979088613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36557017409523502638784817 27417763057142626979088613)
            ·
              refine ⟨5140830573214242558579115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27417763057142626979088613 5140830573214242558579115)
              ·
                refine ⟨7711245859821363837868673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5140830573214242558579115 7711245859821363837868673)
                ·
                  refine ⟨5783434394866022878401505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7711245859821363837868673 5783434394866022878401505)
                  ·
                    refine ⟨4337575796149517158801129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5783434394866022878401505 4337575796149517158801129)
                    ·
                      refine ⟨3253181847112137869100847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4337575796149517158801129 3253181847112137869100847)
                      ·
                        rfl

theorem cell23_6335549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_6335549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335549 prefixEnd_6335549 := by exact prefixLift 6335549
  have htrace : WordTrace (prefixWord ++ tailWord_6335549) baseStart_6335549 baseEnd_6335549 := by
    simpa [prefixWord, tailWord_6335549, baseEnd_6335549] using wordTrace_append hprefix tailTrace_6335549
  have hstable : (prefixWord ++ tailWord_6335549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335549).length < 2 ^ (prefixWord ++ tailWord_6335549).sum := by decide
  have hdescent : baseEnd_6335549 < baseStart_6335549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335551 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 6, 5]
def baseStart_6335551 : Nat := 118140960795 + 6335551 * 2 ^ 59
def prefixEnd_6335551 : Nat := 4983230072969 + 3 ^ 40 * 6335551 * 2
def baseEnd_6335551 : Nat := 1084394291357815620425279

theorem tailTrace_6335551 : CollatzResearch.WordTrace tailWord_6335551 prefixEnd_6335551 1084394291357815620425279 := by
  unfold tailWord_6335551
  simp only [CollatzResearch.WordTrace]
  refine ⟨231076528670388227811422507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154051019113592151874281671 231076528670388227811422507)
  ·
    refine ⟨346614793005582341717133761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231076528670388227811422507 346614793005582341717133761)
    ·
      refine ⟨259961094754186756287850321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346614793005582341717133761 259961094754186756287850321)
      ·
        refine ⟨194970821065640067215887741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259961094754186756287850321 194970821065640067215887741)
        ·
          refine ⟨73114057899615025205957903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194970821065640067215887741 73114057899615025205957903)
          ·
            refine ⟨109671086849422537808936855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73114057899615025205957903 109671086849422537808936855)
            ·
              refine ⟨164506630274133806713405283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109671086849422537808936855 164506630274133806713405283)
              ·
                refine ⟨246759945411200710070107925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164506630274133806713405283 246759945411200710070107925)
                ·
                  refine ⟨11566872441150033284536309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 246759945411200710070107925 11566872441150033284536309)
                  ·
                    refine ⟨1084394291357815620425279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11566872441150033284536309 1084394291357815620425279)
                    ·
                      rfl

theorem cell23_6335551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 5].length) (baseStart_6335551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335551 prefixEnd_6335551 := by exact prefixLift 6335551
  have htrace : WordTrace (prefixWord ++ tailWord_6335551) baseStart_6335551 baseEnd_6335551 := by
    simpa [prefixWord, tailWord_6335551, baseEnd_6335551] using wordTrace_append hprefix tailTrace_6335551
  have hstable : (prefixWord ++ tailWord_6335551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335551).length < 2 ^ (prefixWord ++ tailWord_6335551).sum := by decide
  have hdescent : baseEnd_6335551 < baseStart_6335551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335601 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_6335601 : Nat := 118140960795 + 6335601 * 2 ^ 59
def prefixEnd_6335601 : Nat := 4983230072969 + 3 ^ 40 * 6335601 * 2
def baseEnd_6335601 : Nat := 3253208548106171665650607

theorem tailTrace_6335601 : CollatzResearch.WordTrace tailWord_6335601 prefixEnd_6335601 3253208548106171665650607 := by
  unfold tailWord_6335601
  simp only [CollatzResearch.WordTrace]
  refine ⟨231078352320207086350742657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154052234880138057567161771 231078352320207086350742657)
  ·
    refine ⟨173308764240155314763056993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231078352320207086350742657 173308764240155314763056993)
    ·
      refine ⟨129981573180116486072292745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173308764240155314763056993 129981573180116486072292745)
      ·
        refine ⟨97486179885087364554219559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129981573180116486072292745 97486179885087364554219559)
        ·
          refine ⟨146229269827631046831329339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97486179885087364554219559 146229269827631046831329339)
          ·
            refine ⟨219343904741446570246994009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146229269827631046831329339 219343904741446570246994009)
            ·
              refine ⟨164507928556084927685245507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219343904741446570246994009 164507928556084927685245507)
              ·
                refine ⟨246761892834127391527868261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164507928556084927685245507 246761892834127391527868261)
                ·
                  refine ⟨46267854906398885911475299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246761892834127391527868261 46267854906398885911475299)
                  ·
                    refine ⟨69401782359598328867212949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46267854906398885911475299 69401782359598328867212949)
                    ·
                      refine ⟨3253208548106171665650607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69401782359598328867212949 3253208548106171665650607)
                      ·
                        rfl

theorem cell23_6335601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_6335601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335601 prefixEnd_6335601 := by exact prefixLift 6335601
  have htrace : WordTrace (prefixWord ++ tailWord_6335601) baseStart_6335601 baseEnd_6335601 := by
    simpa [prefixWord, tailWord_6335601, baseEnd_6335601] using wordTrace_append hprefix tailTrace_6335601
  have hstable : (prefixWord ++ tailWord_6335601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335601).length < 2 ^ (prefixWord ++ tailWord_6335601).sum := by decide
  have hdescent : baseEnd_6335601 < baseStart_6335601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335608 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 4, 2, 3]
def baseStart_6335608 : Nat := 118140960795 + 6335608 * 2 ^ 59
def prefixEnd_6335608 : Nat := 4983230072969 + 3 ^ 40 * 6335608 * 2
def baseEnd_6335608 : Nat := 3253212142470753138263075

theorem tailTrace_6335608 : CollatzResearch.WordTrace tailWord_6335608 prefixEnd_6335608 3253212142470753138263075 := by
  unfold tailWord_6335608
  simp only [CollatzResearch.WordTrace]
  refine ⟨115539303815590863273123739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154052405087454484364164985 115539303815590863273123739)
  ·
    refine ⟨173308955723386294909685609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115539303815590863273123739 173308955723386294909685609)
    ·
      refine ⟨129981716792539721182264207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173308955723386294909685609 129981716792539721182264207)
      ·
        refine ⟨194972575188809581773396311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129981716792539721182264207 194972575188809581773396311)
        ·
          refine ⟨292458862783214372660094467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194972575188809581773396311 292458862783214372660094467)
          ·
            refine ⟨438688294174821558990141701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292458862783214372660094467 438688294174821558990141701)
            ·
              refine ⟨82254055157779042310651569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 438688294174821558990141701 82254055157779042310651569)
              ·
                refine ⟨61690541368334281732988677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82254055157779042310651569 61690541368334281732988677)
                ·
                  refine ⟨11566976506562677824935377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61690541368334281732988677 11566976506562677824935377)
                  ·
                    refine ⟨8675232379922008368701533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11566976506562677824935377 8675232379922008368701533)
                    ·
                      refine ⟨3253212142470753138263075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8675232379922008368701533 3253212142470753138263075)
                      ·
                        rfl

theorem cell23_6335608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_6335608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335608 prefixEnd_6335608 := by exact prefixLift 6335608
  have htrace : WordTrace (prefixWord ++ tailWord_6335608) baseStart_6335608 baseEnd_6335608 := by
    simpa [prefixWord, tailWord_6335608, baseEnd_6335608] using wordTrace_append hprefix tailTrace_6335608
  have hstable : (prefixWord ++ tailWord_6335608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335608).length < 2 ^ (prefixWord ++ tailWord_6335608).sum := by decide
  have hdescent : baseEnd_6335608 < baseStart_6335608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335625 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 2, 2, 3]
def baseStart_6335625 : Nat := 118140960795 + 6335625 * 2 ^ 59
def prefixEnd_6335625 : Nat := 4983230072969 + 3 ^ 40 * 6335625 * 2
def baseEnd_6335625 : Nat := 3253220871641879571750497

theorem tailTrace_6335625 : CollatzResearch.WordTrace tailWord_6335625 prefixEnd_6335625 3253220871641879571750497 := by
  unfold tailWord_6335625
  simp only [CollatzResearch.WordTrace]
  refine ⟨231079227672120138449616329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154052818448080092299744219 231079227672120138449616329)
  ·
    refine ⟨173309420754090103837212247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231079227672120138449616329 173309420754090103837212247)
    ·
      refine ⟨259964131131135155755818371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173309420754090103837212247 259964131131135155755818371)
      ·
        refine ⟨389946196696702733633727557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259964131131135155755818371 389946196696702733633727557)
        ·
          refine ⟨73114911880631762556323917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389946196696702733633727557 73114911880631762556323917)
          ·
            refine ⟨27418091955236910958621469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73114911880631762556323917 27418091955236910958621469)
            ·
              refine ⟨10281784483213841609483051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27418091955236910958621469 10281784483213841609483051)
              ·
                refine ⟨15422676724820762414224577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10281784483213841609483051 15422676724820762414224577)
                ·
                  refine ⟨11567007543615571810668433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15422676724820762414224577 11567007543615571810668433)
                  ·
                    refine ⟨8675255657711678858001325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11567007543615571810668433 8675255657711678858001325)
                    ·
                      refine ⟨3253220871641879571750497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8675255657711678858001325 3253220871641879571750497)
                      ·
                        rfl

theorem cell23_6335625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 2, 3].length) (baseStart_6335625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335625 prefixEnd_6335625 := by exact prefixLift 6335625
  have htrace : WordTrace (prefixWord ++ tailWord_6335625) baseStart_6335625 baseEnd_6335625 := by
    simpa [prefixWord, tailWord_6335625, baseEnd_6335625] using wordTrace_append hprefix tailTrace_6335625
  have hstable : (prefixWord ++ tailWord_6335625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335625).length < 2 ^ (prefixWord ++ tailWord_6335625).sum := by decide
  have hdescent : baseEnd_6335625 < baseStart_6335625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335688 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 1, 6]
def baseStart_6335688 : Nat := 118140960795 + 6335688 * 2 ^ 59
def prefixEnd_6335688 : Nat := 4983230072969 + 3 ^ 40 * 6335688 * 2
def baseEnd_6335688 : Nat := 1084417740307704275087569

theorem tailTrace_6335688 : CollatzResearch.WordTrace tailWord_6335688 prefixEnd_6335688 1084417740307704275087569 := by
  unfold tailWord_6335688
  simp only [CollatzResearch.WordTrace]
  refine ⟨115540762735445950104579859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154054350313927933472773145 115540762735445950104579859)
  ·
    refine ⟨173311144103168925156869789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115540762735445950104579859 173311144103168925156869789)
    ·
      refine ⟨64991679038688346933826171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173311144103168925156869789 64991679038688346933826171)
      ·
        refine ⟨97487518558032520400739257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64991679038688346933826171 97487518558032520400739257)
        ·
          refine ⟨73115638918524390300554443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97487518558032520400739257 73115638918524390300554443)
          ·
            refine ⟨109673458377786585450831665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73115638918524390300554443 109673458377786585450831665)
            ·
              refine ⟨82255093783339939088123749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109673458377786585450831665 82255093783339939088123749)
              ·
                refine ⟨15422830084376238579023203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82255093783339939088123749 15422830084376238579023203)
                ·
                  refine ⟨23134245126564357868534805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15422830084376238579023203 23134245126564357868534805)
                  ·
                    refine ⟨1084417740307704275087569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23134245126564357868534805 1084417740307704275087569)
                    ·
                      rfl

theorem cell23_6335688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_6335688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335688 prefixEnd_6335688 := by exact prefixLift 6335688
  have htrace : WordTrace (prefixWord ++ tailWord_6335688) baseStart_6335688 baseEnd_6335688 := by
    simpa [prefixWord, tailWord_6335688, baseEnd_6335688] using wordTrace_append hprefix tailTrace_6335688
  have hstable : (prefixWord ++ tailWord_6335688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335688).length < 2 ^ (prefixWord ++ tailWord_6335688).sum := by decide
  have hdescent : baseEnd_6335688 < baseStart_6335688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335705 : List Nat := [1, 2, 1, 2, 3, 1, 1, 6, 2, 4]
def baseStart_6335705 : Nat := 118140960795 + 6335705 * 2 ^ 59
def prefixEnd_6335705 : Nat := 4983230072969 + 3 ^ 40 * 6335705 * 2
def baseEnd_6335705 : Nat := 1084420650031413086250043

theorem tailTrace_6335705 : CollatzResearch.WordTrace tailWord_6335705 prefixEnd_6335705 1084420650031413086250043 := by
  unfold tailWord_6335705
  simp only [CollatzResearch.WordTrace]
  refine ⟨231082145511830312112528569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154054763674553541408352379 231082145511830312112528569)
  ·
    refine ⟨173311609133872734084396427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231082145511830312112528569 173311609133872734084396427)
    ·
      refine ⟨259967413700809101126594641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173311609133872734084396427 259967413700809101126594641)
      ·
        refine ⟨194975560275606825844945981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259967413700809101126594641 194975560275606825844945981)
        ·
          refine ⟨73115835103352559691854743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194975560275606825844945981 73115835103352559691854743)
          ·
            refine ⟨109673752655028839537782115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73115835103352559691854743 109673752655028839537782115)
            ·
              refine ⟨164510628982543259306673173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109673752655028839537782115 164510628982543259306673173)
              ·
                refine ⟨7711435733556715280000305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164510628982543259306673173 7711435733556715280000305)
                ·
                  refine ⟨5783576800167536460000229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7711435733556715280000305 5783576800167536460000229)
                  ·
                    refine ⟨1084420650031413086250043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5783576800167536460000229 1084420650031413086250043)
                    ·
                      rfl

theorem cell23_6335705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 4].length) (baseStart_6335705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335705 prefixEnd_6335705 := by exact prefixLift 6335705
  have htrace : WordTrace (prefixWord ++ tailWord_6335705) baseStart_6335705 baseEnd_6335705 := by
    simpa [prefixWord, tailWord_6335705, baseEnd_6335705] using wordTrace_append hprefix tailTrace_6335705
  have hstable : (prefixWord ++ tailWord_6335705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335705).length < 2 ^ (prefixWord ++ tailWord_6335705).sum := by decide
  have hdescent : baseEnd_6335705 < baseStart_6335705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335722 : List Nat := [3, 1, 3, 1, 1, 4, 1, 3, 2, 4]
def baseStart_6335722 : Nat := 118140960795 + 6335722 * 2 ^ 59
def prefixEnd_6335722 : Nat := 4983230072969 + 3 ^ 40 * 6335722 * 2
def baseEnd_6335722 : Nat := 1084423559755121897412517

theorem tailTrace_6335722 : CollatzResearch.WordTrace tailWord_6335722 prefixEnd_6335722 1084423559755121897412517 := by
  unfold tailWord_6335722
  simp only [CollatzResearch.WordTrace]
  refine ⟨57770691388192181003974355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154055177035179149343931613 57770691388192181003974355)
  ·
    refine ⟨86656037082288271505961533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57770691388192181003974355 86656037082288271505961533)
    ·
      refine ⟨32496013905858101814735575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86656037082288271505961533 32496013905858101814735575)
      ·
        refine ⟨48744020858787152722103363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32496013905858101814735575 48744020858787152722103363)
        ·
          refine ⟨73116031288180729083155045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48744020858787152722103363 73116031288180729083155045)
          ·
            refine ⟨13709255866533886703091571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73116031288180729083155045 13709255866533886703091571)
            ·
              refine ⟨20563883799800830054637357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13709255866533886703091571 20563883799800830054637357)
              ·
                refine ⟨7711456424925311270489009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20563883799800830054637357 7711456424925311270489009)
                ·
                  refine ⟨5783592318693983452866757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7711456424925311270489009 5783592318693983452866757)
                  ·
                    refine ⟨1084423559755121897412517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5783592318693983452866757 1084423559755121897412517)
                    ·
                      rfl

theorem cell23_6335722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_6335722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335722 prefixEnd_6335722 := by exact prefixLift 6335722
  have htrace : WordTrace (prefixWord ++ tailWord_6335722) baseStart_6335722 baseEnd_6335722 := by
    simpa [prefixWord, tailWord_6335722, baseEnd_6335722] using wordTrace_append hprefix tailTrace_6335722
  have hstable : (prefixWord ++ tailWord_6335722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335722).length < 2 ^ (prefixWord ++ tailWord_6335722).sum := by decide
  have hdescent : baseEnd_6335722 < baseStart_6335722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335725 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_6335725 : Nat := 118140960795 + 6335725 * 2 ^ 59
def prefixEnd_6335725 : Nat := 4983230072969 + 3 ^ 40 * 6335725 * 2
def baseEnd_6335725 : Nat := 3253272219707329180500037

theorem tailTrace_6335725 : CollatzResearch.WordTrace tailWord_6335725 prefixEnd_6335725 3253272219707329180500037 := by
  unfold tailWord_6335725
  simp only [CollatzResearch.WordTrace]
  refine ⟨231082874971757855528256629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154055249981171903685504419 231082874971757855528256629)
  ·
    refine ⟨21664019528602298955774059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231082874971757855528256629 21664019528602298955774059)
    ·
      refine ⟨32496029292903448433661089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21664019528602298955774059 32496029292903448433661089)
      ·
        refine ⟨24372021969677586325245817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32496029292903448433661089 24372021969677586325245817)
        ·
          refine ⟨18279016477258189743934363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24372021969677586325245817 18279016477258189743934363)
          ·
            refine ⟨27418524715887284615901545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18279016477258189743934363 27418524715887284615901545)
            ·
              refine ⟨20563893536915463461926159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27418524715887284615901545 20563893536915463461926159)
              ·
                refine ⟨30845840305373195192889239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20563893536915463461926159 30845840305373195192889239)
                ·
                  refine ⟨46268760458059792789333859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30845840305373195192889239 46268760458059792789333859)
                  ·
                    refine ⟨69403140687089689184000789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46268760458059792789333859 69403140687089689184000789)
                    ·
                      refine ⟨3253272219707329180500037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69403140687089689184000789 3253272219707329180500037)
                      ·
                        rfl

theorem cell23_6335725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_6335725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335725 prefixEnd_6335725 := by exact prefixLift 6335725
  have htrace : WordTrace (prefixWord ++ tailWord_6335725) baseStart_6335725 baseEnd_6335725 := by
    simpa [prefixWord, tailWord_6335725, baseEnd_6335725] using wordTrace_append hprefix tailTrace_6335725
  have hstable : (prefixWord ++ tailWord_6335725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335725).length < 2 ^ (prefixWord ++ tailWord_6335725).sum := by decide
  have hdescent : baseEnd_6335725 < baseStart_6335725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335742 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_6335742 : Nat := 118140960795 + 6335742 * 2 ^ 59
def prefixEnd_6335742 : Nat := 4983230072969 + 3 ^ 40 * 6335742 * 2
def baseEnd_6335742 : Nat := 3253280948878455613987459

theorem tailTrace_6335742 : CollatzResearch.WordTrace tailWord_6335742 prefixEnd_6335742 3253280948878455613987459 := by
  unfold tailWord_6335742
  simp only [CollatzResearch.WordTrace]
  refine ⟨28885436876587033428953185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154055663341797511621083653 28885436876587033428953185)
  ·
    refine ⟨21664077657440275071714889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28885436876587033428953185 21664077657440275071714889)
    ·
      refine ⟨16248058243080206303786167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21664077657440275071714889 16248058243080206303786167)
      ·
        refine ⟨24372087364620309455679251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16248058243080206303786167 24372087364620309455679251)
        ·
          refine ⟨36558131046930464183518877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24372087364620309455679251 36558131046930464183518877)
          ·
            refine ⟨13709299142598924068819579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36558131046930464183518877 13709299142598924068819579)
            ·
              refine ⟨20563948713898386103229369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13709299142598924068819579 20563948713898386103229369)
              ·
                refine ⟨15422961535423789577422027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20563948713898386103229369 15422961535423789577422027)
                ·
                  refine ⟨23134442303135684366133041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15422961535423789577422027 23134442303135684366133041)
                  ·
                    refine ⟨17350831727351763274599781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23134442303135684366133041 17350831727351763274599781)
                    ·
                      refine ⟨3253280948878455613987459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17350831727351763274599781 3253280948878455613987459)
                      ·
                        rfl

theorem cell23_6335742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_6335742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335742 prefixEnd_6335742 := by exact prefixLift 6335742
  have htrace : WordTrace (prefixWord ++ tailWord_6335742) baseStart_6335742 baseEnd_6335742 := by
    simpa [prefixWord, tailWord_6335742, baseEnd_6335742] using wordTrace_append hprefix tailTrace_6335742
  have hstable : (prefixWord ++ tailWord_6335742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335742).length < 2 ^ (prefixWord ++ tailWord_6335742).sum := by decide
  have hdescent : baseEnd_6335742 < baseStart_6335742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335745 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_6335745 : Nat := 118140960795 + 6335745 * 2 ^ 59
def prefixEnd_6335745 : Nat := 4983230072969 + 3 ^ 40 * 6335745 * 2
def baseEnd_6335745 : Nat := 3253282489320419102249945

theorem tailTrace_6335745 : CollatzResearch.WordTrace tailWord_6335745 prefixEnd_6335745 3253282489320419102249945 := by
  unfold tailWord_6335745
  simp only [CollatzResearch.WordTrace]
  refine ⟨231083604431685398943984689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154055736287790265962656459 231083604431685398943984689)
  ·
    refine ⟨173312703323764049207988517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231083604431685398943984689 173312703323764049207988517)
    ·
      refine ⟨32496131873205759226497847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173312703323764049207988517 32496131873205759226497847)
      ·
        refine ⟨48744197809808638839746771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32496131873205759226497847 48744197809808638839746771)
        ·
          refine ⟨73116296714712958259620157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48744197809808638839746771 73116296714712958259620157)
          ·
            refine ⟨27418611268017359347357559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73116296714712958259620157 27418611268017359347357559)
            ·
              refine ⟨41127916902026039021036339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27418611268017359347357559 41127916902026039021036339)
              ·
                refine ⟨61691875353039058531554509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41127916902026039021036339 61691875353039058531554509)
                ·
                  refine ⟨23134453257389646949332941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61691875353039058531554509 23134453257389646949332941)
                  ·
                    refine ⟨8675419971521117605999853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23134453257389646949332941 8675419971521117605999853)
                    ·
                      refine ⟨3253282489320419102249945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8675419971521117605999853 3253282489320419102249945)
                      ·
                        rfl

theorem cell23_6335745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_6335745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335745 prefixEnd_6335745 := by exact prefixLift 6335745
  have htrace : WordTrace (prefixWord ++ tailWord_6335745) baseStart_6335745 baseEnd_6335745 := by
    simpa [prefixWord, tailWord_6335745, baseEnd_6335745] using wordTrace_append hprefix tailTrace_6335745
  have hstable : (prefixWord ++ tailWord_6335745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335745).length < 2 ^ (prefixWord ++ tailWord_6335745).sum := by decide
  have hdescent : baseEnd_6335745 < baseStart_6335745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335746 : List Nat := [3, 4, 1, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_6335746 : Nat := 118140960795 + 6335746 * 2 ^ 59
def prefixEnd_6335746 : Nat := 4983230072969 + 3 ^ 40 * 6335746 * 2
def baseEnd_6335746 : Nat := 3253283002801073598337441

theorem tailTrace_6335746 : CollatzResearch.WordTrace tailWord_6335746 prefixEnd_6335746 3253283002801073598337441 := by
  unfold tailWord_6335746
  simp only [CollatzResearch.WordTrace]
  refine ⟨57770910226170444028692773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154055760603121184076514061 57770910226170444028692773)
  ·
    refine ⟨10832045667406958255379895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57770910226170444028692773 10832045667406958255379895)
    ·
      refine ⟨16248068501110437383069843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10832045667406958255379895 16248068501110437383069843)
      ·
        refine ⟨24372102751665656074604765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16248068501110437383069843 24372102751665656074604765)
        ·
          refine ⟨9139538531874621027976787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24372102751665656074604765 9139538531874621027976787)
          ·
            refine ⟨13709307797811931541965181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9139538531874621027976787 13709307797811931541965181)
            ·
              refine ⟨5140990424179474328236943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13709307797811931541965181 5140990424179474328236943)
              ·
                refine ⟨7711485636269211492355415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5140990424179474328236943 7711485636269211492355415)
                ·
                  refine ⟨11567228454403817238533123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7711485636269211492355415 11567228454403817238533123)
                  ·
                    refine ⟨17350842681605725857799685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11567228454403817238533123 17350842681605725857799685)
                    ·
                      refine ⟨3253283002801073598337441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17350842681605725857799685 3253283002801073598337441)
                      ·
                        rfl

theorem cell23_6335746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_6335746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335746 prefixEnd_6335746 := by exact prefixLift 6335746
  have htrace : WordTrace (prefixWord ++ tailWord_6335746) baseStart_6335746 baseEnd_6335746 := by
    simpa [prefixWord, tailWord_6335746, baseEnd_6335746] using wordTrace_append hprefix tailTrace_6335746
  have hstable : (prefixWord ++ tailWord_6335746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335746).length < 2 ^ (prefixWord ++ tailWord_6335746).sum := by decide
  have hdescent : baseEnd_6335746 < baseStart_6335746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335772 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_6335772 : Nat := 118140960795 + 6335772 * 2 ^ 59
def prefixEnd_6335772 : Nat := 4983230072969 + 3 ^ 40 * 6335772 * 2
def baseEnd_6335772 : Nat := 3253296353298090496612321

theorem tailTrace_6335772 : CollatzResearch.WordTrace tailWord_6335772 prefixEnd_6335772 3253296353298090496612321 := by
  unfold tailWord_6335772
  simp only [CollatzResearch.WordTrace]
  refine ⟨115542294601293791277608785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154056392801725055036811713 115542294601293791277608785)
  ·
    refine ⟨86656720950970343458206589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115542294601293791277608785 86656720950970343458206589)
    ·
      refine ⟨32496270356613878796827471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86656720950970343458206589 32496270356613878796827471)
      ·
        refine ⟨48744405534920818195241207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32496270356613878796827471 48744405534920818195241207)
        ·
          refine ⟨73116608302381227292861811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48744405534920818195241207 73116608302381227292861811)
          ·
            refine ⟨109674912453571840939292717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73116608302381227292861811 109674912453571840939292717)
            ·
              refine ⟨41128092170089440352234769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109674912453571840939292717 41128092170089440352234769)
              ·
                refine ⟨30846069127567080264176077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41128092170089440352234769 30846069127567080264176077)
                ·
                  refine ⟨11567275922837655099066029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30846069127567080264176077 11567275922837655099066029)
                  ·
                    refine ⟨4337728471064120662149761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11567275922837655099066029 4337728471064120662149761)
                    ·
                      refine ⟨3253296353298090496612321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4337728471064120662149761 3253296353298090496612321)
                      ·
                        rfl

theorem cell23_6335772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_6335772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335772 prefixEnd_6335772 := by exact prefixLift 6335772
  have htrace : WordTrace (prefixWord ++ tailWord_6335772) baseStart_6335772 baseEnd_6335772 := by
    simpa [prefixWord, tailWord_6335772, baseEnd_6335772] using wordTrace_append hprefix tailTrace_6335772
  have hstable : (prefixWord ++ tailWord_6335772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335772).length < 2 ^ (prefixWord ++ tailWord_6335772).sum := by decide
  have hdescent : baseEnd_6335772 < baseStart_6335772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335802 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2]
def baseStart_6335802 : Nat := 118140960795 + 6335802 * 2 ^ 59
def prefixEnd_6335802 : Nat := 4983230072969 + 3 ^ 40 * 6335802 * 2
def baseEnd_6335802 : Nat := 3253311757717725379237183

theorem tailTrace_6335802 : CollatzResearch.WordTrace tailWord_6335802 prefixEnd_6335802 3253311757717725379237183 := by
  unfold tailWord_6335802
  simp only [CollatzResearch.WordTrace]
  refine ⟨57771420848119724419702415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154057122261652598452539773 57771420848119724419702415)
  ·
    refine ⟨86657131272179586629553623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57771420848119724419702415 86657131272179586629553623)
    ·
      refine ⟨129985696908269379944330435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86657131272179586629553623 129985696908269379944330435)
      ·
        refine ⟨194978545362404069916495653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129985696908269379944330435 194978545362404069916495653)
        ·
          refine ⟨36558477255450763109342935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194978545362404069916495653 36558477255450763109342935)
          ·
            refine ⟨54837715883176144664014403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36558477255450763109342935 54837715883176144664014403)
            ·
              refine ⟨82256573824764216996021605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54837715883176144664014403 82256573824764216996021605)
              ·
                refine ⟨15423107592143290686754051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82256573824764216996021605 15423107592143290686754051)
                ·
                  refine ⟨23134661388214936030131077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15423107592143290686754051 23134661388214936030131077)
                  ·
                    refine ⟨4337749010290300505649577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23134661388214936030131077 4337749010290300505649577)
                    ·
                      refine ⟨3253311757717725379237183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4337749010290300505649577 3253311757717725379237183)
                      ·
                        rfl

theorem cell23_6335802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2].length) (baseStart_6335802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335802 prefixEnd_6335802 := by exact prefixLift 6335802
  have htrace : WordTrace (prefixWord ++ tailWord_6335802) baseStart_6335802 baseEnd_6335802 := by
    simpa [prefixWord, tailWord_6335802, baseEnd_6335802] using wordTrace_append hprefix tailTrace_6335802
  have hstable : (prefixWord ++ tailWord_6335802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335802).length < 2 ^ (prefixWord ++ tailWord_6335802).sum := by decide
  have hdescent : baseEnd_6335802 < baseStart_6335802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335808 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 9]
def baseStart_6335808 : Nat := 118140960795 + 6335808 * 2 ^ 59
def prefixEnd_6335808 : Nat := 4983230072969 + 3 ^ 40 * 6335808 * 2
def baseEnd_6335808 : Nat := 361479426511294706195795

theorem tailTrace_6335808 : CollatzResearch.WordTrace tailWord_6335808 prefixEnd_6335808 361479426511294706195795 := by
  unfold tailWord_6335808
  simp only [CollatzResearch.WordTrace]
  refine ⟨115542951115228580351764039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154057268153638107135685385 115542951115228580351764039)
  ·
    refine ⟨173314426672842870527646059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115542951115228580351764039 173314426672842870527646059)
    ·
      refine ⟨259971640009264305791469089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173314426672842870527646059 259971640009264305791469089)
      ·
        refine ⟨194978730006948229343601817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259971640009264305791469089 194978730006948229343601817)
        ·
          refine ⟨146234047505211172007701363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194978730006948229343601817 146234047505211172007701363)
          ·
            refine ⟨219351071257816758011552045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146234047505211172007701363 219351071257816758011552045)
            ·
              refine ⟨82256651721681284254332017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219351071257816758011552045 82256651721681284254332017)
              ·
                refine ⟨61692488791260963190749013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82256651721681284254332017 61692488791260963190749013)
                ·
                  refine ⟨361479426511294706195795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61692488791260963190749013 361479426511294706195795)
                  ·
                    rfl

theorem cell23_6335808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 9].length) (baseStart_6335808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335808 prefixEnd_6335808 := by exact prefixLift 6335808
  have htrace : WordTrace (prefixWord ++ tailWord_6335808) baseStart_6335808 baseEnd_6335808 := by
    simpa [prefixWord, tailWord_6335808, baseEnd_6335808] using wordTrace_append hprefix tailTrace_6335808
  have hstable : (prefixWord ++ tailWord_6335808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335808).length < 2 ^ (prefixWord ++ tailWord_6335808).sum := by decide
  have hdescent : baseEnd_6335808 < baseStart_6335808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335812 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_6335812 : Nat := 118140960795 + 6335812 * 2 ^ 59
def prefixEnd_6335812 : Nat := 4983230072969 + 3 ^ 40 * 6335812 * 2
def baseEnd_6335812 : Nat := 1084438964174756780037379

theorem tailTrace_6335812 : CollatzResearch.WordTrace tailWord_6335812 prefixEnd_6335812 1084438964174756780037379 := by
  unfold tailWord_6335812
  simp only [CollatzResearch.WordTrace]
  refine ⟨115543024061221334693336845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154057365414961779591115793 115543024061221334693336845)
  ·
    refine ⟨43328634022958000510001317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115543024061221334693336845 43328634022958000510001317)
    ·
      refine ⟨8124118879304625095625247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43328634022958000510001317 8124118879304625095625247)
      ·
        refine ⟨12186178318956937643437871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8124118879304625095625247 12186178318956937643437871)
        ·
          refine ⟨18279267478435406465156807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12186178318956937643437871 18279267478435406465156807)
          ·
            refine ⟨27418901217653109697735211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18279267478435406465156807 27418901217653109697735211)
            ·
              refine ⟨41128351826479664546602817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27418901217653109697735211 41128351826479664546602817)
              ·
                refine ⟨30846263869859748409952113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41128351826479664546602817 30846263869859748409952113)
                ·
                  refine ⟨23134697902394811307464085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30846263869859748409952113 23134697902394811307464085)
                  ·
                    refine ⟨1084438964174756780037379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23134697902394811307464085 1084438964174756780037379)
                    ·
                      rfl

theorem cell23_6335812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_6335812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335812 prefixEnd_6335812 := by exact prefixLift 6335812
  have htrace : WordTrace (prefixWord ++ tailWord_6335812) baseStart_6335812 baseEnd_6335812 := by
    simpa [prefixWord, tailWord_6335812, baseEnd_6335812] using wordTrace_append hprefix tailTrace_6335812
  have hstable : (prefixWord ++ tailWord_6335812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335812).length < 2 ^ (prefixWord ++ tailWord_6335812).sum := by decide
  have hdescent : baseEnd_6335812 < baseStart_6335812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335815 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_6335815 : Nat := 118140960795 + 6335815 * 2 ^ 59
def prefixEnd_6335815 : Nat := 4983230072969 + 3 ^ 40 * 6335815 * 2
def baseEnd_6335815 : Nat := 3253318432966233828374623

theorem tailTrace_6335815 : CollatzResearch.WordTrace tailWord_6335815 prefixEnd_6335815 3253318432966233828374623 := by
  unfold tailWord_6335815
  simp only [CollatzResearch.WordTrace]
  refine ⟨231086157541431800899032899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154057438360954533932688599 231086157541431800899032899)
  ·
    refine ⟨346629236312147701348549349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231086157541431800899032899 346629236312147701348549349)
    ·
      refine ⟨64992981808527694002853003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346629236312147701348549349 64992981808527694002853003)
      ·
        refine ⟨97489472712791541004279505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64992981808527694002853003 97489472712791541004279505)
        ·
          refine ⟨73117104534593655753209629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97489472712791541004279505 73117104534593655753209629)
          ·
            refine ⟨27418914200472620907453611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73117104534593655753209629 27418914200472620907453611)
            ·
              refine ⟨41128371300708931361180417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27418914200472620907453611 41128371300708931361180417)
              ·
                refine ⟨30846278475531698520885313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41128371300708931361180417 30846278475531698520885313)
                ·
                  refine ⟨23134708856648773890663985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30846278475531698520885313 23134708856648773890663985)
                  ·
                    refine ⟨17351031642486580417997989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23134708856648773890663985 17351031642486580417997989)
                    ·
                      refine ⟨3253318432966233828374623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17351031642486580417997989 3253318432966233828374623)
                      ·
                        rfl

theorem cell23_6335815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_6335815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335815 prefixEnd_6335815 := by exact prefixLift 6335815
  have htrace : WordTrace (prefixWord ++ tailWord_6335815) baseStart_6335815 baseEnd_6335815 := by
    simpa [prefixWord, tailWord_6335815, baseEnd_6335815] using wordTrace_append hprefix tailTrace_6335815
  have hstable : (prefixWord ++ tailWord_6335815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335815).length < 2 ^ (prefixWord ++ tailWord_6335815).sum := by decide
  have hdescent : baseEnd_6335815 < baseStart_6335815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335825 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 7]
def baseStart_6335825 : Nat := 118140960795 + 6335825 * 2 ^ 59
def prefixEnd_6335825 : Nat := 4983230072969 + 3 ^ 40 * 6335825 * 2
def baseEnd_6335825 : Nat := 361480396419197643249953

theorem tailTrace_6335825 : CollatzResearch.WordTrace tailWord_6335825 prefixEnd_6335825 361480396419197643249953 := by
  unfold tailWord_6335825
  simp only [CollatzResearch.WordTrace]
  refine ⟨231086522271395572606896929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154057681514263715071264619 231086522271395572606896929)
  ·
    refine ⟨173314891703546679455172697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231086522271395572606896929 173314891703546679455172697)
    ·
      refine ⟨129986168777660009591379523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173314891703546679455172697 129986168777660009591379523)
      ·
        refine ⟨194979253166490014387069285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129986168777660009591379523 194979253166490014387069285)
        ·
          refine ⟨36558609968716877697575491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194979253166490014387069285 36558609968716877697575491)
          ·
            refine ⟨54837914953075316546363237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36558609968716877697575491 54837914953075316546363237)
            ·
              refine ⟨10282109053701621852443107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54837914953075316546363237 10282109053701621852443107)
              ·
                refine ⟨15423163580552432778664661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10282109053701621852443107 15423163580552432778664661)
                ·
                  refine ⟨361480396419197643249953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15423163580552432778664661 361480396419197643249953)
                  ·
                    rfl

theorem cell23_6335825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 7].length) (baseStart_6335825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335825 prefixEnd_6335825 := by exact prefixLift 6335825
  have htrace : WordTrace (prefixWord ++ tailWord_6335825) baseStart_6335825 baseEnd_6335825 := by
    simpa [prefixWord, tailWord_6335825, baseEnd_6335825] using wordTrace_append hprefix tailTrace_6335825
  have hstable : (prefixWord ++ tailWord_6335825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335825).length < 2 ^ (prefixWord ++ tailWord_6335825).sum := by decide
  have hdescent : baseEnd_6335825 < baseStart_6335825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335830 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_6335830 : Nat := 118140960795 + 6335830 * 2 ^ 59
def prefixEnd_6335830 : Nat := 4983230072969 + 3 ^ 40 * 6335830 * 2
def baseEnd_6335830 : Nat := 3253326135176051269687055

theorem tailTrace_6335830 : CollatzResearch.WordTrace tailWord_6335830 prefixEnd_6335830 3253326135176051269687055 := by
  unfold tailWord_6335830
  simp only [CollatzResearch.WordTrace]
  refine ⟨14442919039773591153801809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154057803090918305640552629 14442919039773591153801809)
  ·
    refine ⟨10832189279830193365351357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14442919039773591153801809 10832189279830193365351357)
    ·
      refine ⟨4062070979936322512006759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10832189279830193365351357 4062070979936322512006759)
      ·
        refine ⟨6093106469904483768010139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4062070979936322512006759 6093106469904483768010139)
        ·
          refine ⟨9139659704856725652015209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6093106469904483768010139 9139659704856725652015209)
          ·
            refine ⟨6854744778642544239011407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9139659704856725652015209 6854744778642544239011407)
            ·
              refine ⟨10282117167963816358517111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6854744778642544239011407 10282117167963816358517111)
              ·
                refine ⟨15423175751945724537775667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10282117167963816358517111 15423175751945724537775667)
                ·
                  refine ⟨23134763627918586806663501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15423175751945724537775667 23134763627918586806663501)
                  ·
                    refine ⟨8675536360469470052498813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23134763627918586806663501 8675536360469470052498813)
                    ·
                      refine ⟨3253326135176051269687055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8675536360469470052498813 3253326135176051269687055)
                      ·
                        rfl

theorem cell23_6335830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_6335830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335830 prefixEnd_6335830 := by exact prefixLift 6335830
  have htrace : WordTrace (prefixWord ++ tailWord_6335830) baseStart_6335830 baseEnd_6335830 := by
    simpa [prefixWord, tailWord_6335830, baseEnd_6335830] using wordTrace_append hprefix tailTrace_6335830
  have hstable : (prefixWord ++ tailWord_6335830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335830).length < 2 ^ (prefixWord ++ tailWord_6335830).sum := by decide
  have hdescent : baseEnd_6335830 < baseStart_6335830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335855 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 2, 5]
def baseStart_6335855 : Nat := 118140960795 + 6335855 * 2 ^ 59
def prefixEnd_6335855 : Nat := 4983230072969 + 3 ^ 40 * 6335855 * 2
def baseEnd_6335855 : Nat := 1084446324064137890624813

theorem tailTrace_6335855 : CollatzResearch.WordTrace tailWord_6335855 prefixEnd_6335855 1084446324064137890624813 := by
  unfold tailWord_6335855
  simp only [CollatzResearch.WordTrace]
  refine ⟨231087616461286887730489019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154058410974191258486992679 231087616461286887730489019)
  ·
    refine ⟨346631424691930331595733529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231087616461286887730489019 346631424691930331595733529)
    ·
      refine ⟨259973568518947748696800147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346631424691930331595733529 259973568518947748696800147)
      ·
        refine ⟨389960352778421623045200221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259973568518947748696800147 389960352778421623045200221)
        ·
          refine ⟨146235132291908108641950083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389960352778421623045200221 146235132291908108641950083)
          ·
            refine ⟨219352698437862162962925125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146235132291908108641950083 219352698437862162962925125)
            ·
              refine ⟨41128630957099155555548461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 219352698437862162962925125 41128630957099155555548461)
              ·
                refine ⟨15423236608912183333330673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41128630957099155555548461 15423236608912183333330673)
                ·
                  refine ⟨11567427456684137499998005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15423236608912183333330673 11567427456684137499998005)
                  ·
                    refine ⟨1084446324064137890624813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11567427456684137499998005 1084446324064137890624813)
                    ·
                      rfl

theorem cell23_6335855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 5].length) (baseStart_6335855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335855 prefixEnd_6335855 := by exact prefixLift 6335855
  have htrace : WordTrace (prefixWord ++ tailWord_6335855) baseStart_6335855 baseEnd_6335855 := by
    simpa [prefixWord, tailWord_6335855, baseEnd_6335855] using wordTrace_append hprefix tailTrace_6335855
  have hstable : (prefixWord ++ tailWord_6335855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335855).length < 2 ^ (prefixWord ++ tailWord_6335855).sum := by decide
  have hdescent : baseEnd_6335855 < baseStart_6335855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335936 : List Nat := [2, 1, 1, 2, 3, 1, 6, 2, 1, 4]
def baseStart_6335936 : Nat := 118140960795 + 6335936 * 2 ^ 59
def prefixEnd_6335936 : Nat := 4983230072969 + 3 ^ 40 * 6335936 * 2
def baseEnd_6335936 : Nat := 1084460188041809284987189

theorem tailTrace_6335936 : CollatzResearch.WordTrace tailWord_6335936 prefixEnd_6335936 1084460188041809284987189 := by
  unfold tailWord_6335936
  simp only [CollatzResearch.WordTrace]
  refine ⟨115545285386996719282093831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154060380515995625709458441 115545285386996719282093831)
  ·
    refine ⟨173317928080495078923140747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115545285386996719282093831 173317928080495078923140747)
    ·
      refine ⟨259976892120742618384711121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173317928080495078923140747 259976892120742618384711121)
      ·
        refine ⟨194982669090556963788533341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259976892120742618384711121 194982669090556963788533341)
        ·
          refine ⟨73118500908958861420700003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194982669090556963788533341 73118500908958861420700003)
          ·
            refine ⟨109677751363438292131050005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73118500908958861420700003 109677751363438292131050005)
            ·
              refine ⟨5141144595161169943642969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109677751363438292131050005 5141144595161169943642969)
              ·
                refine ⟨3855858446370877457732227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5141144595161169943642969 3855858446370877457732227)
                ·
                  refine ⟨5783787669556316186598341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855858446370877457732227 5783787669556316186598341)
                  ·
                    refine ⟨1084460188041809284987189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5783787669556316186598341 1084460188041809284987189)
                    ·
                      rfl

theorem cell23_6335936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 1, 4].length) (baseStart_6335936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335936 prefixEnd_6335936 := by exact prefixLift 6335936
  have htrace : WordTrace (prefixWord ++ tailWord_6335936) baseStart_6335936 baseEnd_6335936 := by
    simpa [prefixWord, tailWord_6335936, baseEnd_6335936] using wordTrace_append hprefix tailTrace_6335936
  have hstable : (prefixWord ++ tailWord_6335936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335936).length < 2 ^ (prefixWord ++ tailWord_6335936).sum := by decide
  have hdescent : baseEnd_6335936 < baseStart_6335936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335952 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 3, 5, 2]
def baseStart_6335952 : Nat := 118140960795 + 6335952 * 2 ^ 59
def prefixEnd_6335952 : Nat := 4983230072969 + 3 ^ 40 * 6335952 * 2
def baseEnd_6335952 : Nat := 3253388779815899792361493

theorem tailTrace_6335952 : CollatzResearch.WordTrace tailWord_6335952 prefixEnd_6335952 3253388779815899792361493 := by
  unfold tailWord_6335952
  simp only [CollatzResearch.WordTrace]
  refine ⟨115545577170967736648385055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154060769561290315531180073 115545577170967736648385055)
  ·
    refine ⟨173318365756451604972577583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115545577170967736648385055 173318365756451604972577583)
    ·
      refine ⟨259977548634677407458866375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173318365756451604972577583 259977548634677407458866375)
      ·
        refine ⟨389966322952016111188299563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259977548634677407458866375 389966322952016111188299563)
        ·
          refine ⟨584949484428024166782449345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389966322952016111188299563 584949484428024166782449345)
          ·
            refine ⟨438712113321018125086837009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584949484428024166782449345 438712113321018125086837009)
            ·
              refine ⟨329034084990763593815127757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438712113321018125086837009 329034084990763593815127757)
              ·
                refine ⟨123387781871536347680672909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329034084990763593815127757 123387781871536347680672909)
                ·
                  refine ⟨46270418201826130380252341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123387781871536347680672909 46270418201826130380252341)
                  ·
                    refine ⟨4337851706421199723148657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46270418201826130380252341 4337851706421199723148657)
                    ·
                      refine ⟨3253388779815899792361493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4337851706421199723148657 3253388779815899792361493)
                      ·
                        rfl

theorem cell23_6335952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 5, 2].length) (baseStart_6335952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335952 prefixEnd_6335952 := by exact prefixLift 6335952
  have htrace : WordTrace (prefixWord ++ tailWord_6335952) baseStart_6335952 baseEnd_6335952 := by
    simpa [prefixWord, tailWord_6335952, baseEnd_6335952] using wordTrace_append hprefix tailTrace_6335952
  have hstable : (prefixWord ++ tailWord_6335952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335952).length < 2 ^ (prefixWord ++ tailWord_6335952).sum := by decide
  have hdescent : baseEnd_6335952 < baseStart_6335952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335962 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 3, 5]
def baseStart_6335962 : Nat := 118140960795 + 6335962 * 2 ^ 59
def prefixEnd_6335962 : Nat := 4983230072969 + 3 ^ 40 * 6335962 * 2
def baseEnd_6335962 : Nat := 1084464638207481584412149

theorem tailTrace_6335962 : CollatzResearch.WordTrace tailWord_6335962 prefixEnd_6335962 1084464638207481584412149 := by
  unfold tailWord_6335962
  simp only [CollatzResearch.WordTrace]
  refine ⟨57772879767974811251158535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154061012714599496669756093 57772879767974811251158535)
  ·
    refine ⟨86659319651962216876737803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57772879767974811251158535 86659319651962216876737803)
    ·
      refine ⟨129988979477943325315106705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86659319651962216876737803 129988979477943325315106705)
      ·
        refine ⟨97491734608457493986330029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129988979477943325315106705 97491734608457493986330029)
        ·
          refine ⟨36559400478171560244873761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97491734608457493986330029 36559400478171560244873761)
          ·
            refine ⟨27419550358628670183655321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36559400478171560244873761 27419550358628670183655321)
            ·
              refine ⟨20564662768971502637741491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27419550358628670183655321 20564662768971502637741491)
              ·
                refine ⟨30846994153457253956612237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20564662768971502637741491 30846994153457253956612237)
                ·
                  refine ⟨11567622807546470233729589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30846994153457253956612237 11567622807546470233729589)
                  ·
                    refine ⟨1084464638207481584412149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11567622807546470233729589 1084464638207481584412149)
                    ·
                      rfl

theorem cell23_6335962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_6335962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335962 prefixEnd_6335962 := by exact prefixLift 6335962
  have htrace : WordTrace (prefixWord ++ tailWord_6335962) baseStart_6335962 baseEnd_6335962 := by
    simpa [prefixWord, tailWord_6335962, baseEnd_6335962] using wordTrace_append hprefix tailTrace_6335962
  have hstable : (prefixWord ++ tailWord_6335962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335962).length < 2 ^ (prefixWord ++ tailWord_6335962).sum := by decide
  have hdescent : baseEnd_6335962 < baseStart_6335962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335969 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 1, 5, 2]
def baseStart_6335969 : Nat := 118140960795 + 6335969 * 2 ^ 59
def prefixEnd_6335969 : Nat := 4983230072969 + 3 ^ 40 * 6335969 * 2
def baseEnd_6335969 : Nat := 3253397508987026225848915

theorem tailTrace_6335969 : CollatzResearch.WordTrace tailWord_6335969 prefixEnd_6335969 3253397508987026225848915 := by
  unfold tailWord_6335969
  simp only [CollatzResearch.WordTrace]
  refine ⟨231091774382873885200138961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154061182921915923466759307 231091774382873885200138961)
  ·
    refine ⟨173318830787155413900104221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231091774382873885200138961 173318830787155413900104221)
    ·
      refine ⟨64994561545183280212539083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173318830787155413900104221 64994561545183280212539083)
      ·
        refine ⟨97491842317774920318808625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64994561545183280212539083 97491842317774920318808625)
        ·
          refine ⟨73118881738331190239106469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97491842317774920318808625 73118881738331190239106469)
          ·
            refine ⟨13709790325937098169832463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73118881738331190239106469 13709790325937098169832463)
            ·
              refine ⟨20564685488905647254748695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13709790325937098169832463 20564685488905647254748695)
              ·
                refine ⟨30847028233358470882123043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20564685488905647254748695 30847028233358470882123043)
                ·
                  refine ⟨46270542350037706323184565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30847028233358470882123043 46270542350037706323184565)
                  ·
                    refine ⟨4337863345316034967798553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46270542350037706323184565 4337863345316034967798553)
                    ·
                      refine ⟨3253397508987026225848915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4337863345316034967798553 3253397508987026225848915)
                      ·
                        rfl

theorem cell23_6335969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_6335969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335969 prefixEnd_6335969 := by exact prefixLift 6335969
  have htrace : WordTrace (prefixWord ++ tailWord_6335969) baseStart_6335969 baseEnd_6335969 := by
    simpa [prefixWord, tailWord_6335969, baseEnd_6335969] using wordTrace_append hprefix tailTrace_6335969
  have hstable : (prefixWord ++ tailWord_6335969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335969).length < 2 ^ (prefixWord ++ tailWord_6335969).sum := by decide
  have hdescent : baseEnd_6335969 < baseStart_6335969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6335995 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 6]
def baseStart_6335995 : Nat := 118140960795 + 6335995 * 2 ^ 59
def prefixEnd_6335995 : Nat := 4983230072969 + 3 ^ 40 * 6335995 * 2
def baseEnd_6335995 : Nat := 3253410859484043124123795

theorem tailTrace_6335995 : CollatzResearch.WordTrace tailWord_6335995 prefixEnd_6335995 3253410859484043124123795 := by
  unfold tailWord_6335995
  simp only [CollatzResearch.WordTrace]
  refine ⟨231092722680779691640585439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154061815120519794427056959 231092722680779691640585439)
  ·
    refine ⟨346639084021169537460878159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231092722680779691640585439 346639084021169537460878159)
    ·
      refine ⟨519958626031754306191317239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346639084021169537460878159 519958626031754306191317239)
      ·
        refine ⟨779937939047631459286975859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519958626031754306191317239 779937939047631459286975859)
        ·
          refine ⟨1169906908571447188930463789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779937939047631459286975859 1169906908571447188930463789)
          ·
            refine ⟨438715090714292695848923921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1169906908571447188930463789 438715090714292695848923921)
            ·
              refine ⟨329036318035719521886692941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438715090714292695848923921 329036318035719521886692941)
              ·
                refine ⟨123388619263394820707509853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329036318035719521886692941 123388619263394820707509853)
                ·
                  refine ⟨46270732223773057765316195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123388619263394820707509853 46270732223773057765316195)
                  ·
                    refine ⟨69406098335659586647974293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46270732223773057765316195 69406098335659586647974293)
                    ·
                      refine ⟨3253410859484043124123795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69406098335659586647974293 3253410859484043124123795)
                      ·
                        rfl

theorem cell23_6335995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 6].length) (baseStart_6335995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6335995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6335995 prefixEnd_6335995 := by exact prefixLift 6335995
  have htrace : WordTrace (prefixWord ++ tailWord_6335995) baseStart_6335995 baseEnd_6335995 := by
    simpa [prefixWord, tailWord_6335995, baseEnd_6335995] using wordTrace_append hprefix tailTrace_6335995
  have hstable : (prefixWord ++ tailWord_6335995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6335995).length < 2 ^ (prefixWord ++ tailWord_6335995).sum := by decide
  have hdescent : baseEnd_6335995 < baseStart_6335995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6335995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336005 : List Nat := [1, 3, 1, 1, 2, 2, 1, 12]
def baseStart_6336005 : Nat := 118140960795 + 6336005 * 2 ^ 59
def prefixEnd_6336005 : Nat := 4983230072969 + 3 ^ 40 * 6336005 * 2
def baseEnd_6336005 : Nat := 120496888677429188333287

theorem tailTrace_6336005 : CollatzResearch.WordTrace tailWord_6336005 prefixEnd_6336005 120496888677429188333287 := by
  unfold tailWord_6336005
  simp only [CollatzResearch.WordTrace]
  refine ⟨231093087410743463348449469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154062058273828975565632979 231093087410743463348449469)
  ·
    refine ⟨86659907779028798755668551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231093087410743463348449469 86659907779028798755668551)
    ·
      refine ⟨129989861668543198133502827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86659907779028798755668551 129989861668543198133502827)
      ·
        refine ⟨194984792502814797200254241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129989861668543198133502827 194984792502814797200254241)
        ·
          refine ⟨146238594377111097900190681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194984792502814797200254241 146238594377111097900190681)
          ·
            refine ⟨109678945782833323425143011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146238594377111097900190681 109678945782833323425143011)
            ·
              refine ⟨164518418674249985137714517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109678945782833323425143011 164518418674249985137714517)
              ·
                refine ⟨120496888677429188333287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 164518418674249985137714517 120496888677429188333287)
                ·
                  rfl

theorem cell23_6336005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 12].length) (baseStart_6336005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336005 prefixEnd_6336005 := by exact prefixLift 6336005
  have htrace : WordTrace (prefixWord ++ tailWord_6336005) baseStart_6336005 baseEnd_6336005 := by
    simpa [prefixWord, tailWord_6336005, baseEnd_6336005] using wordTrace_append hprefix tailTrace_6336005
  have hstable : (prefixWord ++ tailWord_6336005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336005).length < 2 ^ (prefixWord ++ tailWord_6336005).sum := by decide
  have hdescent : baseEnd_6336005 < baseStart_6336005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336019 : List Nat := [1, 1, 1, 2, 1, 6, 1, 4, 1, 2, 3]
def baseStart_6336019 : Nat := 118140960795 + 6336019 * 2 ^ 59
def prefixEnd_6336019 : Nat := 4983230072969 + 3 ^ 40 * 6336019 * 2
def baseEnd_6336019 : Nat := 3253423183019751030223685

theorem tailTrace_6336019 : CollatzResearch.WordTrace tailWord_6336019 prefixEnd_6336019 3253423183019751030223685 := by
  unfold tailWord_6336019
  simp only [CollatzResearch.WordTrace]
  refine ⟨231093598032692743739459111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154062398688461829159639407 231093598032692743739459111)
  ·
    refine ⟨346640397049039115609188667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231093598032692743739459111 346640397049039115609188667)
    ·
      refine ⟨519960595573558673413783001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346640397049039115609188667 519960595573558673413783001)
      ·
        refine ⟨389970446680169005060337251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519960595573558673413783001 389970446680169005060337251)
        ·
          refine ⟨584955670020253507590505877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389970446680169005060337251 584955670020253507590505877)
          ·
            refine ⟨27419797032199383168304963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 584955670020253507590505877 27419797032199383168304963)
            ·
              refine ⟨41129695548299074752457445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27419797032199383168304963 41129695548299074752457445)
              ·
                refine ⟨7711817915306076516085771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41129695548299074752457445 7711817915306076516085771)
                ·
                  refine ⟨11567726872959114774128657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7711817915306076516085771 11567726872959114774128657)
                  ·
                    refine ⟨8675795154719336080596493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11567726872959114774128657 8675795154719336080596493)
                    ·
                      refine ⟨3253423183019751030223685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8675795154719336080596493 3253423183019751030223685)
                      ·
                        rfl

theorem cell23_6336019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 2, 3].length) (baseStart_6336019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336019 prefixEnd_6336019 := by exact prefixLift 6336019
  have htrace : WordTrace (prefixWord ++ tailWord_6336019) baseStart_6336019 baseEnd_6336019 := by
    simpa [prefixWord, tailWord_6336019, baseEnd_6336019] using wordTrace_append hprefix tailTrace_6336019
  have hstable : (prefixWord ++ tailWord_6336019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336019).length < 2 ^ (prefixWord ++ tailWord_6336019).sum := by decide
  have hdescent : baseEnd_6336019 < baseStart_6336019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336060 : List Nat := [2, 2, 2, 2, 5, 1, 2, 1, 2, 4]
def baseStart_6336060 : Nat := 118140960795 + 6336060 * 2 ^ 59
def prefixEnd_6336060 : Nat := 4983230072969 + 3 ^ 40 * 6336060 * 2
def baseEnd_6336060 : Nat := 1084481411908861789936999

theorem tailTrace_6336060 : CollatzResearch.WordTrace tailWord_6336060 prefixEnd_6336060 1084481411908861789936999 := by
  unfold tailWord_6336060
  simp only [CollatzResearch.WordTrace]
  refine ⟨115547546712772103870850817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154063395617029471827801089 115547546712772103870850817)
  ·
    refine ⟨86660660034579077903138113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115547546712772103870850817 86660660034579077903138113)
    ·
      refine ⟨64995495025934308427353585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86660660034579077903138113 64995495025934308427353585)
      ·
        refine ⟨48746621269450731320515189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64995495025934308427353585 48746621269450731320515189)
        ·
          refine ⟨4569995744011006061298299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48746621269450731320515189 4569995744011006061298299)
          ·
            refine ⟨6854993616016509091947449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569995744011006061298299 6854993616016509091947449)
            ·
              refine ⟨5141245212012381818960587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6854993616016509091947449 5141245212012381818960587)
              ·
                refine ⟨7711867818018572728440881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5141245212012381818960587 7711867818018572728440881)
                ·
                  refine ⟨5783900863513929546330661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7711867818018572728440881 5783900863513929546330661)
                  ·
                    refine ⟨1084481411908861789936999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5783900863513929546330661 1084481411908861789936999)
                    ·
                      rfl

theorem cell23_6336060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_6336060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336060 prefixEnd_6336060 := by exact prefixLift 6336060
  have htrace : WordTrace (prefixWord ++ tailWord_6336060) baseStart_6336060 baseEnd_6336060 := by
    simpa [prefixWord, tailWord_6336060, baseEnd_6336060] using wordTrace_append hprefix tailTrace_6336060
  have hstable : (prefixWord ++ tailWord_6336060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336060).length < 2 ^ (prefixWord ++ tailWord_6336060).sum := by decide
  have hdescent : baseEnd_6336060 < baseStart_6336060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336076 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 3, 3, 2]
def baseStart_6336076 : Nat := 118140960795 + 6336076 * 2 ^ 59
def prefixEnd_6336076 : Nat := 4983230072969 + 3 ^ 40 * 6336076 * 2
def baseEnd_6336076 : Nat := 3253452451417057307210923

theorem tailTrace_6336076 : CollatzResearch.WordTrace tailWord_6336076 prefixEnd_6336076 3253452451417057307210923 := by
  unfold tailWord_6336076
  simp only [CollatzResearch.WordTrace]
  refine ⟨115547838496743121237142041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154063784662324161649522721 115547838496743121237142041)
  ·
    refine ⟨86660878872557340927856531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115547838496743121237142041 86660878872557340927856531)
    ·
      refine ⟨129991318308836011391784797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86660878872557340927856531 129991318308836011391784797)
      ·
        refine ⟨48746744365813504271919299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129991318308836011391784797 48746744365813504271919299)
        ·
          refine ⟨73120116548720256407878949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48746744365813504271919299 73120116548720256407878949)
          ·
            refine ⟨13710021852885048076477303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73120116548720256407878949 13710021852885048076477303)
            ·
              refine ⟨20565032779327572114715955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13710021852885048076477303 20565032779327572114715955)
              ·
                refine ⟨30847549168991358172073933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20565032779327572114715955 30847549168991358172073933)
                ·
                  refine ⟨11567830938371759314527725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30847549168991358172073933 11567830938371759314527725)
                  ·
                    refine ⟨4337936601889409742947897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11567830938371759314527725 4337936601889409742947897)
                    ·
                      refine ⟨3253452451417057307210923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4337936601889409742947897 3253452451417057307210923)
                      ·
                        rfl

theorem cell23_6336076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_6336076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336076 prefixEnd_6336076 := by exact prefixLift 6336076
  have htrace : WordTrace (prefixWord ++ tailWord_6336076) baseStart_6336076 baseEnd_6336076 := by
    simpa [prefixWord, tailWord_6336076, baseEnd_6336076] using wordTrace_append hprefix tailTrace_6336076
  have hstable : (prefixWord ++ tailWord_6336076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336076).length < 2 ^ (prefixWord ++ tailWord_6336076).sum := by decide
  have hdescent : baseEnd_6336076 < baseStart_6336076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336129 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 7]
def baseStart_6336129 : Nat := 118140960795 + 6336129 * 2 ^ 59
def prefixEnd_6336129 : Nat := 4983230072969 + 3 ^ 40 * 6336129 * 2
def baseEnd_6336129 : Nat := 361497740654638399983131

theorem tailTrace_6336129 : CollatzResearch.WordTrace tailWord_6336129 prefixEnd_6336129 361497740654638399983131 := by
  unfold tailWord_6336129
  simp only [CollatzResearch.WordTrace]
  refine ⟨231097610062294232525963441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154065073374862821683975627 231097610062294232525963441)
  ·
    refine ⟨173323207546720674394472581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231097610062294232525963441 173323207546720674394472581)
    ·
      refine ⟨32498101415010126448963609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173323207546720674394472581 32498101415010126448963609)
      ·
        refine ⟨24373576061257594836722707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32498101415010126448963609 24373576061257594836722707)
        ·
          refine ⟨36560364091886392255084061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24373576061257594836722707 36560364091886392255084061)
          ·
            refine ⟨13710136534457397095656523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36560364091886392255084061 13710136534457397095656523)
            ·
              refine ⟨20565204801686095643484785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13710136534457397095656523 20565204801686095643484785)
              ·
                refine ⟨15423903601264571732613589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20565204801686095643484785 15423903601264571732613589)
                ·
                  refine ⟨361497740654638399983131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15423903601264571732613589 361497740654638399983131)
                  ·
                    rfl

theorem cell23_6336129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 7].length) (baseStart_6336129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336129 prefixEnd_6336129 := by exact prefixLift 6336129
  have htrace : WordTrace (prefixWord ++ tailWord_6336129) baseStart_6336129 baseEnd_6336129 := by
    simpa [prefixWord, tailWord_6336129, baseEnd_6336129] using wordTrace_append hprefix tailTrace_6336129
  have hstable : (prefixWord ++ tailWord_6336129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336129).length < 2 ^ (prefixWord ++ tailWord_6336129).sum := by decide
  have hdescent : baseEnd_6336129 < baseStart_6336129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336174 : List Nat := [4, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_6336174 : Nat := 118140960795 + 6336174 * 2 ^ 59
def prefixEnd_6336174 : Nat := 4983230072969 + 3 ^ 40 * 6336174 * 2
def baseEnd_6336174 : Nat := 3253502772521197923785473

theorem tailTrace_6336174 : CollatzResearch.WordTrace tailWord_6336174 prefixEnd_6336174 3253502772521197923785473 := by
  unfold tailWord_6336174
  simp only [CollatzResearch.WordTrace]
  refine ⟨28887406418391400651418947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154066167564754136807567717 28887406418391400651418947)
  ·
    refine ⟨43331109627587100977128421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28887406418391400651418947 43331109627587100977128421)
    ·
      refine ⟨8124583055172581433211579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43331109627587100977128421 8124583055172581433211579)
      ·
        refine ⟨12186874582758872149817369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8124583055172581433211579 12186874582758872149817369)
        ·
          refine ⟨9140155937069154112363027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12186874582758872149817369 9140155937069154112363027)
          ·
            refine ⟨13710233905603731168544541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9140155937069154112363027 13710233905603731168544541)
            ·
              refine ⟨5141337714601399188204203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13710233905603731168544541 5141337714601399188204203)
              ·
                refine ⟨7712006571902098782306305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5141337714601399188204203 7712006571902098782306305)
                ·
                  refine ⟨5784004928926574086729729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7712006571902098782306305 5784004928926574086729729)
                  ·
                    refine ⟨4338003696694930565047297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5784004928926574086729729 4338003696694930565047297)
                    ·
                      refine ⟨3253502772521197923785473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338003696694930565047297 3253502772521197923785473)
                      ·
                        rfl

theorem cell23_6336174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_6336174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336174 prefixEnd_6336174 := by exact prefixLift 6336174
  have htrace : WordTrace (prefixWord ++ tailWord_6336174) baseStart_6336174 baseEnd_6336174 := by
    simpa [prefixWord, tailWord_6336174, baseEnd_6336174] using wordTrace_append hprefix tailTrace_6336174
  have hstable : (prefixWord ++ tailWord_6336174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336174).length < 2 ^ (prefixWord ++ tailWord_6336174).sum := by decide
  have hdescent : baseEnd_6336174 < baseStart_6336174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336196 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_6336196 : Nat := 118140960795 + 6336196 * 2 ^ 59
def prefixEnd_6336196 : Nat := 4983230072969 + 3 ^ 40 * 6336196 * 2
def baseEnd_6336196 : Nat := 3253514069095596837710371

theorem tailTrace_6336196 : CollatzResearch.WordTrace tailWord_6336196 prefixEnd_6336196 3253514069095596837710371 := by
  unfold tailWord_6336196
  simp only [CollatzResearch.WordTrace]
  refine ⟨115550026876525751484326221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154066702502034335312434961 115550026876525751484326221)
  ·
    refine ⟨43331260078697156806622333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115550026876525751484326221 43331260078697156806622333)
    ·
      refine ⟨16249222529511433802483375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43331260078697156806622333 16249222529511433802483375)
      ·
        refine ⟨24373833794267150703725063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16249222529511433802483375 24373833794267150703725063)
        ·
          refine ⟨36560750691400726055587595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24373833794267150703725063 36560750691400726055587595)
          ·
            refine ⟨54841126037101089083381393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36560750691400726055587595 54841126037101089083381393)
            ·
              refine ⟨41130844527825816812536045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54841126037101089083381393 41130844527825816812536045)
              ·
                refine ⟨15424066697934681304701017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41130844527825816812536045 15424066697934681304701017)
                ·
                  refine ⟨11568050023451010978525763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15424066697934681304701017 11568050023451010978525763)
                  ·
                    refine ⟨17352075035176516467788645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11568050023451010978525763 17352075035176516467788645)
                    ·
                      refine ⟨3253514069095596837710371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17352075035176516467788645 3253514069095596837710371)
                      ·
                        rfl

theorem cell23_6336196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_6336196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336196 prefixEnd_6336196 := by exact prefixLift 6336196
  have htrace : WordTrace (prefixWord ++ tailWord_6336196) baseStart_6336196 baseEnd_6336196 := by
    simpa [prefixWord, tailWord_6336196, baseEnd_6336196] using wordTrace_append hprefix tailTrace_6336196
  have hstable : (prefixWord ++ tailWord_6336196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336196).length < 2 ^ (prefixWord ++ tailWord_6336196).sum := by decide
  have hdescent : baseEnd_6336196 < baseStart_6336196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336199 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_6336199 : Nat := 118140960795 + 6336199 * 2 ^ 59
def prefixEnd_6336199 : Nat := 4983230072969 + 3 ^ 40 * 6336199 * 2
def baseEnd_6336199 : Nat := 3253515609537560325972857

theorem tailTrace_6336199 : CollatzResearch.WordTrace tailWord_6336199 prefixEnd_6336199 3253515609537560325972857 := by
  unfold tailWord_6336199
  simp only [CollatzResearch.WordTrace]
  refine ⟨231100163172040634481011651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154066775448027089654007767 231100163172040634481011651)
  ·
    refine ⟨346650244758060951721517477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231100163172040634481011651 346650244758060951721517477)
    ·
      refine ⟨64996920892136428447784527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346650244758060951721517477 64996920892136428447784527)
      ·
        refine ⟨97495381338204642671676791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64996920892136428447784527 97495381338204642671676791)
        ·
          refine ⟨146243072007306964007515187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97495381338204642671676791 146243072007306964007515187)
          ·
            refine ⟨219364608010960446011272781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146243072007306964007515187 219364608010960446011272781)
            ·
              refine ⟨82261728004110167254227293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219364608010960446011272781 82261728004110167254227293)
              ·
                refine ⟨30848148001541312720335235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82261728004110167254227293 30848148001541312720335235)
                ·
                  refine ⟨46272222002311969080502853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30848148001541312720335235 46272222002311969080502853)
                  ·
                    refine ⟨8676041625433494202594285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46272222002311969080502853 8676041625433494202594285)
                    ·
                      refine ⟨3253515609537560325972857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8676041625433494202594285 3253515609537560325972857)
                      ·
                        rfl

theorem cell23_6336199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_6336199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336199 prefixEnd_6336199 := by exact prefixLift 6336199
  have htrace : WordTrace (prefixWord ++ tailWord_6336199) baseStart_6336199 baseEnd_6336199 := by
    simpa [prefixWord, tailWord_6336199, baseEnd_6336199] using wordTrace_append hprefix tailTrace_6336199
  have hstable : (prefixWord ++ tailWord_6336199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336199).length < 2 ^ (prefixWord ++ tailWord_6336199).sum := by decide
  have hdescent : baseEnd_6336199 < baseStart_6336199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336216 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 2, 2, 3]
def baseStart_6336216 : Nat := 118140960795 + 6336216 * 2 ^ 59
def prefixEnd_6336216 : Nat := 4983230072969 + 3 ^ 40 * 6336216 * 2
def baseEnd_6336216 : Nat := 3253524338708686759460279

theorem tailTrace_6336216 : CollatzResearch.WordTrace tailWord_6336216 prefixEnd_6336216 3253524338708686759460279 := by
  unfold tailWord_6336216
  simp only [CollatzResearch.WordTrace]
  refine ⟨115550391606489523192190251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154067188808652697589587001 115550391606489523192190251)
  ·
    refine ⟨173325587409734284788285377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115550391606489523192190251 173325587409734284788285377)
    ·
      refine ⟨129994190557300713591214033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173325587409734284788285377 129994190557300713591214033)
      ·
        refine ⟨97495642917975535193410525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129994190557300713591214033 97495642917975535193410525)
        ·
          refine ⟨36560866094240825697528947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97495642917975535193410525 36560866094240825697528947)
          ·
            refine ⟨54841299141361238546293421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36560866094240825697528947 54841299141361238546293421)
            ·
              refine ⟨20565487178010464454860033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54841299141361238546293421 20565487178010464454860033)
              ·
                refine ⟨15424115383507848341145025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20565487178010464454860033 15424115383507848341145025)
                ·
                  refine ⟨11568086537630886255858769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15424115383507848341145025 11568086537630886255858769)
                  ·
                    refine ⟨8676064903223164691894077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11568086537630886255858769 8676064903223164691894077)
                    ·
                      refine ⟨3253524338708686759460279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8676064903223164691894077 3253524338708686759460279)
                      ·
                        rfl

theorem cell23_6336216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_6336216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336216 prefixEnd_6336216 := by exact prefixLift 6336216
  have htrace : WordTrace (prefixWord ++ tailWord_6336216) baseStart_6336216 baseEnd_6336216 := by
    simpa [prefixWord, tailWord_6336216, baseEnd_6336216] using wordTrace_append hprefix tailTrace_6336216
  have hstable : (prefixWord ++ tailWord_6336216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336216).length < 2 ^ (prefixWord ++ tailWord_6336216).sum := by decide
  have hdescent : baseEnd_6336216 < baseStart_6336216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336236 : List Nat := [2, 2, 1, 1, 2, 2, 6, 1, 6]
def baseStart_6336236 : Nat := 118140960795 + 6336236 * 2 ^ 59
def prefixEnd_6336236 : Nat := 4983230072969 + 3 ^ 40 * 6336236 * 2
def baseEnd_6336236 : Nat := 361503845369086297912243

theorem tailTrace_6336236 : CollatzResearch.WordTrace tailWord_6336236 prefixEnd_6336236 361503845369086297912243 := by
  unfold tailWord_6336236
  simp only [CollatzResearch.WordTrace]
  refine ⟨115550756336453294900054281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154067675115271059866739041 115550756336453294900054281)
  ·
    refine ⟨86663067252339971175040711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115550756336453294900054281 86663067252339971175040711)
    ·
      refine ⟨129994600878509956762561067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86663067252339971175040711 129994600878509956762561067)
      ·
        refine ⟨194991901317764935143841601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129994600878509956762561067 194991901317764935143841601)
        ·
          refine ⟨146243925988323701357881201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194991901317764935143841601 146243925988323701357881201)
          ·
            refine ⟨109682944491242776018410901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146243925988323701357881201 109682944491242776018410901)
            ·
              refine ⟨5141388023027005125863011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109682944491242776018410901 5141388023027005125863011)
              ·
                refine ⟨7712082034540507688794517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5141388023027005125863011 7712082034540507688794517)
                ·
                  refine ⟨361503845369086297912243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7712082034540507688794517 361503845369086297912243)
                  ·
                    rfl

theorem cell23_6336236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 6].length) (baseStart_6336236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336236 prefixEnd_6336236 := by exact prefixLift 6336236
  have htrace : WordTrace (prefixWord ++ tailWord_6336236) baseStart_6336236 baseEnd_6336236 := by
    simpa [prefixWord, tailWord_6336236, baseEnd_6336236] using wordTrace_append hprefix tailTrace_6336236
  have hstable : (prefixWord ++ tailWord_6336236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336236).length < 2 ^ (prefixWord ++ tailWord_6336236).sum := by decide
  have hdescent : baseEnd_6336236 < baseStart_6336236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336256 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 6, 3, 2]
def baseStart_6336256 : Nat := 118140960795 + 6336256 * 2 ^ 59
def prefixEnd_6336256 : Nat := 4983230072969 + 3 ^ 40 * 6336256 * 2
def baseEnd_6336256 : Nat := 3253544877934866602960095

theorem tailTrace_6336256 : CollatzResearch.WordTrace tailWord_6336256 prefixEnd_6336256 3253544877934866602960095 := by
  unfold tailWord_6336256
  simp only [CollatzResearch.WordTrace]
  refine ⟨115551121066417066607918311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154068161421889422143891081 115551121066417066607918311)
  ·
    refine ⟨173326681599625599911877467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115551121066417066607918311 173326681599625599911877467)
    ·
      refine ⟨259990022399438399867816201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173326681599625599911877467 259990022399438399867816201)
      ·
        refine ⟨194992516799578799900862151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259990022399438399867816201 194992516799578799900862151)
        ·
          refine ⟨292488775199368199851293227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194992516799578799900862151 292488775199368199851293227)
          ·
            refine ⟨438733162799052299776939841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292488775199368199851293227 438733162799052299776939841)
            ·
              refine ⟨329049872099289224832704881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438733162799052299776939841 329049872099289224832704881)
              ·
                refine ⟨246787404074466918624528661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329049872099289224832704881 246787404074466918624528661)
                ·
                  refine ⟨11568159565990636810524781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 246787404074466918624528661 11568159565990636810524781)
                  ·
                    refine ⟨4338059837246488803946793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11568159565990636810524781 4338059837246488803946793)
                    ·
                      refine ⟨3253544877934866602960095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338059837246488803946793 3253544877934866602960095)
                      ·
                        rfl

theorem cell23_6336256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6, 3, 2].length) (baseStart_6336256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336256 prefixEnd_6336256 := by exact prefixLift 6336256
  have htrace : WordTrace (prefixWord ++ tailWord_6336256) baseStart_6336256 baseEnd_6336256 := by
    simpa [prefixWord, tailWord_6336256, baseEnd_6336256] using wordTrace_append hprefix tailTrace_6336256
  have hstable : (prefixWord ++ tailWord_6336256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336256).length < 2 ^ (prefixWord ++ tailWord_6336256).sum := by decide
  have hdescent : baseEnd_6336256 < baseStart_6336256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336274 : List Nat := [3, 2, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_6336274 : Nat := 118140960795 + 6336274 * 2 ^ 59
def prefixEnd_6336274 : Nat := 4983230072969 + 3 ^ 40 * 6336274 * 2
def baseEnd_6336274 : Nat := 1084518040195549177511671

theorem tailTrace_6336274 : CollatzResearch.WordTrace tailWord_6336274 prefixEnd_6336274 1084518040195549177511671 := by
  unfold tailWord_6336274
  simp only [CollatzResearch.WordTrace]
  refine ⟨57775724661692230572497969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154068599097845948193327917 57775724661692230572497969)
  ·
    refine ⟨43331793496269172929373477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57775724661692230572497969 43331793496269172929373477)
    ·
      refine ⟨8124711280550469924257527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43331793496269172929373477 8124711280550469924257527)
      ·
        refine ⟨12187066920825704886386291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8124711280550469924257527 12187066920825704886386291)
        ·
          refine ⟨18280600381238557329579437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12187066920825704886386291 18280600381238557329579437)
          ·
            refine ⟨6855225142964458998592289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18280600381238557329579437 6855225142964458998592289)
            ·
              refine ⟨5141418857223344248944217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6855225142964458998592289 5141418857223344248944217)
              ·
                refine ⟨3856064142917508186708163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5141418857223344248944217 3856064142917508186708163)
                ·
                  refine ⟨5784096214376262280062245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856064142917508186708163 5784096214376262280062245)
                  ·
                    refine ⟨1084518040195549177511671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5784096214376262280062245 1084518040195549177511671)
                    ·
                      rfl

theorem cell23_6336274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_6336274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336274 prefixEnd_6336274 := by exact prefixLift 6336274
  have htrace : WordTrace (prefixWord ++ tailWord_6336274) baseStart_6336274 baseEnd_6336274 := by
    simpa [prefixWord, tailWord_6336274, baseEnd_6336274] using wordTrace_append hprefix tailTrace_6336274
  have hstable : (prefixWord ++ tailWord_6336274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336274).length < 2 ^ (prefixWord ++ tailWord_6336274).sum := by decide
  have hdescent : baseEnd_6336274 < baseStart_6336274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336296 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 1, 6]
def baseStart_6336296 : Nat := 118140960795 + 6336296 * 2 ^ 59
def prefixEnd_6336296 : Nat := 4983230072969 + 3 ^ 40 * 6336296 * 2
def baseEnd_6336296 : Nat := 1084521805720348815486637

theorem tailTrace_6336296 : CollatzResearch.WordTrace tailWord_6336296 prefixEnd_6336296 1084521805720348815486637 := by
  unfold tailWord_6336296
  simp only [CollatzResearch.WordTrace]
  refine ⟨115551850526344610023646371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154069134035126146698195161 115551850526344610023646371)
  ·
    refine ⟨173327775789516915035469557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115551850526344610023646371 173327775789516915035469557)
    ·
      refine ⟨16249478980267210784575271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173327775789516915035469557 16249478980267210784575271)
      ·
        refine ⟨24374218470400816176862907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16249478980267210784575271 24374218470400816176862907)
        ·
          refine ⟨36561327705601224265294361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24374218470400816176862907 36561327705601224265294361)
          ·
            refine ⟨27420995779200918198970771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36561327705601224265294361 27420995779200918198970771)
            ·
              refine ⟨41131493668801377298456157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27420995779200918198970771 41131493668801377298456157)
              ·
                refine ⟨15424310125800516486921059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41131493668801377298456157 15424310125800516486921059)
                ·
                  refine ⟨23136465188700774730381589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15424310125800516486921059 23136465188700774730381589)
                  ·
                    refine ⟨1084521805720348815486637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23136465188700774730381589 1084521805720348815486637)
                    ·
                      rfl

theorem cell23_6336296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_6336296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336296 prefixEnd_6336296 := by exact prefixLift 6336296
  have htrace : WordTrace (prefixWord ++ tailWord_6336296) baseStart_6336296 baseEnd_6336296 := by
    simpa [prefixWord, tailWord_6336296, baseEnd_6336296] using wordTrace_append hprefix tailTrace_6336296
  have hstable : (prefixWord ++ tailWord_6336296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336296).length < 2 ^ (prefixWord ++ tailWord_6336296).sum := by decide
  have hdescent : baseEnd_6336296 < baseStart_6336296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336303 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 3, 2, 2]
def baseStart_6336303 : Nat := 118140960795 + 6336303 * 2 ^ 59
def prefixEnd_6336303 : Nat := 4983230072969 + 3 ^ 40 * 6336303 * 2
def baseEnd_6336303 : Nat := 3253569011525627919072379

theorem tailTrace_6336303 : CollatzResearch.WordTrace tailWord_6336303 prefixEnd_6336303 3253569011525627919072379 := by
  unfold tailWord_6336303
  simp only [CollatzResearch.WordTrace]
  refine ⟨231103956363663860242797563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154069304242442573495198375 231103956363663860242797563)
  ·
    refine ⟨346655934545495790364196345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231103956363663860242797563 346655934545495790364196345)
    ·
      refine ⟨259991950909121842773147259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346655934545495790364196345 259991950909121842773147259)
      ·
        refine ⟨389987926363682764159720889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259991950909121842773147259 389987926363682764159720889)
        ·
          refine ⟨292490944772762073119790667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389987926363682764159720889 292490944772762073119790667)
          ·
            refine ⟨438736417159143109679686001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292490944772762073119790667 438736417159143109679686001)
            ·
              refine ⟨329052312869357332259764501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438736417159143109679686001 329052312869357332259764501)
              ·
                refine ⟨15424327165751124949676461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 329052312869357332259764501 15424327165751124949676461)
                ·
                  refine ⟨5784122687156671856128673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15424327165751124949676461 5784122687156671856128673)
                  ·
                    refine ⟨4338092015367503892096505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5784122687156671856128673 4338092015367503892096505)
                    ·
                      refine ⟨3253569011525627919072379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338092015367503892096505 3253569011525627919072379)
                      ·
                        rfl

theorem cell23_6336303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 2, 2].length) (baseStart_6336303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336303 prefixEnd_6336303 := by exact prefixLift 6336303
  have htrace : WordTrace (prefixWord ++ tailWord_6336303) baseStart_6336303 baseEnd_6336303 := by
    simpa [prefixWord, tailWord_6336303, baseEnd_6336303] using wordTrace_append hprefix tailTrace_6336303
  have hstable : (prefixWord ++ tailWord_6336303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336303).length < 2 ^ (prefixWord ++ tailWord_6336303).sum := by decide
  have hdescent : baseEnd_6336303 < baseStart_6336303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336307 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 2, 3, 2]
def baseStart_6336307 : Nat := 118140960795 + 6336307 * 2 ^ 59
def prefixEnd_6336307 : Nat := 4983230072969 + 3 ^ 40 * 6336307 * 2
def baseEnd_6336307 : Nat := 3253571065448245903422361

theorem tailTrace_6336307 : CollatzResearch.WordTrace tailWord_6336307 prefixEnd_6336307 3253571065448245903422361 := by
  unfold tailWord_6336307
  simp only [CollatzResearch.WordTrace]
  refine ⟨231104102255649368925943175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154069401503766245950628783 231104102255649368925943175)
  ·
    refine ⟨346656153383474053388914763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231104102255649368925943175 346656153383474053388914763)
    ·
      refine ⟨519984230075211080083372145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346656153383474053388914763 519984230075211080083372145)
      ·
        refine ⟨389988172556408310062529109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519984230075211080083372145 389988172556408310062529109)
        ·
          refine ⟨4570173897145409883545263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 389988172556408310062529109 4570173897145409883545263)
          ·
            refine ⟨6855260845718114825317895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4570173897145409883545263 6855260845718114825317895)
            ·
              refine ⟨10282891268577172237976843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6855260845718114825317895 10282891268577172237976843)
              ·
                refine ⟨15424336902865758356965265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10282891268577172237976843 15424336902865758356965265)
                ·
                  refine ⟨11568252677149318767723949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15424336902865758356965265 11568252677149318767723949)
                  ·
                    refine ⟨4338094753930994537896481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11568252677149318767723949 4338094753930994537896481)
                    ·
                      refine ⟨3253571065448245903422361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338094753930994537896481 3253571065448245903422361)
                      ·
                        rfl

theorem cell23_6336307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 2, 3, 2].length) (baseStart_6336307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336307 prefixEnd_6336307 := by exact prefixLift 6336307
  have htrace : WordTrace (prefixWord ++ tailWord_6336307) baseStart_6336307 baseEnd_6336307 := by
    simpa [prefixWord, tailWord_6336307, baseEnd_6336307] using wordTrace_append hprefix tailTrace_6336307
  have hstable : (prefixWord ++ tailWord_6336307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336307).length < 2 ^ (prefixWord ++ tailWord_6336307).sum := by decide
  have hdescent : baseEnd_6336307 < baseStart_6336307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336316 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_6336316 : Nat := 118140960795 + 6336316 * 2 ^ 59
def prefixEnd_6336316 : Nat := 4983230072969 + 3 ^ 40 * 6336316 * 2
def baseEnd_6336316 : Nat := 3253575686774136368209819

theorem tailTrace_6336316 : CollatzResearch.WordTrace tailWord_6336316 prefixEnd_6336316 3253575686774136368209819 := by
  unfold tailWord_6336316
  simp only [CollatzResearch.WordTrace]
  refine ⟨115552215256308381731510401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154069620341744508975347201 115552215256308381731510401)
  ·
    refine ⟨86664161442231286298632801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115552215256308381731510401 86664161442231286298632801)
    ·
      refine ⟨64998121081673464723974601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86664161442231286298632801 64998121081673464723974601)
      ·
        refine ⟨48748590811255098542980951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64998121081673464723974601 48748590811255098542980951)
        ·
          refine ⟨73122886216882647814471427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48748590811255098542980951 73122886216882647814471427)
          ·
            refine ⟨109684329325323971721707141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73122886216882647814471427 109684329325323971721707141)
            ·
              refine ⟨20565811748498244697820089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109684329325323971721707141 20565811748498244697820089)
              ·
                refine ⟨15424358811373683523365067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20565811748498244697820089 15424358811373683523365067)
                ·
                  refine ⟨23136538217060525285047601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15424358811373683523365067 23136538217060525285047601)
                  ·
                    refine ⟨17352403662795393963785701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23136538217060525285047601 17352403662795393963785701)
                    ·
                      refine ⟨3253575686774136368209819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17352403662795393963785701 3253575686774136368209819)
                      ·
                        rfl

theorem cell23_6336316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_6336316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336316 prefixEnd_6336316 := by exact prefixLift 6336316
  have htrace : WordTrace (prefixWord ++ tailWord_6336316) baseStart_6336316 baseEnd_6336316 := by
    simpa [prefixWord, tailWord_6336316, baseEnd_6336316] using wordTrace_append hprefix tailTrace_6336316
  have hstable : (prefixWord ++ tailWord_6336316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336316).length < 2 ^ (prefixWord ++ tailWord_6336316).sum := by decide
  have hdescent : baseEnd_6336316 < baseStart_6336316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336323 : List Nat := [1, 1, 1, 3, 1, 6, 1, 3, 1, 2, 3]
def baseStart_6336323 : Nat := 118140960795 + 6336323 * 2 ^ 59
def prefixEnd_6336323 : Nat := 4983230072969 + 3 ^ 40 * 6336323 * 2
def baseEnd_6336323 : Nat := 3253579281138717840822287

theorem tailTrace_6336323 : CollatzResearch.WordTrace tailWord_6336323 prefixEnd_6336323 3253579281138717840822287 := by
  unfold tailWord_6336323
  simp only [CollatzResearch.WordTrace]
  refine ⟨231104685823591403658525623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154069790549060935772350415 231104685823591403658525623)
  ·
    refine ⟨346657028735387105487788435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231104685823591403658525623 346657028735387105487788435)
    ·
      refine ⟨519985543103080658231682653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346657028735387105487788435 519985543103080658231682653)
      ·
        refine ⟨194994578663655246836880995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 519985543103080658231682653 194994578663655246836880995)
        ·
          refine ⟨292491867995482870255321493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194994578663655246836880995 292491867995482870255321493)
          ·
            refine ⟨13710556312288259543218195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 292491867995482870255321493 13710556312288259543218195)
            ·
              refine ⟨20565834468432389314827293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13710556312288259543218195 20565834468432389314827293)
              ·
                refine ⟨7712187925662145993060235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20565834468432389314827293 7712187925662145993060235)
                ·
                  refine ⟨11568281888493218989590353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7712187925662145993060235 11568281888493218989590353)
                  ·
                    refine ⟨8676211416369914242192765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11568281888493218989590353 8676211416369914242192765)
                    ·
                      refine ⟨3253579281138717840822287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8676211416369914242192765 3253579281138717840822287)
                      ·
                        rfl

theorem cell23_6336323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_6336323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336323 prefixEnd_6336323 := by exact prefixLift 6336323
  have htrace : WordTrace (prefixWord ++ tailWord_6336323) baseStart_6336323 baseEnd_6336323 := by
    simpa [prefixWord, tailWord_6336323, baseEnd_6336323] using wordTrace_append hprefix tailTrace_6336323
  have hstable : (prefixWord ++ tailWord_6336323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336323).length < 2 ^ (prefixWord ++ tailWord_6336323).sum := by decide
  have hdescent : baseEnd_6336323 < baseStart_6336323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336337 : List Nat := [1, 2, 2, 1, 5, 1, 2, 4, 1, 2, 2]
def baseStart_6336337 : Nat := 118140960795 + 6336337 * 2 ^ 59
def prefixEnd_6336337 : Nat := 4983230072969 + 3 ^ 40 * 6336337 * 2
def baseEnd_6336337 : Nat := 3253586469867880786047223

theorem tailTrace_6336337 : CollatzResearch.WordTrace tailWord_6336337 prefixEnd_6336337 3253586469867880786047223 := by
  unfold tailWord_6336337
  simp only [CollatzResearch.WordTrace]
  refine ⟨231105196445540684049535265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154070130963693789366356843 231105196445540684049535265)
  ·
    refine ⟨173328897334155513037151449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231105196445540684049535265 173328897334155513037151449)
    ·
      refine ⟨129996673000616634777863587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173328897334155513037151449 129996673000616634777863587)
      ·
        refine ⟨194995009500924952166795381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129996673000616634777863587 194995009500924952166795381)
        ·
          refine ⟨18280782140711714265637067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194995009500924952166795381 18280782140711714265637067)
          ·
            refine ⟨27421173211067571398455601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18280782140711714265637067 27421173211067571398455601)
            ·
              refine ⟨20565879908300678548841701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27421173211067571398455601 20565879908300678548841701)
              ·
                refine ⟨3856102482806377227907819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20565879908300678548841701 3856102482806377227907819)
                ·
                  refine ⟨5784153724209565841861729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856102482806377227907819 5784153724209565841861729)
                  ·
                    refine ⟨4338115293157174381396297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5784153724209565841861729 4338115293157174381396297)
                    ·
                      refine ⟨3253586469867880786047223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338115293157174381396297 3253586469867880786047223)
                      ·
                        rfl

theorem cell23_6336337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 1, 2, 2].length) (baseStart_6336337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336337 prefixEnd_6336337 := by exact prefixLift 6336337
  have htrace : WordTrace (prefixWord ++ tailWord_6336337) baseStart_6336337 baseEnd_6336337 := by
    simpa [prefixWord, tailWord_6336337, baseEnd_6336337] using wordTrace_append hprefix tailTrace_6336337
  have hstable : (prefixWord ++ tailWord_6336337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336337).length < 2 ^ (prefixWord ++ tailWord_6336337).sum := by decide
  have hdescent : baseEnd_6336337 < baseStart_6336337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336396 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 2, 4, 3]
def baseStart_6336396 : Nat := 118140960795 + 6336396 * 2 ^ 59
def prefixEnd_6336396 : Nat := 4983230072969 + 3 ^ 40 * 6336396 * 2
def baseEnd_6336396 : Nat := 3253616765226496055209451

theorem tailTrace_6336396 : CollatzResearch.WordTrace tailWord_6336396 prefixEnd_6336396 3253616765226496055209451 := by
  unfold tailWord_6336396
  simp only [CollatzResearch.WordTrace]
  refine ⟨115553674176163468562966521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154071565568217958083955361 115553674176163468562966521)
  ·
    refine ⟨86665255632122601422224891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115553674176163468562966521 86665255632122601422224891)
    ·
      refine ⟨129997883448183902133337337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86665255632122601422224891 129997883448183902133337337)
      ·
        refine ⟨97498412586137926600003003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129997883448183902133337337 97498412586137926600003003)
        ·
          refine ⟨146247618879206889900004505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97498412586137926600003003 146247618879206889900004505)
          ·
            refine ⟨109685714159405167425003379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146247618879206889900004505 109685714159405167425003379)
            ·
              refine ⟨164528571239107751137505069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109685714159405167425003379 164528571239107751137505069)
              ·
                refine ⟨61698214214665406676564401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164528571239107751137505069 61698214214665406676564401)
                ·
                  refine ⟨46273660660999055007423301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61698214214665406676564401 46273660660999055007423301)
                  ·
                    refine ⟨8676311373937322813891869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46273660660999055007423301 8676311373937322813891869)
                    ·
                      refine ⟨3253616765226496055209451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8676311373937322813891869 3253616765226496055209451)
                      ·
                        rfl

theorem cell23_6336396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_6336396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336396 prefixEnd_6336396 := by exact prefixLift 6336396
  have htrace : WordTrace (prefixWord ++ tailWord_6336396) baseStart_6336396 baseEnd_6336396 := by
    simpa [prefixWord, tailWord_6336396, baseEnd_6336396] using wordTrace_append hprefix tailTrace_6336396
  have hstable : (prefixWord ++ tailWord_6336396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336396).length < 2 ^ (prefixWord ++ tailWord_6336396).sum := by decide
  have hdescent : baseEnd_6336396 < baseStart_6336396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336404 : List Nat := [2, 4, 2, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_6336404 : Nat := 118140960795 + 6336404 * 2 ^ 59
def prefixEnd_6336404 : Nat := 4983230072969 + 3 ^ 40 * 6336404 * 2
def baseEnd_6336404 : Nat := 3253620873071732023909415

theorem tailTrace_6336404 : CollatzResearch.WordTrace tailWord_6336404 prefixEnd_6336404 3253620873071732023909415 := by
  unfold tailWord_6336404
  simp only [CollatzResearch.WordTrace]
  refine ⟨115553820068148977246112133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154071760090865302994816177 115553820068148977246112133)
  ·
    refine ⟨21666341262777933233646025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115553820068148977246112133 21666341262777933233646025)
    ·
      refine ⟨16249755947083449925234519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21666341262777933233646025 16249755947083449925234519)
      ·
        refine ⟨24374633920625174887851779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16249755947083449925234519 24374633920625174887851779)
        ·
          refine ⟨36561950880937762331777669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24374633920625174887851779 36561950880937762331777669)
          ·
            refine ⟨6855365790175830437208313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36561950880937762331777669 6855365790175830437208313)
            ·
              refine ⟨5141524342631872827906235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6855365790175830437208313 5141524342631872827906235)
              ·
                refine ⟨7712286513947809241859353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5141524342631872827906235 7712286513947809241859353)
                ·
                  refine ⟨5784214885460856931394515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7712286513947809241859353 5784214885460856931394515)
                  ·
                    refine ⟨8676322328191285397091773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5784214885460856931394515 8676322328191285397091773)
                    ·
                      refine ⟨3253620873071732023909415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8676322328191285397091773 3253620873071732023909415)
                      ·
                        rfl

theorem cell23_6336404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_6336404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336404 prefixEnd_6336404 := by exact prefixLift 6336404
  have htrace : WordTrace (prefixWord ++ tailWord_6336404) baseStart_6336404 baseEnd_6336404 := by
    simpa [prefixWord, tailWord_6336404, baseEnd_6336404] using wordTrace_append hprefix tailTrace_6336404
  have hstable : (prefixWord ++ tailWord_6336404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336404).length < 2 ^ (prefixWord ++ tailWord_6336404).sum := by decide
  have hdescent : baseEnd_6336404 < baseStart_6336404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336414 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_6336414 : Nat := 118140960795 + 6336414 * 2 ^ 59
def prefixEnd_6336414 : Nat := 4983230072969 + 3 ^ 40 * 6336414 * 2
def baseEnd_6336414 : Nat := 3253626007878276984784369

theorem tailTrace_6336414 : CollatzResearch.WordTrace tailWord_6336414 prefixEnd_6336414 3253626007878276984784369 := by
  unfold tailWord_6336414
  simp only [CollatzResearch.WordTrace]
  refine ⟨28888500608282715775011037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154072003244174484133392197 28888500608282715775011037)
  ·
    refine ⟨10833187728106018415629139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28888500608282715775011037 10833187728106018415629139)
    ·
      refine ⟨16249781592159027623443709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10833187728106018415629139 16249781592159027623443709)
      ·
        refine ⟨6093668097059635358791391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16249781592159027623443709 6093668097059635358791391)
        ·
          refine ⟨9140502145589453038187087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6093668097059635358791391 9140502145589453038187087)
          ·
            refine ⟨13710753218384179557280631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9140502145589453038187087 13710753218384179557280631)
            ·
              refine ⟨20566129827576269335920947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13710753218384179557280631 20566129827576269335920947)
              ·
                refine ⟨30849194741364404003881421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20566129827576269335920947 30849194741364404003881421)
                ·
                  refine ⟨11568448028011651501455533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30849194741364404003881421 11568448028011651501455533)
                  ·
                    refine ⟨4338168010504369313045825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11568448028011651501455533 4338168010504369313045825)
                    ·
                      refine ⟨3253626007878276984784369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338168010504369313045825 3253626007878276984784369)
                      ·
                        rfl

theorem cell23_6336414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_6336414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336414 prefixEnd_6336414 := by exact prefixLift 6336414
  have htrace : WordTrace (prefixWord ++ tailWord_6336414) baseStart_6336414 baseEnd_6336414 := by
    simpa [prefixWord, tailWord_6336414, baseEnd_6336414] using wordTrace_append hprefix tailTrace_6336414
  have hstable : (prefixWord ++ tailWord_6336414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336414).length < 2 ^ (prefixWord ++ tailWord_6336414).sum := by decide
  have hdescent : baseEnd_6336414 < baseStart_6336414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336483 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 4]
def baseStart_6336483 : Nat := 118140960795 + 6336483 * 2 ^ 59
def prefixEnd_6336483 : Nat := 4983230072969 + 3 ^ 40 * 6336483 * 2
def baseEnd_6336483 : Nat := 3253661438043437214821551

theorem tailTrace_6336483 : CollatzResearch.WordTrace tailWord_6336483 prefixEnd_6336483 3253661438043437214821551 := by
  unfold tailWord_6336483
  simp only [CollatzResearch.WordTrace]
  refine ⟨231110521503011750984350103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154073681002007833989566735 231110521503011750984350103)
  ·
    refine ⟨346665782254517626476525155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231110521503011750984350103 346665782254517626476525155)
    ·
      refine ⟨519998673381776439714787733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346665782254517626476525155 519998673381776439714787733)
      ·
        refine ⟨24374937814770770611630675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 519998673381776439714787733 24374937814770770611630675)
        ·
          refine ⟨36562406722156155917446013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24374937814770770611630675 36562406722156155917446013)
          ·
            refine ⟨13710902520808558469042255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36562406722156155917446013 13710902520808558469042255)
            ·
              refine ⟨20566353781212837703563383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13710902520808558469042255 20566353781212837703563383)
              ·
                refine ⟨30849530671819256555345075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20566353781212837703563383 30849530671819256555345075)
                ·
                  refine ⟨46274296007728884833017613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30849530671819256555345075 46274296007728884833017613)
                  ·
                    refine ⟨17352861002898331812381605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46274296007728884833017613 17352861002898331812381605)
                    ·
                      refine ⟨3253661438043437214821551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17352861002898331812381605 3253661438043437214821551)
                      ·
                        rfl

theorem cell23_6336483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_6336483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336483 prefixEnd_6336483 := by exact prefixLift 6336483
  have htrace : WordTrace (prefixWord ++ tailWord_6336483) baseStart_6336483 baseEnd_6336483 := by
    simpa [prefixWord, tailWord_6336483, baseEnd_6336483] using wordTrace_append hprefix tailTrace_6336483
  have hstable : (prefixWord ++ tailWord_6336483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336483).length < 2 ^ (prefixWord ++ tailWord_6336483).sum := by decide
  have hdescent : baseEnd_6336483 < baseStart_6336483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336496 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 6]
def baseStart_6336496 : Nat := 118140960795 + 6336496 * 2 ^ 59
def prefixEnd_6336496 : Nat := 4983230072969 + 3 ^ 40 * 6336496 * 2
def baseEnd_6336496 : Nat := 3253668113291945663958991

theorem tailTrace_6336496 : CollatzResearch.WordTrace tailWord_6336496 prefixEnd_6336496 3253668113291945663958991 := by
  unfold tailWord_6336496
  simp only [CollatzResearch.WordTrace]
  refine ⟨115555497825982327102286671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154073997101309769469715561 115555497825982327102286671)
  ·
    refine ⟨173333246738973490653430007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115555497825982327102286671 173333246738973490653430007)
    ·
      refine ⟨259999870108460235980145011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173333246738973490653430007 259999870108460235980145011)
      ·
        refine ⟨389999805162690353970217517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259999870108460235980145011 389999805162690353970217517)
        ·
          refine ⟨146249926936008882738831569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389999805162690353970217517 146249926936008882738831569)
          ·
            refine ⟨109687445202006662054123677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146249926936008882738831569 109687445202006662054123677)
            ·
              refine ⟨41132791950752498270296379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109687445202006662054123677 41132791950752498270296379)
              ·
                refine ⟨61699187926128747405444569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41132791950752498270296379 61699187926128747405444569)
                ·
                  refine ⟨46274390944596560554083427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61699187926128747405444569 46274390944596560554083427)
                  ·
                    refine ⟨69411586416894840831125141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46274390944596560554083427 69411586416894840831125141)
                    ·
                      refine ⟨3253668113291945663958991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69411586416894840831125141 3253668113291945663958991)
                      ·
                        rfl

theorem cell23_6336496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_6336496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336496 prefixEnd_6336496 := by exact prefixLift 6336496
  have htrace : WordTrace (prefixWord ++ tailWord_6336496) baseStart_6336496 baseEnd_6336496 := by
    simpa [prefixWord, tailWord_6336496, baseEnd_6336496] using wordTrace_append hprefix tailTrace_6336496
  have hstable : (prefixWord ++ tailWord_6336496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336496).length < 2 ^ (prefixWord ++ tailWord_6336496).sum := by decide
  have hdescent : baseEnd_6336496 < baseStart_6336496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336560 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 4, 3, 2]
def baseStart_6336560 : Nat := 118140960795 + 6336560 * 2 ^ 59
def prefixEnd_6336560 : Nat := 4983230072969 + 3 ^ 40 * 6336560 * 2
def baseEnd_6336560 : Nat := 3253700976053833413558697

theorem tailTrace_6336560 : CollatzResearch.WordTrace tailWord_6336560 prefixEnd_6336560 3253700976053833413558697 := by
  unfold tailWord_6336560
  simp only [CollatzResearch.WordTrace]
  refine ⟨115556664961866396567451567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154075553282488528756602089 115556664961866396567451567)
  ·
    refine ⟨173334997442799594851177351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115556664961866396567451567 173334997442799594851177351)
    ·
      refine ⟨260002496164199392276766027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173334997442799594851177351 260002496164199392276766027)
      ·
        refine ⟨390003744246299088415149041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260002496164199392276766027 390003744246299088415149041)
        ·
          refine ⟨292502808184724316311361781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390003744246299088415149041 292502808184724316311361781)
          ·
            refine ⟨27422138267317904654190167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 292502808184724316311361781 27422138267317904654190167)
            ·
              refine ⟨41133207400976856981285251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27422138267317904654190167 41133207400976856981285251)
              ·
                refine ⟨61699811101465285471927877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41133207400976856981285251 61699811101465285471927877)
                ·
                  refine ⟨11568714581524741025986477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61699811101465285471927877 11568714581524741025986477)
                  ·
                    refine ⟨4338267968071777884744929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11568714581524741025986477 4338267968071777884744929)
                    ·
                      refine ⟨3253700976053833413558697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338267968071777884744929 3253700976053833413558697)
                      ·
                        rfl

theorem cell23_6336560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4, 3, 2].length) (baseStart_6336560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336560 prefixEnd_6336560 := by exact prefixLift 6336560
  have htrace : WordTrace (prefixWord ++ tailWord_6336560) baseStart_6336560 baseEnd_6336560 := by
    simpa [prefixWord, tailWord_6336560, baseEnd_6336560] using wordTrace_append hprefix tailTrace_6336560
  have hstable : (prefixWord ++ tailWord_6336560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336560).length < 2 ^ (prefixWord ++ tailWord_6336560).sum := by decide
  have hdescent : baseEnd_6336560 < baseStart_6336560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336567 : List Nat := [1, 1, 3, 1, 2, 2, 2, 6, 1, 1, 3]
def baseStart_6336567 : Nat := 118140960795 + 6336567 * 2 ^ 59
def prefixEnd_6336567 : Nat := 4983230072969 + 3 ^ 40 * 6336567 * 2
def baseEnd_6336567 : Nat := 3253704570418414886171165

theorem tailTrace_6336567 : CollatzResearch.WordTrace tailWord_6336567 prefixEnd_6336567 3253704570418414886171165 := by
  unfold tailWord_6336567
  simp only [CollatzResearch.WordTrace]
  refine ⟨231113585234707433330407955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154075723489804955553605303 231113585234707433330407955)
  ·
    refine ⟨346670377852061149995611933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231113585234707433330407955 346670377852061149995611933)
    ·
      refine ⟨130001391694522931248354475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346670377852061149995611933 130001391694522931248354475)
      ·
        refine ⟨195002087541784396872531713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130001391694522931248354475 195002087541784396872531713)
        ·
          refine ⟨146251565656338297654398785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195002087541784396872531713 146251565656338297654398785)
          ·
            refine ⟨109688674242253723240799089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146251565656338297654398785 109688674242253723240799089)
            ·
              refine ⟨82266505681690292430599317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109688674242253723240799089 82266505681690292430599317)
              ·
                refine ⟨3856242453829232457684343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82266505681690292430599317 3856242453829232457684343)
                ·
                  refine ⟨5784363680743848686526515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856242453829232457684343 5784363680743848686526515)
                  ·
                    refine ⟨8676545521115773029789773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5784363680743848686526515 8676545521115773029789773)
                    ·
                      refine ⟨3253704570418414886171165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8676545521115773029789773 3253704570418414886171165)
                      ·
                        rfl

theorem cell23_6336567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 1, 1, 3].length) (baseStart_6336567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336567 prefixEnd_6336567 := by exact prefixLift 6336567
  have htrace : WordTrace (prefixWord ++ tailWord_6336567) baseStart_6336567 baseEnd_6336567 := by
    simpa [prefixWord, tailWord_6336567, baseEnd_6336567] using wordTrace_append hprefix tailTrace_6336567
  have hstable : (prefixWord ++ tailWord_6336567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336567).length < 2 ^ (prefixWord ++ tailWord_6336567).sum := by decide
  have hdescent : baseEnd_6336567 < baseStart_6336567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336574 : List Nat := [4, 2, 1, 3, 2, 2, 2, 1, 6]
def baseStart_6336574 : Nat := 118140960795 + 6336574 * 2 ^ 59
def prefixEnd_6336574 : Nat := 4983230072969 + 3 ^ 40 * 6336574 * 2
def baseEnd_6336574 : Nat := 361523129420332928753737

theorem tailTrace_6336574 : CollatzResearch.WordTrace tailWord_6336574 prefixEnd_6336574 361523129420332928753737 := by
  unfold tailWord_6336574
  simp only [CollatzResearch.WordTrace]
  refine ⟨28889230068210259190739097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154075893697121382350608517 28889230068210259190739097)
  ·
    refine ⟨21666922551157694393054323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28889230068210259190739097 21666922551157694393054323)
    ·
      refine ⟨32500383826736541589581485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21666922551157694393054323 32500383826736541589581485)
      ·
        refine ⟨12187643935026203096093057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32500383826736541589581485 12187643935026203096093057)
        ·
          refine ⟨9140732951269652322069793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12187643935026203096093057 9140732951269652322069793)
          ·
            refine ⟨6855549713452239241552345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9140732951269652322069793 6855549713452239241552345)
            ·
              refine ⟨5141662285089179431164259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6855549713452239241552345 5141662285089179431164259)
              ·
                refine ⟨7712493427633769146746389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5141662285089179431164259 7712493427633769146746389)
                ·
                  refine ⟨361523129420332928753737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7712493427633769146746389 361523129420332928753737)
                  ·
                    rfl

theorem cell23_6336574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_6336574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336574 prefixEnd_6336574 := by exact prefixLift 6336574
  have htrace : WordTrace (prefixWord ++ tailWord_6336574) baseStart_6336574 baseEnd_6336574 := by
    simpa [prefixWord, tailWord_6336574, baseEnd_6336574] using wordTrace_append hprefix tailTrace_6336574
  have hstable : (prefixWord ++ tailWord_6336574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336574).length < 2 ^ (prefixWord ++ tailWord_6336574).sum := by decide
  have hdescent : baseEnd_6336574 < baseStart_6336574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336583 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 1, 6]
def baseStart_6336583 : Nat := 118140960795 + 6336583 * 2 ^ 59
def prefixEnd_6336583 : Nat := 4983230072969 + 3 ^ 40 * 6336583 * 2
def baseEnd_6336583 : Nat := 1084570928702962274523697

theorem tailTrace_6336583 : CollatzResearch.WordTrace tailWord_6336583 prefixEnd_6336583 1084570928702962274523697 := by
  unfold tailWord_6336583
  simp only [CollatzResearch.WordTrace]
  refine ⟨231114168802649468062990403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154076112535099645375326935 231114168802649468062990403)
  ·
    refine ⟨346671253203974202094485605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231114168802649468062990403 346671253203974202094485605)
    ·
      refine ⟨65000859975745162892716051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346671253203974202094485605 65000859975745162892716051)
      ·
        refine ⟨97501289963617744339074077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65000859975745162892716051 97501289963617744339074077)
        ·
          refine ⟨36562983736356654127152779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97501289963617744339074077 36562983736356654127152779)
          ·
            refine ⟨54844475604534981190729169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36562983736356654127152779 54844475604534981190729169)
            ·
              refine ⟨41133356703401235893046877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54844475604534981190729169 41133356703401235893046877)
              ·
                refine ⟨15425008763775463459892579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41133356703401235893046877 15425008763775463459892579)
                ·
                  refine ⟨23137513145663195189838869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15425008763775463459892579 23137513145663195189838869)
                  ·
                    refine ⟨1084570928702962274523697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23137513145663195189838869 1084570928702962274523697)
                    ·
                      rfl

theorem cell23_6336583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_6336583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336583 prefixEnd_6336583 := by exact prefixLift 6336583
  have htrace : WordTrace (prefixWord ++ tailWord_6336583) baseStart_6336583 baseEnd_6336583 := by
    simpa [prefixWord, tailWord_6336583, baseEnd_6336583] using wordTrace_append hprefix tailTrace_6336583
  have hstable : (prefixWord ++ tailWord_6336583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336583).length < 2 ^ (prefixWord ++ tailWord_6336583).sum := by decide
  have hdescent : baseEnd_6336583 < baseStart_6336583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336590 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_6336590 : Nat := 118140960795 + 6336590 * 2 ^ 59
def prefixEnd_6336590 : Nat := 4983230072969 + 3 ^ 40 * 6336590 * 2
def baseEnd_6336590 : Nat := 3253716380473468296183559

theorem tailTrace_6336590 : CollatzResearch.WordTrace tailWord_6336590 prefixEnd_6336590 3253716380473468296183559 := by
  unfold tailWord_6336590
  simp only [CollatzResearch.WordTrace]
  refine ⟨28889303014203013532311903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154076282742416072172330149 28889303014203013532311903)
  ·
    refine ⟨43333954521304520298467855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28889303014203013532311903 43333954521304520298467855)
    ·
      refine ⟨65000931781956780447701783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43333954521304520298467855 65000931781956780447701783)
      ·
        refine ⟨97501397672935170671552675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65000931781956780447701783 97501397672935170671552675)
        ·
          refine ⟨146252096509402756007329013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97501397672935170671552675 146252096509402756007329013)
          ·
            refine ⟨13711134047756508375687095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146252096509402756007329013 13711134047756508375687095)
            ·
              refine ⟨20566701071634762563530643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13711134047756508375687095 20566701071634762563530643)
              ·
                refine ⟨30850051607452143845295965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20566701071634762563530643 30850051607452143845295965)
                ·
                  refine ⟨11568769352794553941985987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30850051607452143845295965 11568769352794553941985987)
                  ·
                    refine ⟨17353154029191830912978981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11568769352794553941985987 17353154029191830912978981)
                    ·
                      refine ⟨3253716380473468296183559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17353154029191830912978981 3253716380473468296183559)
                      ·
                        rfl

theorem cell23_6336590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_6336590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336590 prefixEnd_6336590 := by exact prefixLift 6336590
  have htrace : WordTrace (prefixWord ++ tailWord_6336590) baseStart_6336590 baseEnd_6336590 := by
    simpa [prefixWord, tailWord_6336590, baseEnd_6336590] using wordTrace_append hprefix tailTrace_6336590
  have hstable : (prefixWord ++ tailWord_6336590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336590).length < 2 ^ (prefixWord ++ tailWord_6336590).sum := by decide
  have hdescent : baseEnd_6336590 < baseStart_6336590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336594 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_6336594 : Nat := 118140960795 + 6336594 * 2 ^ 59
def prefixEnd_6336594 : Nat := 4983230072969 + 3 ^ 40 * 6336594 * 2
def baseEnd_6336594 : Nat := 3253718434396086280533541

theorem tailTrace_6336594 : CollatzResearch.WordTrace tailWord_6336594 prefixEnd_6336594 3253718434396086280533541 := by
  unfold tailWord_6336594
  simp only [CollatzResearch.WordTrace]
  refine ⟨57778642501402404235410209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154076380003739744627760557 57778642501402404235410209)
  ·
    refine ⟨43333981876051803176557657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57778642501402404235410209 43333981876051803176557657)
    ·
      refine ⟨32500486407038852382418243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43333981876051803176557657 32500486407038852382418243)
      ·
        refine ⟨48750729610558278573627365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32500486407038852382418243 48750729610558278573627365)
        ·
          refine ⟨9140761801979677232555131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48750729610558278573627365 9140761801979677232555131)
          ·
            refine ⟨13711142702969515848832697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9140761801979677232555131 13711142702969515848832697)
            ·
              refine ⟨10283357027227136886624523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13711142702969515848832697 10283357027227136886624523)
              ·
                refine ⟨15425035540840705329936785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10283357027227136886624523 15425035540840705329936785)
                ·
                  refine ⟨11568776655630528997452589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15425035540840705329936785 11568776655630528997452589)
                  ·
                    refine ⟨4338291245861448374044721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11568776655630528997452589 4338291245861448374044721)
                    ·
                      refine ⟨3253718434396086280533541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338291245861448374044721 3253718434396086280533541)
                      ·
                        rfl

theorem cell23_6336594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_6336594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336594 prefixEnd_6336594 := by exact prefixLift 6336594
  have htrace : WordTrace (prefixWord ++ tailWord_6336594) baseStart_6336594 baseEnd_6336594 := by
    simpa [prefixWord, tailWord_6336594, baseEnd_6336594] using wordTrace_append hprefix tailTrace_6336594
  have hstable : (prefixWord ++ tailWord_6336594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336594).length < 2 ^ (prefixWord ++ tailWord_6336594).sum := by decide
  have hdescent : baseEnd_6336594 < baseStart_6336594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336618 : List Nat := [3, 1, 3, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_6336618 : Nat := 118140960795 + 6336618 * 2 ^ 59
def prefixEnd_6336618 : Nat := 4983230072969 + 3 ^ 40 * 6336618 * 2
def baseEnd_6336618 : Nat := 3253730757931794186633431

theorem tailTrace_6336618 : CollatzResearch.WordTrace tailWord_6336618 prefixEnd_6336618 3253730757931794186633431 := by
  unfold tailWord_6336618
  simp only [CollatzResearch.WordTrace]
  refine ⟨57778861339380667260128627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154076963571681779360343005 57778861339380667260128627)
  ·
    refine ⟨86668292009071000890192941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57778861339380667260128627 86668292009071000890192941)
    ·
      refine ⟨32500609503401625333822353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86668292009071000890192941 32500609503401625333822353)
      ·
        refine ⟨24375457127551219000366765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32500609503401625333822353 24375457127551219000366765)
        ·
          refine ⟨9140796422831707125137537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24375457127551219000366765 9140796422831707125137537)
          ·
            refine ⟨6855597317123780343853153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9140796422831707125137537 6855597317123780343853153)
            ·
              refine ⟨5141697987842835257889865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6855597317123780343853153 5141697987842835257889865)
              ·
                refine ⟨3856273490882126443417399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5141697987842835257889865 3856273490882126443417399)
                ·
                  refine ⟨5784410236323189665126099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856273490882126443417399 5784410236323189665126099)
                  ·
                    refine ⟨8676615354484784497689149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5784410236323189665126099 8676615354484784497689149)
                    ·
                      refine ⟨3253730757931794186633431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8676615354484784497689149 3253730757931794186633431)
                      ·
                        rfl

theorem cell23_6336618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_6336618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336618 prefixEnd_6336618 := by exact prefixLift 6336618
  have htrace : WordTrace (prefixWord ++ tailWord_6336618) baseStart_6336618 baseEnd_6336618 := by
    simpa [prefixWord, tailWord_6336618, baseEnd_6336618] using wordTrace_append hprefix tailTrace_6336618
  have hstable : (prefixWord ++ tailWord_6336618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336618).length < 2 ^ (prefixWord ++ tailWord_6336618).sum := by decide
  have hdescent : baseEnd_6336618 < baseStart_6336618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336630 : List Nat := [5, 1, 1, 2, 1, 2, 3, 8]
def baseStart_6336630 : Nat := 118140960795 + 6336630 * 2 ^ 59
def prefixEnd_6336630 : Nat := 4983230072969 + 3 ^ 40 * 6336630 * 2
def baseEnd_6336630 : Nat := 120508774803690671840125

theorem tailTrace_6336630 : CollatzResearch.WordTrace tailWord_6336630 prefixEnd_6336630 120508774803690671840125 := by
  unfold tailWord_6336630
  simp only [CollatzResearch.WordTrace]
  refine ⟨14444742689592449693121959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154077255355652796726634229 14444742689592449693121959)
  ·
    refine ⟨21667114034388674539682939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14444742689592449693121959 21667114034388674539682939)
    ·
      refine ⟨32500671051583011809524409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21667114034388674539682939 32500671051583011809524409)
      ·
        refine ⟨24375503288687258857143307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32500671051583011809524409 24375503288687258857143307)
        ·
          refine ⟨36563254933030888285714961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24375503288687258857143307 36563254933030888285714961)
          ·
            refine ⟨27422441199773166214286221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36563254933030888285714961 27422441199773166214286221)
            ·
              refine ⟨10283415449914937330357333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27422441199773166214286221 10283415449914937330357333)
              ·
                refine ⟨120508774803690671840125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10283415449914937330357333 120508774803690671840125)
                ·
                  rfl

theorem cell23_6336630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_6336630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336630 prefixEnd_6336630 := by exact prefixLift 6336630
  have htrace : WordTrace (prefixWord ++ tailWord_6336630) baseStart_6336630 baseEnd_6336630 := by
    simpa [prefixWord, tailWord_6336630, baseEnd_6336630] using wordTrace_append hprefix tailTrace_6336630
  have hstable : (prefixWord ++ tailWord_6336630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336630).length < 2 ^ (prefixWord ++ tailWord_6336630).sum := by decide
  have hdescent : baseEnd_6336630 < baseStart_6336630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336640 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 6, 1, 3]
def baseStart_6336640 : Nat := 118140960795 + 6336640 * 2 ^ 59
def prefixEnd_6336640 : Nat := 4983230072969 + 3 ^ 40 * 6336640 * 2
def baseEnd_6336640 : Nat := 3253742054506193100558329

theorem tailTrace_6336640 : CollatzResearch.WordTrace tailWord_6336640 prefixEnd_6336640 3253742054506193100558329 := by
  unfold tailWord_6336640
  simp only [CollatzResearch.WordTrace]
  refine ⟨115558123881721483398907687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154077498508961977865210249 115558123881721483398907687)
  ·
    refine ⟨173337185822582225098361531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115558123881721483398907687 173337185822582225098361531)
    ·
      refine ⟨260005778733873337647542297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173337185822582225098361531 260005778733873337647542297)
      ·
        refine ⟨195004334050405003235656723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260005778733873337647542297 195004334050405003235656723)
        ·
          refine ⟨292506501075607504853485085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195004334050405003235656723 292506501075607504853485085)
          ·
            refine ⟨109689937903352814320056907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292506501075607504853485085 109689937903352814320056907)
            ·
              refine ⟨164534906855029221480085361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109689937903352814320056907 164534906855029221480085361)
              ·
                refine ⟨123401180141271916110064021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164534906855029221480085361 123401180141271916110064021)
                ·
                  refine ⟨5784430319122121067659251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123401180141271916110064021 5784430319122121067659251)
                  ·
                    refine ⟨8676645478683181601488877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5784430319122121067659251 8676645478683181601488877)
                    ·
                      refine ⟨3253742054506193100558329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8676645478683181601488877 3253742054506193100558329)
                      ·
                        rfl

theorem cell23_6336640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_6336640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336640 prefixEnd_6336640 := by exact prefixLift 6336640
  have htrace : WordTrace (prefixWord ++ tailWord_6336640) baseStart_6336640 baseEnd_6336640 := by
    simpa [prefixWord, tailWord_6336640, baseEnd_6336640] using wordTrace_append hprefix tailTrace_6336640
  have hstable : (prefixWord ++ tailWord_6336640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336640).length < 2 ^ (prefixWord ++ tailWord_6336640).sum := by decide
  have hdescent : baseEnd_6336640 < baseStart_6336640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336674 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_6336674 : Nat := 118140960795 + 6336674 * 2 ^ 59
def prefixEnd_6336674 : Nat := 4983230072969 + 3 ^ 40 * 6336674 * 2
def baseEnd_6336674 : Nat := 3253759512848445967533173

theorem tailTrace_6336674 : CollatzResearch.WordTrace tailWord_6336674 prefixEnd_6336674 3253759512848445967533173 := by
  unfold tailWord_6336674
  simp only [CollatzResearch.WordTrace]
  refine ⟨57779371961329947651138269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154078325230213193736368717 57779371961329947651138269)
  ·
    refine ⟨21667264485498730369176851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57779371961329947651138269 21667264485498730369176851)
    ·
      refine ⟨32500896728248095553765277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21667264485498730369176851 32500896728248095553765277)
      ·
        refine ⟨12187836273093035832661979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32500896728248095553765277 12187836273093035832661979)
        ·
          refine ⟨18281754409639553748992969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12187836273093035832661979 18281754409639553748992969)
          ·
            refine ⟨13711315807229665311744727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18281754409639553748992969 13711315807229665311744727)
            ·
              refine ⟨20566973710844497967617091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13711315807229665311744727 20566973710844497967617091)
              ·
                refine ⟨30850460566266746951425637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20566973710844497967617091 30850460566266746951425637)
                ·
                  refine ⟨5784461356175015053392307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30850460566266746951425637 5784461356175015053392307)
                  ·
                    refine ⟨8676692034262522580088461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5784461356175015053392307 8676692034262522580088461)
                    ·
                      refine ⟨3253759512848445967533173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8676692034262522580088461 3253759512848445967533173)
                      ·
                        rfl

theorem cell23_6336674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_6336674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336674 prefixEnd_6336674 := by exact prefixLift 6336674
  have htrace : WordTrace (prefixWord ++ tailWord_6336674) baseStart_6336674 baseEnd_6336674 := by
    simpa [prefixWord, tailWord_6336674, baseEnd_6336674] using wordTrace_append hprefix tailTrace_6336674
  have hstable : (prefixWord ++ tailWord_6336674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336674).length < 2 ^ (prefixWord ++ tailWord_6336674).sum := by decide
  have hdescent : baseEnd_6336674 < baseStart_6336674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336730 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3]
def baseStart_6336730 : Nat := 118140960795 + 6336730 * 2 ^ 59
def prefixEnd_6336730 : Nat := 4983230072969 + 3 ^ 40 * 6336730 * 2
def baseEnd_6336730 : Nat := 3253788267765097748432915

theorem tailTrace_6336730 : CollatzResearch.WordTrace tailWord_6336730 prefixEnd_6336730 3253788267765097748432915 := by
  unfold tailWord_6336730
  simp only [CollatzResearch.WordTrace]
  refine ⟨57779882583279228042147911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154079686888744608112394429 57779882583279228042147911)
  ·
    refine ⟨86669823874918842063221867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57779882583279228042147911 86669823874918842063221867)
    ·
      refine ⟨130004735812378263094832801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86669823874918842063221867 130004735812378263094832801)
      ·
        refine ⟨97503551859283697321124601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130004735812378263094832801 97503551859283697321124601)
        ·
          refine ⟨73127663894462772990843451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97503551859283697321124601 73127663894462772990843451)
          ·
            refine ⟨109691495841694159486265177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73127663894462772990843451 109691495841694159486265177)
            ·
              refine ⟨82268621881270619614698883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109691495841694159486265177 82268621881270619614698883)
              ·
                refine ⟨123402932821905929422048325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82268621881270619614698883 123402932821905929422048325)
                ·
                  refine ⟨23138049904107361766634061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123402932821905929422048325 23138049904107361766634061)
                  ·
                    refine ⟨8676768714040260662487773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23138049904107361766634061 8676768714040260662487773)
                    ·
                      refine ⟨3253788267765097748432915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8676768714040260662487773 3253788267765097748432915)
                      ·
                        rfl

theorem cell23_6336730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_6336730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336730 prefixEnd_6336730 := by exact prefixLift 6336730
  have htrace : WordTrace (prefixWord ++ tailWord_6336730) baseStart_6336730 baseEnd_6336730 := by
    simpa [prefixWord, tailWord_6336730, baseEnd_6336730] using wordTrace_append hprefix tailTrace_6336730
  have hstable : (prefixWord ++ tailWord_6336730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336730).length < 2 ^ (prefixWord ++ tailWord_6336730).sum := by decide
  have hdescent : baseEnd_6336730 < baseStart_6336730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336750 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_6336750 : Nat := 118140960795 + 6336750 * 2 ^ 59
def prefixEnd_6336750 : Nat := 4983230072969 + 3 ^ 40 * 6336750 * 2
def baseEnd_6336750 : Nat := 1084599512459395890060941

theorem tailTrace_6336750 : CollatzResearch.WordTrace tailWord_6336750 prefixEnd_6336750 1084599512459395890060941 := by
  unfold tailWord_6336750
  simp only [CollatzResearch.WordTrace]
  refine ⟨28890032474130556948039963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154080173195362970389546469 28890032474130556948039963)
  ·
    refine ⟨43335048711195835422059945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28890032474130556948039963 43335048711195835422059945)
    ·
      refine ⟨32501286533396876566544959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43335048711195835422059945 32501286533396876566544959)
      ·
        refine ⟨48751929800095314849817439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32501286533396876566544959 48751929800095314849817439)
        ·
          refine ⟨73127894700142972274726159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48751929800095314849817439 73127894700142972274726159)
          ·
            refine ⟨109691842050214458412089239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73127894700142972274726159 109691842050214458412089239)
            ·
              refine ⟨164537763075321687618133859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109691842050214458412089239 164537763075321687618133859)
              ·
                refine ⟨246806644612982531427200789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164537763075321687618133859 246806644612982531427200789)
                ·
                  refine ⟨11569061466233556160650037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 246806644612982531427200789 11569061466233556160650037)
                  ·
                    refine ⟨1084599512459395890060941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11569061466233556160650037 1084599512459395890060941)
                    ·
                      rfl

theorem cell23_6336750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_6336750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336750 prefixEnd_6336750 := by exact prefixLift 6336750
  have htrace : WordTrace (prefixWord ++ tailWord_6336750) baseStart_6336750 baseEnd_6336750 := by
    simpa [prefixWord, tailWord_6336750, baseEnd_6336750] using wordTrace_append hprefix tailTrace_6336750
  have hstable : (prefixWord ++ tailWord_6336750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336750).length < 2 ^ (prefixWord ++ tailWord_6336750).sum := by decide
  have hdescent : baseEnd_6336750 < baseStart_6336750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336804 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 2, 4, 2]
def baseStart_6336804 : Nat := 118140960795 + 6336804 * 2 ^ 59
def prefixEnd_6336804 : Nat := 4983230072969 + 3 ^ 40 * 6336804 * 2
def baseEnd_6336804 : Nat := 3253826265333530458907575

theorem tailTrace_6336804 : CollatzResearch.WordTrace tailWord_6336804 prefixEnd_6336804 3253826265333530458907575 := by
  unfold tailWord_6336804
  simp only [CollatzResearch.WordTrace]
  refine ⟨115561114667424411403392733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154081486223232548537856977 115561114667424411403392733)
  ·
    refine ⟨43335418000284154276272275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115561114667424411403392733 43335418000284154276272275)
    ·
      refine ⟨65003127000426231414408413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43335418000284154276272275 65003127000426231414408413)
      ·
        refine ⟨24376172625159836780403155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65003127000426231414408413 24376172625159836780403155)
        ·
          refine ⟨36564258937739755170604733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24376172625159836780403155 36564258937739755170604733)
          ·
            refine ⟨13711597101652408188976775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36564258937739755170604733 13711597101652408188976775)
            ·
              refine ⟨20567395652478612283465163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13711597101652408188976775 20567395652478612283465163)
              ·
                refine ⟨30851093478717918425197745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20567395652478612283465163 30851093478717918425197745)
                ·
                  refine ⟨23138320109038438818898309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30851093478717918425197745 23138320109038438818898309)
                  ·
                    refine ⟨4338435020444707278543433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23138320109038438818898309 4338435020444707278543433)
                    ·
                      refine ⟨3253826265333530458907575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338435020444707278543433 3253826265333530458907575)
                      ·
                        rfl

theorem cell23_6336804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_6336804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336804 prefixEnd_6336804 := by exact prefixLift 6336804
  have htrace : WordTrace (prefixWord ++ tailWord_6336804) baseStart_6336804 baseEnd_6336804 := by
    simpa [prefixWord, tailWord_6336804, baseEnd_6336804] using wordTrace_append hprefix tailTrace_6336804
  have hstable : (prefixWord ++ tailWord_6336804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336804).length < 2 ^ (prefixWord ++ tailWord_6336804).sum := by decide
  have hdescent : baseEnd_6336804 < baseStart_6336804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336874 : List Nat := [3, 1, 3, 3, 1, 1, 1, 4, 1, 5]
def baseStart_6336874 : Nat := 118140960795 + 6336874 * 2 ^ 59
def prefixEnd_6336874 : Nat := 4983230072969 + 3 ^ 40 * 6336874 * 2
def baseEnd_6336874 : Nat := 1084620736326448395010751

theorem tailTrace_6336874 : CollatzResearch.WordTrace tailWord_6336874 prefixEnd_6336874 1084620736326448395010751 := by
  unfold tailWord_6336874
  simp only [CollatzResearch.WordTrace]
  refine ⟨57781195611148806190458419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154083188296396816507889117 57781195611148806190458419)
  ·
    refine ⟨86671793416723209285687629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57781195611148806190458419 86671793416723209285687629)
    ·
      refine ⟨32501922531271203482132861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86671793416723209285687629 32501922531271203482132861)
      ·
        refine ⟨12188220949226701305799823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32501922531271203482132861 12188220949226701305799823)
        ·
          refine ⟨18282331423840051958699735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12188220949226701305799823 18282331423840051958699735)
          ·
            refine ⟨27423497135760077938049603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18282331423840051958699735 27423497135760077938049603)
            ·
              refine ⟨41135245703640116907074405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27423497135760077938049603 41135245703640116907074405)
              ·
                refine ⟨7712858569432521920076451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41135245703640116907074405 7712858569432521920076451)
                ·
                  refine ⟨11569287854148782880114677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7712858569432521920076451 11569287854148782880114677)
                  ·
                    refine ⟨1084620736326448395010751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11569287854148782880114677 1084620736326448395010751)
                    ·
                      rfl

theorem cell23_6336874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_6336874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336874 prefixEnd_6336874 := by exact prefixLift 6336874
  have htrace : WordTrace (prefixWord ++ tailWord_6336874) baseStart_6336874 baseEnd_6336874 := by
    simpa [prefixWord, tailWord_6336874, baseEnd_6336874] using wordTrace_append hprefix tailTrace_6336874
  have hstable : (prefixWord ++ tailWord_6336874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336874).length < 2 ^ (prefixWord ++ tailWord_6336874).sum := by decide
  have hdescent : baseEnd_6336874 < baseStart_6336874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336890 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_6336890 : Nat := 118140960795 + 6336890 * 2 ^ 59
def prefixEnd_6336890 : Nat := 4983230072969 + 3 ^ 40 * 6336890 * 2
def baseEnd_6336890 : Nat := 3253870424669817122432179

theorem tailTrace_6336890 : CollatzResearch.WordTrace tailWord_6336890 prefixEnd_6336890 3253870424669817122432179 := by
  unfold tailWord_6336890
  simp only [CollatzResearch.WordTrace]
  refine ⟨57781341503134314873604031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154083577341691506329610749 57781341503134314873604031)
  ·
    refine ⟨86672012254701472310406047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57781341503134314873604031 86672012254701472310406047)
    ·
      refine ⟨130008018382052208465609071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86672012254701472310406047 130008018382052208465609071)
      ·
        refine ⟨195012027573078312698413607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130008018382052208465609071 195012027573078312698413607)
        ·
          refine ⟨292518041359617469047620411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195012027573078312698413607 292518041359617469047620411)
          ·
            refine ⟨438777062039426203571430617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292518041359617469047620411 438777062039426203571430617)
            ·
              refine ⟨329082796529569652678572963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438777062039426203571430617 329082796529569652678572963)
              ·
                refine ⟨493624194794354479017859445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329082796529569652678572963 493624194794354479017859445)
                ·
                  refine ⟨46277268261970732407924323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 493624194794354479017859445 46277268261970732407924323)
                  ·
                    refine ⟨69415902392956098611886485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46277268261970732407924323 69415902392956098611886485)
                    ·
                      refine ⟨3253870424669817122432179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69415902392956098611886485 3253870424669817122432179)
                      ·
                        rfl

theorem cell23_6336890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_6336890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336890 prefixEnd_6336890 := by exact prefixLift 6336890
  have htrace : WordTrace (prefixWord ++ tailWord_6336890) baseStart_6336890 baseEnd_6336890 := by
    simpa [prefixWord, tailWord_6336890, baseEnd_6336890] using wordTrace_append hprefix tailTrace_6336890
  have hstable : (prefixWord ++ tailWord_6336890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336890).length < 2 ^ (prefixWord ++ tailWord_6336890).sum := by decide
  have hdescent : baseEnd_6336890 < baseStart_6336890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336904 : List Nat := [2, 1, 3, 3, 1, 1, 2, 4, 2, 4]
def baseStart_6336904 : Nat := 118140960795 + 6336904 * 2 ^ 59
def prefixEnd_6336904 : Nat := 4983230072969 + 3 ^ 40 * 6336904 * 2
def baseEnd_6336904 : Nat := 1084625871132993355885705

theorem tailTrace_6336904 : CollatzResearch.WordTrace tailWord_6336904 prefixEnd_6336904 1084625871132993355885705 := by
  unfold tailWord_6336904
  simp only [CollatzResearch.WordTrace]
  refine ⟨115562938317243269942712883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154083917756324359923617177 115562938317243269942712883)
  ·
    refine ⟨173344407475864904914069325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115562938317243269942712883 173344407475864904914069325)
    ·
      refine ⟨65004152803449339342775997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173344407475864904914069325 65004152803449339342775997)
      ·
        refine ⟨24376557301293502253540999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65004152803449339342775997 24376557301293502253540999)
        ·
          refine ⟨36564835951940253380311499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24376557301293502253540999 36564835951940253380311499)
          ·
            refine ⟨54847253927910380070467249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36564835951940253380311499 54847253927910380070467249)
            ·
              refine ⟨41135440445932785052850437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54847253927910380070467249 41135440445932785052850437)
              ·
                refine ⟨7712895083612397197409457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41135440445932785052850437 7712895083612397197409457)
                ·
                  refine ⟨5784671312709297898057093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7712895083612397197409457 5784671312709297898057093)
                  ·
                    refine ⟨1084625871132993355885705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5784671312709297898057093 1084625871132993355885705)
                    ·
                      rfl

theorem cell23_6336904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_6336904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336904 prefixEnd_6336904 := by exact prefixLift 6336904
  have htrace : WordTrace (prefixWord ++ tailWord_6336904) baseStart_6336904 baseEnd_6336904 := by
    simpa [prefixWord, tailWord_6336904, baseEnd_6336904] using wordTrace_append hprefix tailTrace_6336904
  have hstable : (prefixWord ++ tailWord_6336904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336904).length < 2 ^ (prefixWord ++ tailWord_6336904).sum := by decide
  have hdescent : baseEnd_6336904 < baseStart_6336904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336931 : List Nat := [1, 1, 1, 4, 1, 6, 1, 2, 1, 2, 3]
def baseStart_6336931 : Nat := 118140960795 + 6336931 * 2 ^ 59
def prefixEnd_6336931 : Nat := 4983230072969 + 3 ^ 40 * 6336931 * 2
def baseEnd_6336931 : Nat := 3253891477376651462019491

theorem tailTrace_6336931 : CollatzResearch.WordTrace tailWord_6336931 prefixEnd_6336931 3253891477376651462019491 := by
  unfold tailWord_6336931
  simp only [CollatzResearch.WordTrace]
  refine ⟨231126861405388723496658647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154084574270259148997772431 231126861405388723496658647)
  ·
    refine ⟨346690292108083085244987971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231126861405388723496658647 346690292108083085244987971)
    ·
      refine ⟨520035438162124627867481957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346690292108083085244987971 520035438162124627867481957)
      ·
        refine ⟨97506644655398367725152867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 520035438162124627867481957 97506644655398367725152867)
        ·
          refine ⟨146259966983097551587729301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97506644655398367725152867 146259966983097551587729301)
          ·
            refine ⟨6855935952332697730674811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 146259966983097551587729301 6855935952332697730674811)
            ·
              refine ⟨10283903928499046596012217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6855935952332697730674811 10283903928499046596012217)
              ·
                refine ⟨7712927946374284947009163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10283903928499046596012217 7712927946374284947009163)
                ·
                  refine ⟨11569391919561427420513745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7712927946374284947009163 11569391919561427420513745)
                  ·
                    refine ⟨8677043939671070565385309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11569391919561427420513745 8677043939671070565385309)
                    ·
                      refine ⟨3253891477376651462019491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8677043939671070565385309 3253891477376651462019491)
                      ·
                        rfl

theorem cell23_6336931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_6336931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336931 prefixEnd_6336931 := by exact prefixLift 6336931
  have htrace : WordTrace (prefixWord ++ tailWord_6336931) baseStart_6336931 baseEnd_6336931 := by
    simpa [prefixWord, tailWord_6336931, baseEnd_6336931] using wordTrace_append hprefix tailTrace_6336931
  have hstable : (prefixWord ++ tailWord_6336931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336931).length < 2 ^ (prefixWord ++ tailWord_6336931).sum := by decide
  have hdescent : baseEnd_6336931 < baseStart_6336931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336938 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 1, 6]
def baseStart_6336938 : Nat := 118140960795 + 6336938 * 2 ^ 59
def prefixEnd_6336938 : Nat := 4983230072969 + 3 ^ 40 * 6336938 * 2
def baseEnd_6336938 : Nat := 1084631690580410978210653

theorem tailTrace_6336938 : CollatzResearch.WordTrace tailWord_6336938 prefixEnd_6336938 1084631690580410978210653 := by
  unfold tailWord_6336938
  simp only [CollatzResearch.WordTrace]
  refine ⟨57781779179090840923040867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154084744477575575794775645 57781779179090840923040867)
  ·
    refine ⟨86672668768636261384561301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57781779179090840923040867 86672668768636261384561301)
    ·
      refine ⟨4062781348529824752401311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86672668768636261384561301 4062781348529824752401311)
      ·
        refine ⟨6094172022794737128601967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4062781348529824752401311 6094172022794737128601967)
        ·
          refine ⟨9141258034192105692902951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6094172022794737128601967 9141258034192105692902951)
          ·
            refine ⟨13711887051288158539354427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9141258034192105692902951 13711887051288158539354427)
            ·
              refine ⟨20567830576932237809031641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13711887051288158539354427 20567830576932237809031641)
              ·
                refine ⟨15425872932699178356773731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20567830576932237809031641 15425872932699178356773731)
                ·
                  refine ⟨23138809399048767535160597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15425872932699178356773731 23138809399048767535160597)
                  ·
                    refine ⟨1084631690580410978210653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23138809399048767535160597 1084631690580410978210653)
                    ·
                      rfl

theorem cell23_6336938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_6336938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336938 prefixEnd_6336938 := by exact prefixLift 6336938
  have htrace : WordTrace (prefixWord ++ tailWord_6336938) baseStart_6336938 baseEnd_6336938 := by
    simpa [prefixWord, tailWord_6336938, baseEnd_6336938] using wordTrace_append hprefix tailTrace_6336938
  have hstable : (prefixWord ++ tailWord_6336938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336938).length < 2 ^ (prefixWord ++ tailWord_6336938).sum := by decide
  have hdescent : baseEnd_6336938 < baseStart_6336938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336941 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_6336941 : Nat := 118140960795 + 6336941 * 2 ^ 59
def prefixEnd_6336941 : Nat := 4983230072969 + 3 ^ 40 * 6336941 * 2
def baseEnd_6336941 : Nat := 3253896612183196422894445

theorem tailTrace_6336941 : CollatzResearch.WordTrace tailWord_6336941 prefixEnd_6336941 3253896612183196422894445 := by
  unfold tailWord_6336941
  simp only [CollatzResearch.WordTrace]
  refine ⟨231127226135352495204522677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154084817423568330136348451 231127226135352495204522677)
  ·
    refine ⟨21668177450189296425424001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231127226135352495204522677 21668177450189296425424001)
    ·
      refine ⟨16251133087641972319068001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21668177450189296425424001 16251133087641972319068001)
      ·
        refine ⟨12188349815731479239301001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16251133087641972319068001 12188349815731479239301001)
        ·
          refine ⟨9141262361798609429475751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12188349815731479239301001 9141262361798609429475751)
          ·
            refine ⟨13711893542697914144213627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9141262361798609429475751 13711893542697914144213627)
            ·
              refine ⟨20567840314046871216320441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13711893542697914144213627 20567840314046871216320441)
              ·
                refine ⟨15425880235535153412240331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20567840314046871216320441 15425880235535153412240331)
                ·
                  refine ⟨23138820353302730118360497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15425880235535153412240331 23138820353302730118360497)
                  ·
                    refine ⟨17354115264977047588770373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23138820353302730118360497 17354115264977047588770373)
                    ·
                      refine ⟨3253896612183196422894445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17354115264977047588770373 3253896612183196422894445)
                      ·
                        rfl

theorem cell23_6336941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_6336941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336941 prefixEnd_6336941 := by exact prefixLift 6336941
  have htrace : WordTrace (prefixWord ++ tailWord_6336941) baseStart_6336941 baseEnd_6336941 := by
    simpa [prefixWord, tailWord_6336941, baseEnd_6336941] using wordTrace_append hprefix tailTrace_6336941
  have hstable : (prefixWord ++ tailWord_6336941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336941).length < 2 ^ (prefixWord ++ tailWord_6336941).sum := by decide
  have hdescent : baseEnd_6336941 < baseStart_6336941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336967 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_6336967 : Nat := 118140960795 + 6336967 * 2 ^ 59
def prefixEnd_6336967 : Nat := 4983230072969 + 3 ^ 40 * 6336967 * 2
def baseEnd_6336967 : Nat := 3253909962680213321169325

theorem tailTrace_6336967 : CollatzResearch.WordTrace tailWord_6336967 prefixEnd_6336967 3253909962680213321169325 := by
  unfold tailWord_6336967
  simp only [CollatzResearch.WordTrace]
  refine ⟨231128174433258301644969155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154085449622172201096646103 231128174433258301644969155)
  ·
    refine ⟨346692261649887452467453733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231128174433258301644969155 346692261649887452467453733)
    ·
      refine ⟨65004799059353897337647575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346692261649887452467453733 65004799059353897337647575)
      ·
        refine ⟨97507198589030846006471363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65004799059353897337647575 97507198589030846006471363)
        ·
          refine ⟨146260797883546269009707045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97507198589030846006471363 146260797883546269009707045)
          ·
            refine ⟨27423899603164925439320071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146260797883546269009707045 27423899603164925439320071)
            ·
              refine ⟨41135849404747388158980107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27423899603164925439320071 41135849404747388158980107)
              ·
                refine ⟨61703774107121082238470161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41135849404747388158980107 61703774107121082238470161)
                ·
                  refine ⟨46277830580340811678852621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61703774107121082238470161 46277830580340811678852621)
                  ·
                    refine ⟨17354186467627804379569733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46277830580340811678852621 17354186467627804379569733)
                    ·
                      refine ⟨3253909962680213321169325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17354186467627804379569733 3253909962680213321169325)
                      ·
                        rfl

theorem cell23_6336967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_6336967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336967 prefixEnd_6336967 := by exact prefixLift 6336967
  have htrace : WordTrace (prefixWord ++ tailWord_6336967) baseStart_6336967 baseEnd_6336967 := by
    simpa [prefixWord, tailWord_6336967, baseEnd_6336967] using wordTrace_append hprefix tailTrace_6336967
  have hstable : (prefixWord ++ tailWord_6336967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336967).length < 2 ^ (prefixWord ++ tailWord_6336967).sum := by decide
  have hdescent : baseEnd_6336967 < baseStart_6336967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6336978 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_6336978 : Nat := 118140960795 + 6336978 * 2 ^ 59
def prefixEnd_6336978 : Nat := 4983230072969 + 3 ^ 40 * 6336978 * 2
def baseEnd_6336978 : Nat := 3253915610967412778131775

theorem tailTrace_6336978 : CollatzResearch.WordTrace tailWord_6336978 prefixEnd_6336978 3253915610967412778131775 := by
  unfold tailWord_6336978
  simp only [CollatzResearch.WordTrace]
  refine ⟨57782143909054612630904897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154085717090812300349079725 57782143909054612630904897)
  ·
    refine ⟨43336607931790959473178673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57782143909054612630904897 43336607931790959473178673)
    ·
      refine ⟨32502455948843219604884005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43336607931790959473178673 32502455948843219604884005)
      ·
        refine ⟨6094210490408103675915751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32502455948843219604884005 6094210490408103675915751)
        ·
          refine ⟨9141315735612155513873627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6094210490408103675915751 9141315735612155513873627)
          ·
            refine ⟨13711973603418233270810441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9141315735612155513873627 13711973603418233270810441)
            ·
              refine ⟨10283980202563674953107831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13711973603418233270810441 10283980202563674953107831)
              ·
                refine ⟨15425970303845512429661747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10283980202563674953107831 15425970303845512429661747)
                ·
                  refine ⟨23138955455768268644492621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15425970303845512429661747 23138955455768268644492621)
                  ·
                    refine ⟨8677108295913100741684733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23138955455768268644492621 8677108295913100741684733)
                    ·
                      refine ⟨3253915610967412778131775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8677108295913100741684733 3253915610967412778131775)
                      ·
                        rfl

theorem cell23_6336978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_6336978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6336978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6336978 prefixEnd_6336978 := by exact prefixLift 6336978
  have htrace : WordTrace (prefixWord ++ tailWord_6336978) baseStart_6336978 baseEnd_6336978 := by
    simpa [prefixWord, tailWord_6336978, baseEnd_6336978] using wordTrace_append hprefix tailTrace_6336978
  have hstable : (prefixWord ++ tailWord_6336978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6336978).length < 2 ^ (prefixWord ++ tailWord_6336978).sum := by decide
  have hdescent : baseEnd_6336978 < baseStart_6336978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6336978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337005 : List Nat := [1, 5, 1, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_6337005 : Nat := 118140960795 + 6337005 * 2 ^ 59
def prefixEnd_6337005 : Nat := 4983230072969 + 3 ^ 40 * 6337005 * 2
def baseEnd_6337005 : Nat := 3253929474945084172494151

theorem tailTrace_6337005 : CollatzResearch.WordTrace tailWord_6337005 prefixEnd_6337005 3253929474945084172494151 := by
  unfold tailWord_6337005
  simp only [CollatzResearch.WordTrace]
  refine ⟨231129560407120634134852469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154086373604747089423234979 231129560407120634134852469)
  ·
    refine ⟨21668396288167559450142419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231129560407120634134852469 21668396288167559450142419)
    ·
      refine ⟨32502594432251339175213629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21668396288167559450142419 32502594432251339175213629)
      ·
        refine ⟨12188472912094252190705111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32502594432251339175213629 12188472912094252190705111)
        ·
          refine ⟨18282709368141378286057667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12188472912094252190705111 18282709368141378286057667)
          ·
            refine ⟨27424064052212067429086501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18282709368141378286057667 27424064052212067429086501)
            ·
              refine ⟨5142012009789762642953719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27424064052212067429086501 5142012009789762642953719)
              ·
                refine ⟨7713018014684643964430579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142012009789762642953719 7713018014684643964430579)
                ·
                  refine ⟨11569527022026965946645869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7713018014684643964430579 11569527022026965946645869)
                  ·
                    refine ⟨4338572633260112229992201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11569527022026965946645869 4338572633260112229992201)
                    ·
                      refine ⟨3253929474945084172494151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338572633260112229992201 3253929474945084172494151)
                      ·
                        rfl

theorem cell23_6337005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_6337005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337005 prefixEnd_6337005 := by exact prefixLift 6337005
  have htrace : WordTrace (prefixWord ++ tailWord_6337005) baseStart_6337005 baseEnd_6337005 := by
    simpa [prefixWord, tailWord_6337005, baseEnd_6337005] using wordTrace_append hprefix tailTrace_6337005
  have hstable : (prefixWord ++ tailWord_6337005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337005).length < 2 ^ (prefixWord ++ tailWord_6337005).sum := by decide
  have hdescent : baseEnd_6337005 < baseStart_6337005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337014 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_6337014 : Nat := 118140960795 + 6337014 * 2 ^ 59
def prefixEnd_6337014 : Nat := 4983230072969 + 3 ^ 40 * 6337014 * 2
def baseEnd_6337014 : Nat := 3253934096270974637281609

theorem tailTrace_6337014 : CollatzResearch.WordTrace tailWord_6337014 prefixEnd_6337014 3253934096270974637281609 := by
  unfold tailWord_6337014
  simp only [CollatzResearch.WordTrace]
  refine ⟨14445618041505501791995631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154086592442725352447953397 14445618041505501791995631)
  ·
    refine ⟨21668427062258252687993447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14445618041505501791995631 21668427062258252687993447)
    ·
      refine ⟨32502640593387379031990171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21668427062258252687993447 32502640593387379031990171)
      ·
        refine ⟨48753960890081068547985257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32502640593387379031990171 48753960890081068547985257)
        ·
          refine ⟨36565470667560801410988943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48753960890081068547985257 36565470667560801410988943)
          ·
            refine ⟨54848206001341202116483415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36565470667560801410988943 54848206001341202116483415)
            ·
              refine ⟨82272309002011803174725123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54848206001341202116483415 82272309002011803174725123)
              ·
                refine ⟨123408463503017704762087685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82272309002011803174725123 123408463503017704762087685)
                ·
                  refine ⟨23139086906815819642891441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123408463503017704762087685 23139086906815819642891441)
                  ·
                    refine ⟨17354315180111864732168581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23139086906815819642891441 17354315180111864732168581)
                    ·
                      refine ⟨3253934096270974637281609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17354315180111864732168581 3253934096270974637281609)
                      ·
                        rfl

theorem cell23_6337014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_6337014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337014 prefixEnd_6337014 := by exact prefixLift 6337014
  have htrace : WordTrace (prefixWord ++ tailWord_6337014) baseStart_6337014 baseEnd_6337014 := by
    simpa [prefixWord, tailWord_6337014, baseEnd_6337014] using wordTrace_append hprefix tailTrace_6337014
  have hstable : (prefixWord ++ tailWord_6337014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337014).length < 2 ^ (prefixWord ++ tailWord_6337014).sum := by decide
  have hdescent : baseEnd_6337014 < baseStart_6337014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337034 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_6337034 : Nat := 118140960795 + 6337034 * 2 ^ 59
def prefixEnd_6337034 : Nat := 4983230072969 + 3 ^ 40 * 6337034 * 2
def baseEnd_6337034 : Nat := 3253944365884064559031517

theorem tailTrace_6337034 : CollatzResearch.WordTrace tailWord_6337034 prefixEnd_6337034 3253944365884064559031517 := by
  unfold tailWord_6337034
  simp only [CollatzResearch.WordTrace]
  refine ⟨57782654531003893021914539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154087078749343714725105437 57782654531003893021914539)
  ·
    refine ⟨86673981796505839532871809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57782654531003893021914539 86673981796505839532871809)
    ·
      refine ⟨65005486347379379649653857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86673981796505839532871809 65005486347379379649653857)
      ·
        refine ⟨48754114760534534737240393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65005486347379379649653857 48754114760534534737240393)
        ·
          refine ⟨36565586070400901052930295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48754114760534534737240393 36565586070400901052930295)
          ·
            refine ⟨54848379105601351579395443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36565586070400901052930295 54848379105601351579395443)
            ·
              refine ⟨82272568658402027369093165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54848379105601351579395443 82272568658402027369093165)
              ·
                refine ⟨30852213246900760263409937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82272568658402027369093165 30852213246900760263409937)
                ·
                  refine ⟨23139159935175570197557453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30852213246900760263409937 23139159935175570197557453)
                  ·
                    refine ⟨8677184975690838824084045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23139159935175570197557453 8677184975690838824084045)
                    ·
                      refine ⟨3253944365884064559031517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8677184975690838824084045 3253944365884064559031517)
                      ·
                        rfl

theorem cell23_6337034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_6337034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337034 prefixEnd_6337034 := by exact prefixLift 6337034
  have htrace : WordTrace (prefixWord ++ tailWord_6337034) baseStart_6337034 baseEnd_6337034 := by
    simpa [prefixWord, tailWord_6337034, baseEnd_6337034] using wordTrace_append hprefix tailTrace_6337034
  have hstable : (prefixWord ++ tailWord_6337034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337034).length < 2 ^ (prefixWord ++ tailWord_6337034).sum := by decide
  have hdescent : baseEnd_6337034 < baseStart_6337034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337035 : List Nat := [1, 1, 1, 1, 7, 2, 3, 1, 2, 2, 2]
def baseStart_6337035 : Nat := 118140960795 + 6337035 * 2 ^ 59
def prefixEnd_6337035 : Nat := 4983230072969 + 3 ^ 40 * 6337035 * 2
def baseEnd_6337035 : Nat := 3253944879364719055119013

theorem tailTrace_6337035 : CollatzResearch.WordTrace tailWord_6337035 prefixEnd_6337035 3253944879364719055119013 := by
  unfold tailWord_6337035
  simp only [CollatzResearch.WordTrace]
  refine ⟨231130654597011949258444559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154087103064674632838963039 231130654597011949258444559)
  ·
    refine ⟨346695981895517923887666839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231130654597011949258444559 346695981895517923887666839)
    ·
      refine ⟨520043972843276885831500259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346695981895517923887666839 520043972843276885831500259)
      ·
        refine ⟨780065959264915328747250389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520043972843276885831500259 780065959264915328747250389)
        ·
          refine ⟨18282795920271453017513681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 780065959264915328747250389 18282795920271453017513681)
          ·
            refine ⟨13712096940203589763135261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18282795920271453017513681 13712096940203589763135261)
            ·
              refine ⟨5142036352576346161175723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13712096940203589763135261 5142036352576346161175723)
              ·
                refine ⟨7713054528864519241763585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142036352576346161175723 7713054528864519241763585)
                ·
                  refine ⟨5784790896648389431322689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7713054528864519241763585 5784790896648389431322689)
                  ·
                    refine ⟨4338593172486292073492017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5784790896648389431322689 4338593172486292073492017)
                    ·
                      refine ⟨3253944879364719055119013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338593172486292073492017 3253944879364719055119013)
                      ·
                        rfl

theorem cell23_6337035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 2, 2, 2].length) (baseStart_6337035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337035 prefixEnd_6337035 := by exact prefixLift 6337035
  have htrace : WordTrace (prefixWord ++ tailWord_6337035) baseStart_6337035 baseEnd_6337035 := by
    simpa [prefixWord, tailWord_6337035, baseEnd_6337035] using wordTrace_append hprefix tailTrace_6337035
  have hstable : (prefixWord ++ tailWord_6337035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337035).length < 2 ^ (prefixWord ++ tailWord_6337035).sum := by decide
  have hdescent : baseEnd_6337035 < baseStart_6337035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337074 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_6337074 : Nat := 118140960795 + 6337074 * 2 ^ 59
def prefixEnd_6337074 : Nat := 4983230072969 + 3 ^ 40 * 6337074 * 2
def baseEnd_6337074 : Nat := 3253964905110244402531333

theorem tailTrace_6337074 : CollatzResearch.WordTrace tailWord_6337074 prefixEnd_6337074 3253964905110244402531333 := by
  unfold tailWord_6337074
  simp only [CollatzResearch.WordTrace]
  refine ⟨57783019260967664729778569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154088051362580439279409517 57783019260967664729778569)
  ·
    refine ⟨43337264445725748547333927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57783019260967664729778569 43337264445725748547333927)
    ·
      refine ⟨65005896668588622821000891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43337264445725748547333927 65005896668588622821000891)
      ·
        refine ⟨97508845002882934231501337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65005896668588622821000891 97508845002882934231501337)
        ·
          refine ⟨73131633752162200673626003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97508845002882934231501337 73131633752162200673626003)
          ·
            refine ⟨109697450628243301010439005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73131633752162200673626003 109697450628243301010439005)
            ·
              refine ⟨41136543985591237878914627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109697450628243301010439005 41136543985591237878914627)
              ·
                refine ⟨61704815978386856818371941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41136543985591237878914627 61704815978386856818371941)
                ·
                  refine ⟨11569652995947535653444739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61704815978386856818371941 11569652995947535653444739)
                  ·
                    refine ⟨17354479493921303480167109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11569652995947535653444739 17354479493921303480167109)
                    ·
                      refine ⟨3253964905110244402531333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17354479493921303480167109 3253964905110244402531333)
                      ·
                        rfl

theorem cell23_6337074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_6337074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337074 prefixEnd_6337074 := by exact prefixLift 6337074
  have htrace : WordTrace (prefixWord ++ tailWord_6337074) baseStart_6337074 baseEnd_6337074 := by
    simpa [prefixWord, tailWord_6337074, baseEnd_6337074] using wordTrace_append hprefix tailTrace_6337074
  have hstable : (prefixWord ++ tailWord_6337074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337074).length < 2 ^ (prefixWord ++ tailWord_6337074).sum := by decide
  have hdescent : baseEnd_6337074 < baseStart_6337074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337086 : List Nat := [4, 2, 1, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_6337086 : Nat := 118140960795 + 6337086 * 2 ^ 59
def prefixEnd_6337086 : Nat := 4983230072969 + 3 ^ 40 * 6337086 * 2
def baseEnd_6337086 : Nat := 3253971066878098355581279

theorem tailTrace_6337086 : CollatzResearch.WordTrace tailWord_6337086 prefixEnd_6337086 3253971066878098355581279 := by
  unfold tailWord_6337086
  simp only [CollatzResearch.WordTrace]
  refine ⟨28891564339978398121068889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154088343146551456645700741 28891564339978398121068889)
  ·
    refine ⟨21668673254983798590801667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28891564339978398121068889 21668673254983798590801667)
    ·
      refine ⟨32503009882475697886202501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21668673254983798590801667 32503009882475697886202501)
      ·
        refine ⟨6094314352964193353662969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32503009882475697886202501 6094314352964193353662969)
        ·
          refine ⟨4570735764723145015247227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6094314352964193353662969 4570735764723145015247227)
          ·
            refine ⟨6856103647084717522870841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4570735764723145015247227 6856103647084717522870841)
            ·
              refine ⟨5142077735313538142153131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6856103647084717522870841 5142077735313538142153131)
              ·
                refine ⟨7713116602970307213229697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142077735313538142153131 7713116602970307213229697)
                ·
                  refine ⟨5784837452227730409922273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7713116602970307213229697 5784837452227730409922273)
                  ·
                    refine ⟨4338628089170797807441705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5784837452227730409922273 4338628089170797807441705)
                    ·
                      refine ⟨3253971066878098355581279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338628089170797807441705 3253971066878098355581279)
                      ·
                        rfl

theorem cell23_6337086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_6337086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337086 prefixEnd_6337086 := by exact prefixLift 6337086
  have htrace : WordTrace (prefixWord ++ tailWord_6337086) baseStart_6337086 baseEnd_6337086 := by
    simpa [prefixWord, tailWord_6337086, baseEnd_6337086] using wordTrace_append hprefix tailTrace_6337086
  have hstable : (prefixWord ++ tailWord_6337086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337086).length < 2 ^ (prefixWord ++ tailWord_6337086).sum := by decide
  have hdescent : baseEnd_6337086 < baseStart_6337086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337111 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 3]
def baseStart_6337111 : Nat := 118140960795 + 6337111 * 2 ^ 59
def prefixEnd_6337111 : Nat := 4983230072969 + 3 ^ 40 * 6337111 * 2
def baseEnd_6337111 : Nat := 3253983903894460757768663

theorem tailTrace_6337111 : CollatzResearch.WordTrace tailWord_6337111 prefixEnd_6337111 3253983903894460757768663 := by
  unfold tailWord_6337111
  simp only [CollatzResearch.WordTrace]
  refine ⟨231133426544736614238211187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154088951029824409492140791 231133426544736614238211187)
  ·
    refine ⟨346700139817104921357316781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231133426544736614238211187 346700139817104921357316781)
    ·
      refine ⟨130012552431414345508993793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346700139817104921357316781 130012552431414345508993793)
      ·
        refine ⟨97509414323560759131745345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130012552431414345508993793 97509414323560759131745345)
        ·
          refine ⟨73132060742670569348809009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97509414323560759131745345 73132060742670569348809009)
          ·
            refine ⟨54849045557002927011606757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73132060742670569348809009 54849045557002927011606757)
            ·
              refine ⟨10284196041938048814676267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54849045557002927011606757 10284196041938048814676267)
              ·
                refine ⟨15426294062907073222014401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10284196041938048814676267 15426294062907073222014401)
                ·
                  refine ⟨11569720547180304916510801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15426294062907073222014401 11569720547180304916510801)
                  ·
                    refine ⟨8677290410385228687383101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11569720547180304916510801 8677290410385228687383101)
                    ·
                      refine ⟨3253983903894460757768663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8677290410385228687383101 3253983903894460757768663)
                      ·
                        rfl

theorem cell23_6337111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_6337111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337111 prefixEnd_6337111 := by exact prefixLift 6337111
  have htrace : WordTrace (prefixWord ++ tailWord_6337111) baseStart_6337111 baseEnd_6337111 := by
    simpa [prefixWord, tailWord_6337111, baseEnd_6337111] using wordTrace_append hprefix tailTrace_6337111
  have hstable : (prefixWord ++ tailWord_6337111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337111).length < 2 ^ (prefixWord ++ tailWord_6337111).sum := by decide
  have hdescent : baseEnd_6337111 < baseStart_6337111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337175 : List Nat := [1, 1, 3, 3, 2, 1, 4, 3, 1, 1, 3]
def baseStart_6337175 : Nat := 118140960795 + 6337175 * 2 ^ 59
def prefixEnd_6337175 : Nat := 4983230072969 + 3 ^ 40 * 6337175 * 2
def baseEnd_6337175 : Nat := 3254016766656348507368369

theorem tailTrace_6337175 : CollatzResearch.WordTrace tailWord_6337175 prefixEnd_6337175 3254016766656348507368369 := by
  unfold tailWord_6337175
  simp only [CollatzResearch.WordTrace]
  refine ⟨231135760816504753168540979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154090507211003168779027319 231135760816504753168540979)
  ·
    refine ⟨346703641224757129752811469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231135760816504753168540979 346703641224757129752811469)
    ·
      refine ⟨130013865459283923657304301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346703641224757129752811469 130013865459283923657304301)
      ·
        refine ⟨48755199547231471371489113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130013865459283923657304301 48755199547231471371489113)
        ·
          refine ⟨36566399660423603528616835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48755199547231471371489113 36566399660423603528616835)
          ·
            refine ⟨54849599490635405292925253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36566399660423603528616835 54849599490635405292925253)
            ·
              refine ⟨10284299904494138492423485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54849599490635405292925253 10284299904494138492423485)
              ·
                refine ⟨3856612464185301934658807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10284299904494138492423485 3856612464185301934658807)
                ·
                  refine ⟨5784918696277952901988211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856612464185301934658807 5784918696277952901988211)
                  ·
                    refine ⟨8677378044416929352982317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5784918696277952901988211 8677378044416929352982317)
                    ·
                      refine ⟨3254016766656348507368369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8677378044416929352982317 3254016766656348507368369)
                      ·
                        rfl

theorem cell23_6337175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_6337175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337175 prefixEnd_6337175 := by exact prefixLift 6337175
  have htrace : WordTrace (prefixWord ++ tailWord_6337175) baseStart_6337175 baseEnd_6337175 := by
    simpa [prefixWord, tailWord_6337175, baseEnd_6337175] using wordTrace_append hprefix tailTrace_6337175
  have hstable : (prefixWord ++ tailWord_6337175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337175).length < 2 ^ (prefixWord ++ tailWord_6337175).sum := by decide
  have hdescent : baseEnd_6337175 < baseStart_6337175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337248 : List Nat := [2, 1, 1, 3, 1, 2, 1, 6, 2, 1, 3]
def baseStart_6337248 : Nat := 118140960795 + 6337248 * 2 ^ 59
def prefixEnd_6337248 : Nat := 4983230072969 + 3 ^ 40 * 6337248 * 2
def baseEnd_6337248 : Nat := 3254054250744126721755533

theorem tailTrace_6337248 : CollatzResearch.WordTrace tailWord_6337248 prefixEnd_6337248 3254054250744126721755533 := by
  unfold tailWord_6337248
  simp only [CollatzResearch.WordTrace]
  refine ⟨115569211672620143317974199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154092282230160191090632265 115569211672620143317974199)
  ·
    refine ⟨173353817508930214976961299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115569211672620143317974199 173353817508930214976961299)
    ·
      refine ⟨260030726263395322465441949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173353817508930214976961299 260030726263395322465441949)
      ·
        refine ⟨97511522348773245924540731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260030726263395322465441949 97511522348773245924540731)
        ·
          refine ⟨146267283523159868886811097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97511522348773245924540731 146267283523159868886811097)
          ·
            refine ⟨109700462642369901665108323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146267283523159868886811097 109700462642369901665108323)
            ·
              refine ⟨164550693963554852497662485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109700462642369901665108323 164550693963554852497662485)
              ·
                refine ⟨7713313779541633710827929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164550693963554852497662485 7713313779541633710827929)
                ·
                  refine ⟨5784985334656225283120947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7713313779541633710827929 5784985334656225283120947)
                  ·
                    refine ⟨8677478001984337924681421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5784985334656225283120947 8677478001984337924681421)
                    ·
                      refine ⟨3254054250744126721755533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8677478001984337924681421 3254054250744126721755533)
                      ·
                        rfl

theorem cell23_6337248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_6337248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337248 prefixEnd_6337248 := by exact prefixLift 6337248
  have htrace : WordTrace (prefixWord ++ tailWord_6337248) baseStart_6337248 baseEnd_6337248 := by
    simpa [prefixWord, tailWord_6337248, baseEnd_6337248] using wordTrace_append hprefix tailTrace_6337248
  have hstable : (prefixWord ++ tailWord_6337248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337248).length < 2 ^ (prefixWord ++ tailWord_6337248).sum := by decide
  have hdescent : baseEnd_6337248 < baseStart_6337248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337249 : List Nat := [1, 2, 3, 1, 4, 2, 3, 2, 1, 2, 2]
def baseStart_6337249 : Nat := 118140960795 + 6337249 * 2 ^ 59
def prefixEnd_6337249 : Nat := 4983230072969 + 3 ^ 40 * 6337249 * 2
def baseEnd_6337249 : Nat := 3254054764224781217843029

theorem tailTrace_6337249 : CollatzResearch.WordTrace tailWord_6337249 prefixEnd_6337249 3254054764224781217843029 := by
  unfold tailWord_6337249
  simp only [CollatzResearch.WordTrace]
  refine ⟨231138459818236663806734801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154092306545491109204489867 231138459818236663806734801)
  ·
    refine ⟨173353844863677497855051101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231138459818236663806734801 173353844863677497855051101)
    ·
      refine ⟨65007691823879061695644163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173353844863677497855051101 65007691823879061695644163)
      ·
        refine ⟨97511537735818592543466245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65007691823879061695644163 97511537735818592543466245)
        ·
          refine ⟨18283413325465986101899921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97511537735818592543466245 18283413325465986101899921)
          ·
            refine ⟨13712559994099489576424941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18283413325465986101899921 13712559994099489576424941)
            ·
              refine ⟨5142209997787308591159353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13712559994099489576424941 5142209997787308591159353)
              ·
                refine ⟨3856657498340481443369515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5142209997787308591159353 3856657498340481443369515)
                ·
                  refine ⟨5784986247510722165054273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856657498340481443369515 5784986247510722165054273)
                  ·
                    refine ⟨4338739685633041623790705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5784986247510722165054273 4338739685633041623790705)
                    ·
                      refine ⟨3254054764224781217843029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338739685633041623790705 3254054764224781217843029)
                      ·
                        rfl

theorem cell23_6337249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_6337249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337249 prefixEnd_6337249 := by exact prefixLift 6337249
  have htrace : WordTrace (prefixWord ++ tailWord_6337249) baseStart_6337249 baseEnd_6337249 := by
    simpa [prefixWord, tailWord_6337249, baseEnd_6337249] using wordTrace_append hprefix tailTrace_6337249
  have hstable : (prefixWord ++ tailWord_6337249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337249).length < 2 ^ (prefixWord ++ tailWord_6337249).sum := by decide
  have hdescent : baseEnd_6337249 < baseStart_6337249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337258 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_6337258 : Nat := 118140960795 + 6337258 * 2 ^ 59
def prefixEnd_6337258 : Nat := 4983230072969 + 3 ^ 40 * 6337258 * 2
def baseEnd_6337258 : Nat := 3254059385550671682630487

theorem tailTrace_6337258 : CollatzResearch.WordTrace tailWord_6337258 prefixEnd_6337258 3254059385550671682630487 := by
  unfold tailWord_6337258
  simp only [CollatzResearch.WordTrace]
  refine ⟨57784697018801014585953107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154092525383469372229208285 57784697018801014585953107)
  ·
    refine ⟨86677045528201521878929661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57784697018801014585953107 86677045528201521878929661)
    ·
      refine ⟨32503892073075570704598623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86677045528201521878929661 32503892073075570704598623)
      ·
        refine ⟨48755838109613356056897935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32503892073075570704598623 48755838109613356056897935)
        ·
          refine ⟨73133757164420034085346903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48755838109613356056897935 73133757164420034085346903)
          ·
            refine ⟨109700635746630051128020355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73133757164420034085346903 109700635746630051128020355)
            ·
              refine ⟨164550953619945076692030533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109700635746630051128020355 164550953619945076692030533)
              ·
                refine ⟨30853303803739701879755725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164550953619945076692030533 30853303803739701879755725)
                ·
                  refine ⟨11569988926402388204908397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30853303803739701879755725 11569988926402388204908397)
                  ·
                    refine ⟨4338745847400895576840649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11569988926402388204908397 4338745847400895576840649)
                    ·
                      refine ⟨3254059385550671682630487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338745847400895576840649 3254059385550671682630487)
                      ·
                        rfl

theorem cell23_6337258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_6337258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337258 prefixEnd_6337258 := by exact prefixLift 6337258
  have htrace : WordTrace (prefixWord ++ tailWord_6337258) baseStart_6337258 baseEnd_6337258 := by
    simpa [prefixWord, tailWord_6337258, baseEnd_6337258] using wordTrace_append hprefix tailTrace_6337258
  have hstable : (prefixWord ++ tailWord_6337258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337258).length < 2 ^ (prefixWord ++ tailWord_6337258).sum := by decide
  have hdescent : baseEnd_6337258 < baseStart_6337258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337264 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 1, 8]
def baseStart_6337264 : Nat := 118140960795 + 6337264 * 2 ^ 59
def prefixEnd_6337264 : Nat := 4983230072969 + 3 ^ 40 * 6337264 * 2
def baseEnd_6337264 : Nat := 1084687488811532886385153

theorem tailTrace_6337264 : CollatzResearch.WordTrace tailWord_6337264 prefixEnd_6337264 1084687488811532886385153 := by
  unfold tailWord_6337264
  simp only [CollatzResearch.WordTrace]
  refine ⟨115569503456591160684265423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154092671275454880912353897 115569503456591160684265423)
  ·
    refine ⟨173354255184886741026398135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115569503456591160684265423 173354255184886741026398135)
    ·
      refine ⟨260031382777330111539597203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173354255184886741026398135 260031382777330111539597203)
      ·
        refine ⟨390047074165995167309395805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260031382777330111539597203 390047074165995167309395805)
        ·
          refine ⟨146267652812248187741023427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390047074165995167309395805 146267652812248187741023427)
          ·
            refine ⟨219401479218372281611535141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146267652812248187741023427 219401479218372281611535141)
            ·
              refine ⟨41137777353444802802162839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 219401479218372281611535141 41137777353444802802162839)
              ·
                refine ⟨61706666030167204203244259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41137777353444802802162839 61706666030167204203244259)
                ·
                  refine ⟨92559999045250806304866389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61706666030167204203244259 92559999045250806304866389)
                  ·
                    refine ⟨1084687488811532886385153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92559999045250806304866389 1084687488811532886385153)
                    ·
                      rfl

theorem cell23_6337264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_6337264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337264 prefixEnd_6337264 := by exact prefixLift 6337264
  have htrace : WordTrace (prefixWord ++ tailWord_6337264) baseStart_6337264 baseEnd_6337264 := by
    simpa [prefixWord, tailWord_6337264, baseEnd_6337264] using wordTrace_append hprefix tailTrace_6337264
  have hstable : (prefixWord ++ tailWord_6337264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337264).length < 2 ^ (prefixWord ++ tailWord_6337264).sum := by decide
  have hdescent : baseEnd_6337264 < baseStart_6337264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337288 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 3, 4, 2]
def baseStart_6337288 : Nat := 118140960795 + 6337288 * 2 ^ 59
def prefixEnd_6337288 : Nat := 4983230072969 + 3 ^ 40 * 6337288 * 2
def baseEnd_6337288 : Nat := 3254074789970306565255349

theorem tailTrace_6337288 : CollatzResearch.WordTrace tailWord_6337288 prefixEnd_6337288 3254074789970306565255349 := by
  unfold tailWord_6337288
  simp only [CollatzResearch.WordTrace]
  refine ⟨115569941132547686733702259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154093254843396915644936345 115569941132547686733702259)
  ·
    refine ⟨173354911698821530100553389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115569941132547686733702259 173354911698821530100553389)
    ·
      refine ⟨65008091887058073787707521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173354911698821530100553389 65008091887058073787707521)
      ·
        refine ⟨48756068915293555340780641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65008091887058073787707521 48756068915293555340780641)
        ·
          refine ⟨36567051686470166505585481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48756068915293555340780641 36567051686470166505585481)
          ·
            refine ⟨27425288764852624879189111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36567051686470166505585481 27425288764852624879189111)
            ·
              refine ⟨41137933147278937318783667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27425288764852624879189111 41137933147278937318783667)
              ·
                refine ⟨61706899720918405978175501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41137933147278937318783667 61706899720918405978175501)
                ·
                  refine ⟨23140087395344402241815813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61706899720918405978175501 23140087395344402241815813)
                  ·
                    refine ⟨4338766386627075420340465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23140087395344402241815813 4338766386627075420340465)
                    ·
                      refine ⟨3254074789970306565255349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338766386627075420340465 3254074789970306565255349)
                      ·
                        rfl

theorem cell23_6337288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_6337288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337288 prefixEnd_6337288 := by exact prefixLift 6337288
  have htrace : WordTrace (prefixWord ++ tailWord_6337288) baseStart_6337288 baseEnd_6337288 := by
    simpa [prefixWord, tailWord_6337288, baseEnd_6337288] using wordTrace_append hprefix tailTrace_6337288
  have hstable : (prefixWord ++ tailWord_6337288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337288).length < 2 ^ (prefixWord ++ tailWord_6337288).sum := by decide
  have hdescent : baseEnd_6337288 < baseStart_6337288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337301 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_6337301 : Nat := 118140960795 + 6337301 * 2 ^ 59
def prefixEnd_6337301 : Nat := 4983230072969 + 3 ^ 40 * 6337301 * 2
def baseEnd_6337301 : Nat := 3254081465218815014392789

theorem tailTrace_6337301 : CollatzResearch.WordTrace tailWord_6337301 prefixEnd_6337301 3254081465218815014392789 := by
  unfold tailWord_6337301
  simp only [CollatzResearch.WordTrace]
  refine ⟨231140356414048276687627757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154093570942698851125085171 231140356414048276687627757)
  ·
    refine ⟨86677633655268103757860409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231140356414048276687627757 86677633655268103757860409)
    ·
      refine ⟨65008225241451077818395307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86677633655268103757860409 65008225241451077818395307)
      ·
        refine ⟨97512337862176616727592961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65008225241451077818395307 97512337862176616727592961)
        ·
          refine ⟨73134253396632462545694721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97512337862176616727592961 73134253396632462545694721)
          ·
            refine ⟨54850690047474346909271041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73134253396632462545694721 54850690047474346909271041)
            ·
              refine ⟨41138017535605760181953281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54850690047474346909271041 41138017535605760181953281)
              ·
                refine ⟨30853513151704320136464961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41138017535605760181953281 30853513151704320136464961)
                ·
                  refine ⟨23140134863778240102348721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30853513151704320136464961 23140134863778240102348721)
                  ·
                    refine ⟨17355101147833680076761541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23140134863778240102348721 17355101147833680076761541)
                    ·
                      refine ⟨3254081465218815014392789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17355101147833680076761541 3254081465218815014392789)
                      ·
                        rfl

theorem cell23_6337301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_6337301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337301 prefixEnd_6337301 := by exact prefixLift 6337301
  have htrace : WordTrace (prefixWord ++ tailWord_6337301) baseStart_6337301 baseEnd_6337301 := by
    simpa [prefixWord, tailWord_6337301, baseEnd_6337301] using wordTrace_append hprefix tailTrace_6337301
  have hstable : (prefixWord ++ tailWord_6337301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337301).length < 2 ^ (prefixWord ++ tailWord_6337301).sum := by decide
  have hdescent : baseEnd_6337301 < baseStart_6337301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337321 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 2, 3, 3]
def baseStart_6337321 : Nat := 118140960795 + 6337321 * 2 ^ 59
def prefixEnd_6337321 : Nat := 4983230072969 + 3 ^ 40 * 6337321 * 2
def baseEnd_6337321 : Nat := 3254091734831904936142697

theorem tailTrace_6337321 : CollatzResearch.WordTrace tailWord_6337321 prefixEnd_6337321 3254091734831904936142697 := by
  unfold tailWord_6337321
  simp only [CollatzResearch.WordTrace]
  refine ⟨231141085873975820103355817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154094057249317213402237211 231141085873975820103355817)
  ·
    refine ⟨173355814405481865077516863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231141085873975820103355817 173355814405481865077516863)
    ·
      refine ⟨260033721608222797616275295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173355814405481865077516863 260033721608222797616275295)
      ·
        refine ⟨390050582412334196424412943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260033721608222797616275295 390050582412334196424412943)
        ·
          refine ⟨585075873618501294636619415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390050582412334196424412943 585075873618501294636619415)
          ·
            refine ⟨877613810427751941954929123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585075873618501294636619415 877613810427751941954929123)
            ·
              refine ⟨1316420715641627912932393685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877613810427751941954929123 1316420715641627912932393685)
              ·
                refine ⟨30853610522850654209352977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1316420715641627912932393685 30853610522850654209352977)
                ·
                  refine ⟨23140207892137990657014733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30853610522850654209352977 23140207892137990657014733)
                  ·
                    refine ⟨8677577959551746496380525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23140207892137990657014733 8677577959551746496380525)
                    ·
                      refine ⟨3254091734831904936142697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8677577959551746496380525 3254091734831904936142697)
                      ·
                        rfl

theorem cell23_6337321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 3, 3].length) (baseStart_6337321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337321 prefixEnd_6337321 := by exact prefixLift 6337321
  have htrace : WordTrace (prefixWord ++ tailWord_6337321) baseStart_6337321 baseEnd_6337321 := by
    simpa [prefixWord, tailWord_6337321, baseEnd_6337321] using wordTrace_append hprefix tailTrace_6337321
  have hstable : (prefixWord ++ tailWord_6337321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337321).length < 2 ^ (prefixWord ++ tailWord_6337321).sum := by decide
  have hdescent : baseEnd_6337321 < baseStart_6337321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337388 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 3, 4]
def baseStart_6337388 : Nat := 118140960795 + 6337388 * 2 ^ 59
def prefixEnd_6337388 : Nat := 4983230072969 + 3 ^ 40 * 6337388 * 2
def baseEnd_6337388 : Nat := 1084708712678585391334963

theorem tailTrace_6337388 : CollatzResearch.WordTrace tailWord_6337388 prefixEnd_6337388 1084708712678585391334963 := by
  unfold tailWord_6337388
  simp only [CollatzResearch.WordTrace]
  refine ⟨115571764782366545273022409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154095686376488727030696545 115571764782366545273022409)
  ·
    refine ⟨86678823586774908954766807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115571764782366545273022409 86678823586774908954766807)
    ·
      refine ⟨130018235380162363432150211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86678823586774908954766807 130018235380162363432150211)
      ·
        refine ⟨195027353070243545148225317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130018235380162363432150211 195027353070243545148225317)
        ·
          refine ⟨36567628700670664715292247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195027353070243545148225317 36567628700670664715292247)
          ·
            refine ⟨54851443051005997072938371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36567628700670664715292247 54851443051005997072938371)
            ·
              refine ⟨82277164576508995609407557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54851443051005997072938371 82277164576508995609407557)
              ·
                refine ⟨15426968358095436676763917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82277164576508995609407557 15426968358095436676763917)
                ·
                  refine ⟨5785113134285788753786469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15426968358095436676763917 5785113134285788753786469)
                  ·
                    refine ⟨1084708712678585391334963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5785113134285788753786469 1084708712678585391334963)
                    ·
                      rfl

theorem cell23_6337388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_6337388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337388 prefixEnd_6337388 := by exact prefixLift 6337388
  have htrace : WordTrace (prefixWord ++ tailWord_6337388) baseStart_6337388 baseEnd_6337388 := by
    simpa [prefixWord, tailWord_6337388, baseEnd_6337388] using wordTrace_append hprefix tailTrace_6337388
  have hstable : (prefixWord ++ tailWord_6337388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337388).length < 2 ^ (prefixWord ++ tailWord_6337388).sum := by decide
  have hdescent : baseEnd_6337388 < baseStart_6337388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337401 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 8]
def baseStart_6337401 : Nat := 118140960795 + 6337401 * 2 ^ 59
def prefixEnd_6337401 : Nat := 4983230072969 + 3 ^ 40 * 6337401 * 2
def baseEnd_6337401 : Nat := 361570312587140513682481

theorem tailTrace_6337401 : CollatzResearch.WordTrace tailWord_6337401 prefixEnd_6337401 361570312587140513682481 := by
  unfold tailWord_6337401
  simp only [CollatzResearch.WordTrace]
  refine ⟨231144003713685993766268057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154096002475790662510845371 231144003713685993766268057)
  ·
    refine ⟨173358002785264495324701043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231144003713685993766268057 173358002785264495324701043)
    ·
      refine ⟨260037004177896742987051565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173358002785264495324701043 260037004177896742987051565)
      ·
        refine ⟨97513876566711278620144337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260037004177896742987051565 97513876566711278620144337)
        ·
          refine ⟨73135407425033458965108253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97513876566711278620144337 73135407425033458965108253)
          ·
            refine ⟨27425777784387547111915595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73135407425033458965108253 27425777784387547111915595)
            ·
              refine ⟨41138666676581320667873393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27425777784387547111915595 41138666676581320667873393)
              ·
                refine ⟨30854000007435990500905045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41138666676581320667873393 30854000007435990500905045)
                ·
                  refine ⟨361570312587140513682481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30854000007435990500905045 361570312587140513682481)
                  ·
                    rfl

theorem cell23_6337401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 8].length) (baseStart_6337401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337401 prefixEnd_6337401 := by exact prefixLift 6337401
  have htrace : WordTrace (prefixWord ++ tailWord_6337401) baseStart_6337401 baseEnd_6337401 := by
    simpa [prefixWord, tailWord_6337401, baseEnd_6337401] using wordTrace_append hprefix tailTrace_6337401
  have hstable : (prefixWord ++ tailWord_6337401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337401).length < 2 ^ (prefixWord ++ tailWord_6337401).sum := by decide
  have hdescent : baseEnd_6337401 < baseStart_6337401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337415 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_6337415 : Nat := 118140960795 + 6337415 * 2 ^ 59
def prefixEnd_6337415 : Nat := 4983230072969 + 3 ^ 40 * 6337415 * 2
def baseEnd_6337415 : Nat := 3254140002013427568367265

theorem tailTrace_6337415 : CollatzResearch.WordTrace tailWord_6337415 prefixEnd_6337415 3254140002013427568367265 := by
  unfold tailWord_6337415
  simp only [CollatzResearch.WordTrace]
  refine ⟨231144514335635274157277699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154096342890423516104851799 231144514335635274157277699)
  ·
    refine ⟨346716771503452911235916549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231144514335635274157277699 346716771503452911235916549)
    ·
      refine ⟨65009394656897420856734353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346716771503452911235916549 65009394656897420856734353)
      ·
        refine ⟨48757045992673065642550765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65009394656897420856734353 48757045992673065642550765)
        ·
          refine ⟨18283892247252399615956537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48757045992673065642550765 18283892247252399615956537)
          ·
            refine ⟨13712919185439299711967403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18283892247252399615956537 13712919185439299711967403)
            ·
              refine ⟨20569378778158949567951105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13712919185439299711967403 20569378778158949567951105)
              ·
                refine ⟨15427034083619212175963329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20569378778158949567951105 15427034083619212175963329)
                ·
                  refine ⟨11570275562714409131972497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15427034083619212175963329 11570275562714409131972497)
                  ·
                    refine ⟨8677706672035806848979373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11570275562714409131972497 8677706672035806848979373)
                    ·
                      refine ⟨3254140002013427568367265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8677706672035806848979373 3254140002013427568367265)
                      ·
                        rfl

theorem cell23_6337415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_6337415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337415 prefixEnd_6337415 := by exact prefixLift 6337415
  have htrace : WordTrace (prefixWord ++ tailWord_6337415) baseStart_6337415 baseEnd_6337415 := by
    simpa [prefixWord, tailWord_6337415, baseEnd_6337415] using wordTrace_append hprefix tailTrace_6337415
  have hstable : (prefixWord ++ tailWord_6337415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337415).length < 2 ^ (prefixWord ++ tailWord_6337415).sum := by decide
  have hdescent : baseEnd_6337415 < baseStart_6337415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337418 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 8]
def baseStart_6337418 : Nat := 118140960795 + 6337418 * 2 ^ 59
def prefixEnd_6337418 : Nat := 4983230072969 + 3 ^ 40 * 6337418 * 2
def baseEnd_6337418 : Nat := 361571282495043450736639

theorem tailTrace_6337418 : CollatzResearch.WordTrace tailWord_6337418 prefixEnd_6337418 361571282495043450736639 := by
  unfold tailWord_6337418
  simp only [CollatzResearch.WordTrace]
  refine ⟨57786155938656101417409227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154096415836416270446424605 57786155938656101417409227)
  ·
    refine ⟨86679233907984152126113841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57786155938656101417409227 86679233907984152126113841)
    ·
      refine ⟨65009425430988114094585381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86679233907984152126113841 65009425430988114094585381)
      ·
        refine ⟨12189267268310271392734759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65009425430988114094585381 12189267268310271392734759)
        ·
          refine ⟨18283900902465407089102139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12189267268310271392734759 18283900902465407089102139)
          ·
            refine ⟨27425851353698110633653209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18283900902465407089102139 27425851353698110633653209)
            ·
              refine ⟨20569388515273582975239907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27425851353698110633653209 20569388515273582975239907)
              ·
                refine ⟨30854082772910374462859861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20569388515273582975239907 30854082772910374462859861)
                ·
                  refine ⟨361571282495043450736639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30854082772910374462859861 361571282495043450736639)
                  ·
                    rfl

theorem cell23_6337418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_6337418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337418 prefixEnd_6337418 := by exact prefixLift 6337418
  have htrace : WordTrace (prefixWord ++ tailWord_6337418) baseStart_6337418 baseEnd_6337418 := by
    simpa [prefixWord, tailWord_6337418, baseEnd_6337418] using wordTrace_append hprefix tailTrace_6337418
  have hstable : (prefixWord ++ tailWord_6337418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337418).length < 2 ^ (prefixWord ++ tailWord_6337418).sum := by decide
  have hdescent : baseEnd_6337418 < baseStart_6337418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337451 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 4]
def baseStart_6337451 : Nat := 118140960795 + 6337451 * 2 ^ 59
def prefixEnd_6337451 : Nat := 4983230072969 + 3 ^ 40 * 6337451 * 2
def baseEnd_6337451 : Nat := 3254158487316989427517099

theorem tailTrace_6337451 : CollatzResearch.WordTrace tailWord_6337451 prefixEnd_6337451 3254158487316989427517099 := by
  unfold tailWord_6337451
  simp only [CollatzResearch.WordTrace]
  refine ⟨231145827363504852305588207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154097218242336568203725471 231145827363504852305588207)
  ·
    refine ⟨346718741045257278458382311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231145827363504852305588207 346718741045257278458382311)
    ·
      refine ⟨520078111567885917687573467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346718741045257278458382311 520078111567885917687573467)
      ·
        refine ⟨780117167351828876531360201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520078111567885917687573467 780117167351828876531360201)
        ·
          refine ⟨585087875513871657398520151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780117167351828876531360201 585087875513871657398520151)
          ·
            refine ⟨877631813270807486097780227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585087875513871657398520151 877631813270807486097780227)
            ·
              refine ⟨1316447719906211229146670341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877631813270807486097780227 1316447719906211229146670341)
              ·
                refine ⟨246833947482414605465000689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1316447719906211229146670341 246833947482414605465000689)
                ·
                  refine ⟨185125460611810954098750517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246833947482414605465000689 185125460611810954098750517)
                  ·
                    refine ⟨17355511932357276946757861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 185125460611810954098750517 17355511932357276946757861)
                    ·
                      refine ⟨3254158487316989427517099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17355511932357276946757861 3254158487316989427517099)
                      ·
                        rfl

theorem cell23_6337451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 4].length) (baseStart_6337451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337451 prefixEnd_6337451 := by exact prefixLift 6337451
  have htrace : WordTrace (prefixWord ++ tailWord_6337451) baseStart_6337451 baseEnd_6337451 := by
    simpa [prefixWord, tailWord_6337451, baseEnd_6337451] using wordTrace_append hprefix tailTrace_6337451
  have hstable : (prefixWord ++ tailWord_6337451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337451).length < 2 ^ (prefixWord ++ tailWord_6337451).sum := by decide
  have hdescent : baseEnd_6337451 < baseStart_6337451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337479 : List Nat := [1, 1, 4, 1, 1, 2, 6, 2, 1, 1, 3]
def baseStart_6337479 : Nat := 118140960795 + 6337479 * 2 ^ 59
def prefixEnd_6337479 : Nat := 4983230072969 + 3 ^ 40 * 6337479 * 2
def baseEnd_6337479 : Nat := 3254172864775315317966971

theorem tailTrace_6337479 : CollatzResearch.WordTrace tailWord_6337479 prefixEnd_6337479 3254172864775315317966971 := by
  unfold tailWord_6337479
  simp only [CollatzResearch.WordTrace]
  refine ⟨231146848607403413087607491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154097899071602275391738327 231146848607403413087607491)
  ·
    refine ⟨346720272911105119631411237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231146848607403413087607491 346720272911105119631411237)
    ·
      refine ⟨65010051170832209930889607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346720272911105119631411237 65010051170832209930889607)
      ·
        refine ⟨97515076756248314896334411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65010051170832209930889607 97515076756248314896334411)
        ·
          refine ⟨146272615134372472344501617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97515076756248314896334411 146272615134372472344501617)
          ·
            refine ⟨109704461350779354258376213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146272615134372472344501617 109704461350779354258376213)
            ·
              refine ⟨5142396625817782230861385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109704461350779354258376213 5142396625817782230861385)
              ·
                refine ⟨3856797469363336673146039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5142396625817782230861385 3856797469363336673146039)
                ·
                  refine ⟨5785196204045005009719059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856797469363336673146039 5785196204045005009719059)
                  ·
                    refine ⟨8677794306067507514578589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5785196204045005009719059 8677794306067507514578589)
                    ·
                      refine ⟨3254172864775315317966971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8677794306067507514578589 3254172864775315317966971)
                      ·
                        rfl

theorem cell23_6337479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_6337479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337479 prefixEnd_6337479 := by exact prefixLift 6337479
  have htrace : WordTrace (prefixWord ++ tailWord_6337479) baseStart_6337479 baseEnd_6337479 := by
    simpa [prefixWord, tailWord_6337479, baseEnd_6337479] using wordTrace_append hprefix tailTrace_6337479
  have hstable : (prefixWord ++ tailWord_6337479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337479).length < 2 ^ (prefixWord ++ tailWord_6337479).sum := by decide
  have hdescent : baseEnd_6337479 < baseStart_6337479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337505 : List Nat := [1, 2, 3, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_6337505 : Nat := 118140960795 + 6337505 * 2 ^ 59
def prefixEnd_6337505 : Nat := 4983230072969 + 3 ^ 40 * 6337505 * 2
def baseEnd_6337505 : Nat := 3254186215272332216241851

theorem tailTrace_6337505 : CollatzResearch.WordTrace tailWord_6337505 prefixEnd_6337505 3254186215272332216241851 := by
  unfold tailWord_6337505
  simp only [CollatzResearch.WordTrace]
  refine ⟨231147796905309219528053969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154098531270206146352035979 231147796905309219528053969)
  ·
    refine ⟨173360847678981914646040477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231147796905309219528053969 173360847678981914646040477)
    ·
      refine ⟨65010317879618217992265179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173360847678981914646040477 65010317879618217992265179)
      ·
        refine ⟨97515476819427326988397769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65010317879618217992265179 97515476819427326988397769)
        ·
          refine ⟨73136607614570495241298327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97515476819427326988397769 73136607614570495241298327)
          ·
            refine ⟨109704911421855742861947491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73136607614570495241298327 109704911421855742861947491)
            ·
              refine ⟨164557367132783614292921237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109704911421855742861947491 164557367132783614292921237)
              ·
                refine ⟨7713626584349231919980683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164557367132783614292921237 7713626584349231919980683)
                ·
                  refine ⟨11570439876523847879971025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7713626584349231919980683 11570439876523847879971025)
                  ·
                    refine ⟨8677829907392885909978269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11570439876523847879971025 8677829907392885909978269)
                    ·
                      refine ⟨3254186215272332216241851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8677829907392885909978269 3254186215272332216241851)
                      ·
                        rfl

theorem cell23_6337505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_6337505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337505 prefixEnd_6337505 := by exact prefixLift 6337505
  have htrace : WordTrace (prefixWord ++ tailWord_6337505) baseStart_6337505 baseEnd_6337505 := by
    simpa [prefixWord, tailWord_6337505, baseEnd_6337505] using wordTrace_append hprefix tailTrace_6337505
  have hstable : (prefixWord ++ tailWord_6337505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337505).length < 2 ^ (prefixWord ++ tailWord_6337505).sum := by decide
  have hdescent : baseEnd_6337505 < baseStart_6337505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337506 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_6337506 : Nat := 118140960795 + 6337506 * 2 ^ 59
def prefixEnd_6337506 : Nat := 4983230072969 + 3 ^ 40 * 6337506 * 2
def baseEnd_6337506 : Nat := 3254186728752986712329347

theorem tailTrace_6337506 : CollatzResearch.WordTrace tailWord_6337506 prefixEnd_6337506 3254186728752986712329347 := by
  unfold tailWord_6337506
  simp only [CollatzResearch.WordTrace]
  refine ⟨57786958344576399174710093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154098555585537064465893581 57786958344576399174710093)
  ·
    refine ⟨21670109379216149690516285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57786958344576399174710093 21670109379216149690516285)
    ·
      refine ⟨8126291017206056133943607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21670109379216149690516285 8126291017206056133943607)
      ·
        refine ⟨12189436525809084200915411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8126291017206056133943607 12189436525809084200915411)
        ·
          refine ⟨18284154788713626301373117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12189436525809084200915411 18284154788713626301373117)
          ·
            refine ⟨6856558045767609863014919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18284154788713626301373117 6856558045767609863014919)
            ·
              refine ⟨10284837068651414794522379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6856558045767609863014919 10284837068651414794522379)
              ·
                refine ⟨15427255602977122191783569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10284837068651414794522379 15427255602977122191783569)
                ·
                  refine ⟨11570441702232841643837677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15427255602977122191783569 11570441702232841643837677)
                  ·
                    refine ⟨4338915638337315616439129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11570441702232841643837677 4338915638337315616439129)
                    ·
                      refine ⟨3254186728752986712329347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338915638337315616439129 3254186728752986712329347)
                      ·
                        rfl

theorem cell23_6337506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_6337506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337506 prefixEnd_6337506 := by exact prefixLift 6337506
  have htrace : WordTrace (prefixWord ++ tailWord_6337506) baseStart_6337506 baseEnd_6337506 := by
    simpa [prefixWord, tailWord_6337506, baseEnd_6337506] using wordTrace_append hprefix tailTrace_6337506
  have hstable : (prefixWord ++ tailWord_6337506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337506).length < 2 ^ (prefixWord ++ tailWord_6337506).sum := by decide
  have hdescent : baseEnd_6337506 < baseStart_6337506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337519 : List Nat := [1, 1, 2, 1, 4, 3, 1, 5, 1, 2, 2]
def baseStart_6337519 : Nat := 118140960795 + 6337519 * 2 ^ 59
def prefixEnd_6337519 : Nat := 4983230072969 + 3 ^ 40 * 6337519 * 2
def baseEnd_6337519 : Nat := 3254193404001495161466787

theorem tailTrace_6337519 : CollatzResearch.WordTrace tailWord_6337519 prefixEnd_6337519 3254193404001495161466787 := by
  unfold tailWord_6337519
  simp only [CollatzResearch.WordTrace]
  refine ⟨231148307527258499919063611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154098871684838999946042407 231148307527258499919063611)
  ·
    refine ⟨346722461290887749878595417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231148307527258499919063611 346722461290887749878595417)
    ·
      refine ⟨260041845968165812408946563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346722461290887749878595417 260041845968165812408946563)
      ·
        refine ⟨390062768952248718613419845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260041845968165812408946563 390062768952248718613419845)
        ·
          refine ⟨73136769178546634740016221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 390062768952248718613419845 73136769178546634740016221)
          ·
            refine ⟨27426288441954988027506083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73136769178546634740016221 27426288441954988027506083)
            ·
              refine ⟨41139432662932482041259125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27426288441954988027506083 41139432662932482041259125)
              ·
                refine ⟨3856821812149920191368043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41139432662932482041259125 3856821812149920191368043)
                ·
                  refine ⟨5785232718224880287052065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856821812149920191368043 5785232718224880287052065)
                  ·
                    refine ⟨4338924538668660215289049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5785232718224880287052065 4338924538668660215289049)
                    ·
                      refine ⟨3254193404001495161466787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338924538668660215289049 3254193404001495161466787)
                      ·
                        rfl

theorem cell23_6337519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 1, 2, 2].length) (baseStart_6337519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337519 prefixEnd_6337519 := by exact prefixLift 6337519
  have htrace : WordTrace (prefixWord ++ tailWord_6337519) baseStart_6337519 baseEnd_6337519 := by
    simpa [prefixWord, tailWord_6337519, baseEnd_6337519] using wordTrace_append hprefix tailTrace_6337519
  have hstable : (prefixWord ++ tailWord_6337519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337519).length < 2 ^ (prefixWord ++ tailWord_6337519).sum := by decide
  have hdescent : baseEnd_6337519 < baseStart_6337519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337545 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 5, 3, 2]
def baseStart_6337545 : Nat := 118140960795 + 6337545 * 2 ^ 59
def prefixEnd_6337545 : Nat := 4983230072969 + 3 ^ 40 * 6337545 * 2
def baseEnd_6337545 : Nat := 3254206754498512059741667

theorem tailTrace_6337545 : CollatzResearch.WordTrace tailWord_6337545 prefixEnd_6337545 3254206754498512059741667 := by
  unfold tailWord_6337545
  simp only [CollatzResearch.WordTrace]
  refine ⟨231149255825164306359510089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154099503883442870906340059 231149255825164306359510089)
  ·
    refine ⟨173361941868873229769632567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231149255825164306359510089 173361941868873229769632567)
    ·
      refine ⟨260042912803309844654448851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173361941868873229769632567 260042912803309844654448851)
      ·
        refine ⟨390064369204964766981673277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260042912803309844654448851 390064369204964766981673277)
        ·
          refine ⟨146274138451861787618127479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390064369204964766981673277 146274138451861787618127479)
          ·
            refine ⟨219411207677792681427191219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146274138451861787618127479 219411207677792681427191219)
            ·
              refine ⟨329116811516689022140786829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219411207677792681427191219 329116811516689022140786829)
              ·
                refine ⟨123418804318758383302795061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329116811516689022140786829 123418804318758383302795061)
                ·
                  refine ⟨11570512904883598434637037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123418804318758383302795061 11570512904883598434637037)
                  ·
                    refine ⟨4338942339331349412988889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11570512904883598434637037 4338942339331349412988889)
                    ·
                      refine ⟨3254206754498512059741667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4338942339331349412988889 3254206754498512059741667)
                      ·
                        rfl

theorem cell23_6337545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 3, 2].length) (baseStart_6337545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337545 prefixEnd_6337545 := by exact prefixLift 6337545
  have htrace : WordTrace (prefixWord ++ tailWord_6337545) baseStart_6337545 baseEnd_6337545 := by
    simpa [prefixWord, tailWord_6337545, baseEnd_6337545] using wordTrace_append hprefix tailTrace_6337545
  have hstable : (prefixWord ++ tailWord_6337545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337545).length < 2 ^ (prefixWord ++ tailWord_6337545).sum := by decide
  have hdescent : baseEnd_6337545 < baseStart_6337545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337630 : List Nat := [4, 4, 1, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_6337630 : Nat := 118140960795 + 6337630 * 2 ^ 59
def prefixEnd_6337630 : Nat := 4983230072969 + 3 ^ 40 * 6337630 * 2
def baseEnd_6337630 : Nat := 3254250400354144227178777

theorem tailTrace_6337630 : CollatzResearch.WordTrace tailWord_6337630 prefixEnd_6337630 3254250400354144227178777 := by
  unfold tailWord_6337630
  simp only [CollatzResearch.WordTrace]
  refine ⟨28894044503732045734544293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154101570686570910584236229 28894044503732045734544293)
  ·
    refine ⟨5417633344449758575227055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28894044503732045734544293 5417633344449758575227055)
    ·
      refine ⟨8126450016674637862840583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5417633344449758575227055 8126450016674637862840583)
      ·
        refine ⟨12189675025011956794260875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8126450016674637862840583 12189675025011956794260875)
        ·
          refine ⟨18284512537517935191391313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12189675025011956794260875 18284512537517935191391313)
          ·
            refine ⟨13713384403138451393543485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18284512537517935191391313 13713384403138451393543485)
            ·
              refine ⟨5142519151176919272578807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13713384403138451393543485 5142519151176919272578807)
              ·
                refine ⟨7713778726765378908868211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142519151176919272578807 7713778726765378908868211)
                ·
                  refine ⟨11570668090148068363302317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7713778726765378908868211 11570668090148068363302317)
                  ·
                    refine ⟨4339000533805525636238369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11570668090148068363302317 4339000533805525636238369)
                    ·
                      refine ⟨3254250400354144227178777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4339000533805525636238369 3254250400354144227178777)
                      ·
                        rfl

theorem cell23_6337630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_6337630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337630 prefixEnd_6337630 := by exact prefixLift 6337630
  have htrace : WordTrace (prefixWord ++ tailWord_6337630) baseStart_6337630 baseEnd_6337630 := by
    simpa [prefixWord, tailWord_6337630, baseEnd_6337630] using wordTrace_append hprefix tailTrace_6337630
  have hstable : (prefixWord ++ tailWord_6337630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337630).length < 2 ^ (prefixWord ++ tailWord_6337630).sum := by decide
  have hdescent : baseEnd_6337630 < baseStart_6337630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337682 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_6337682 : Nat := 118140960795 + 6337682 * 2 ^ 59
def prefixEnd_6337682 : Nat := 4983230072969 + 3 ^ 40 * 6337682 * 2
def baseEnd_6337682 : Nat := 3254277101348178023728537

theorem tailTrace_6337682 : CollatzResearch.WordTrace tailWord_6337682 prefixEnd_6337682 3254277101348178023728537 := by
  unfold tailWord_6337682
  simp only [CollatzResearch.WordTrace]
  refine ⟨57788563156416994689311825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154102835083778652504831533 57788563156416994689311825)
  ·
    refine ⟨43341422367312746016983869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57788563156416994689311825 43341422367312746016983869)
    ·
      refine ⟨16253033387742279756368951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43341422367312746016983869 16253033387742279756368951)
      ·
        refine ⟨24379550081613419634553427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16253033387742279756368951 24379550081613419634553427)
        ·
          refine ⟨36569325122420129451830141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24379550081613419634553427 36569325122420129451830141)
          ·
            refine ⟨13713496920907548544436303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36569325122420129451830141 13713496920907548544436303)
            ·
              refine ⟨20570245381361322816654455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13713496920907548544436303 20570245381361322816654455)
              ·
                refine ⟨30855368072041984224981683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20570245381361322816654455 30855368072041984224981683)
                ·
                  refine ⟨46283052108062976337472525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30855368072041984224981683 46283052108062976337472525)
                  ·
                    refine ⟨17356144540523616126552197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46283052108062976337472525 17356144540523616126552197)
                    ·
                      refine ⟨3254277101348178023728537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17356144540523616126552197 3254277101348178023728537)
                      ·
                        rfl

theorem cell23_6337682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_6337682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337682 prefixEnd_6337682 := by exact prefixLift 6337682
  have htrace : WordTrace (prefixWord ++ tailWord_6337682) baseStart_6337682 baseEnd_6337682 := by
    simpa [prefixWord, tailWord_6337682, baseEnd_6337682] using wordTrace_append hprefix tailTrace_6337682
  have hstable : (prefixWord ++ tailWord_6337682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337682).length < 2 ^ (prefixWord ++ tailWord_6337682).sum := by decide
  have hdescent : baseEnd_6337682 < baseStart_6337682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337735 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 3, 5]
def baseStart_6337735 : Nat := 118140960795 + 6337735 * 2 ^ 59
def prefixEnd_6337735 : Nat := 4983230072969 + 3 ^ 40 * 6337735 * 2
def baseEnd_6337735 : Nat := 1084768105274288772121931

theorem tailTrace_6337735 : CollatzResearch.WordTrace tailWord_6337735 prefixEnd_6337735 1084768105274288772121931 := by
  unfold tailWord_6337735
  simp only [CollatzResearch.WordTrace]
  refine ⟨231156185694475968808926659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154104123796317312539284439 231156185694475968808926659)
  ·
    refine ⟨346734278541713953213389989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231156185694475968808926659 346734278541713953213389989)
    ·
      refine ⟨65012677226571366227510623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346734278541713953213389989 65012677226571366227510623)
      ·
        refine ⟨97519015839857049341265935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65012677226571366227510623 97519015839857049341265935)
        ·
          refine ⟨146278523759785574011898903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97519015839857049341265935 146278523759785574011898903)
          ·
            refine ⟨219417785639678361017848355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146278523759785574011898903 219417785639678361017848355)
            ·
              refine ⟨329126678459517541526772533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219417785639678361017848355 329126678459517541526772533)
              ·
                refine ⟨30855626105579769518134925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 329126678459517541526772533 30855626105579769518134925)
                ·
                  refine ⟨11570859789592413569300597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30855626105579769518134925 11570859789592413569300597)
                  ·
                    refine ⟨1084768105274288772121931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11570859789592413569300597 1084768105274288772121931)
                    ·
                      rfl

theorem cell23_6337735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_6337735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337735 prefixEnd_6337735 := by exact prefixLift 6337735
  have htrace : WordTrace (prefixWord ++ tailWord_6337735) baseStart_6337735 baseEnd_6337735 := by
    simpa [prefixWord, tailWord_6337735, baseEnd_6337735] using wordTrace_append hprefix tailTrace_6337735
  have hstable : (prefixWord ++ tailWord_6337735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337735).length < 2 ^ (prefixWord ++ tailWord_6337735).sum := by decide
  have hdescent : baseEnd_6337735 < baseStart_6337735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337782 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_6337782 : Nat := 118140960795 + 6337782 * 2 ^ 59
def prefixEnd_6337782 : Nat := 4983230072969 + 3 ^ 40 * 6337782 * 2
def baseEnd_6337782 : Nat := 1084776149804542544159359

theorem tailTrace_6337782 : CollatzResearch.WordTrace tailWord_6337782 prefixEnd_6337782 1084776149804542544159359 := by
  unfold tailWord_6337782
  simp only [CollatzResearch.WordTrace]
  refine ⟨14447368745331605989742975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154105266616870463890591733 14447368745331605989742975)
  ·
    refine ⟨21671053117997408984614463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14447368745331605989742975 21671053117997408984614463)
    ·
      refine ⟨32506579676996113476921695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21671053117997408984614463 32506579676996113476921695)
      ·
        refine ⟨48759869515494170215382543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32506579676996113476921695 48759869515494170215382543)
        ·
          refine ⟨73139804273241255323073815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48759869515494170215382543 73139804273241255323073815)
          ·
            refine ⟨109709706409861882984610723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73139804273241255323073815 109709706409861882984610723)
            ·
              refine ⟨164564559614792824476916085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109709706409861882984610723 164564559614792824476916085)
              ·
                refine ⟨15427927463886827294710883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164564559614792824476916085 15427927463886827294710883)
                ·
                  refine ⟨23141891195830240942066325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15427927463886827294710883 23141891195830240942066325)
                  ·
                    refine ⟨1084776149804542544159359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23141891195830240942066325 1084776149804542544159359)
                    ·
                      rfl

theorem cell23_6337782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_6337782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337782 prefixEnd_6337782 := by exact prefixLift 6337782
  have htrace : WordTrace (prefixWord ++ tailWord_6337782) baseStart_6337782 baseEnd_6337782 := by
    simpa [prefixWord, tailWord_6337782, baseEnd_6337782] using wordTrace_append hprefix tailTrace_6337782
  have hstable : (prefixWord ++ tailWord_6337782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337782).length < 2 ^ (prefixWord ++ tailWord_6337782).sum := by decide
  have hdescent : baseEnd_6337782 < baseStart_6337782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337785 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 6]
def baseStart_6337785 : Nat := 118140960795 + 6337785 * 2 ^ 59
def prefixEnd_6337785 : Nat := 4983230072969 + 3 ^ 40 * 6337785 * 2
def baseEnd_6337785 : Nat := 3254329989855591120740563

theorem tailTrace_6337785 : CollatzResearch.WordTrace tailWord_6337785 prefixEnd_6337785 3254329989855591120740563 := by
  unfold tailWord_6337785
  simp only [CollatzResearch.WordTrace]
  refine ⟨231158009344294827348246809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154105339562863218232164539 231158009344294827348246809)
  ·
    refine ⟨173368507008221120511185107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231158009344294827348246809 173368507008221120511185107)
    ·
      refine ⟨260052760512331680766777661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173368507008221120511185107 260052760512331680766777661)
      ·
        refine ⟨97519785192124380287541623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260052760512331680766777661 97519785192124380287541623)
        ·
          refine ⟨146279677788186570431312435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97519785192124380287541623 146279677788186570431312435)
          ·
            refine ⟨219419516682279855646968653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146279677788186570431312435 219419516682279855646968653)
            ·
              refine ⟨82282318755854945867613245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219419516682279855646968653 82282318755854945867613245)
              ·
                refine ⟨30855869533445604700354967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82282318755854945867613245 30855869533445604700354967)
                ·
                  refine ⟨46283804300168407050532451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30855869533445604700354967 46283804300168407050532451)
                  ·
                    refine ⟨69425706450252610575798677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46283804300168407050532451 69425706450252610575798677)
                    ·
                      refine ⟨3254329989855591120740563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69425706450252610575798677 3254329989855591120740563)
                      ·
                        rfl

theorem cell23_6337785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_6337785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337785 prefixEnd_6337785 := by exact prefixLift 6337785
  have htrace : WordTrace (prefixWord ++ tailWord_6337785) baseStart_6337785 baseEnd_6337785 := by
    simpa [prefixWord, tailWord_6337785, baseEnd_6337785] using wordTrace_append hprefix tailTrace_6337785
  have hstable : (prefixWord ++ tailWord_6337785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337785).length < 2 ^ (prefixWord ++ tailWord_6337785).sum := by decide
  have hdescent : baseEnd_6337785 < baseStart_6337785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337795 : List Nat := [1, 1, 1, 3, 2, 4, 2, 9]
def baseStart_6337795 : Nat := 118140960795 + 6337795 * 2 ^ 59
def prefixEnd_6337795 : Nat := 4983230072969 + 3 ^ 40 * 6337795 * 2
def baseEnd_6337795 : Nat := 120530930543042077096871

theorem tailTrace_6337795 : CollatzResearch.WordTrace tailWord_6337795 prefixEnd_6337795 120530930543042077096871 := by
  unfold tailWord_6337795
  simp only [CollatzResearch.WordTrace]
  refine ⟨231158374074258599056110839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154105582716172399370740559 231158374074258599056110839)
  ·
    refine ⟨346737561111387898584166259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231158374074258599056110839 346737561111387898584166259)
    ·
      refine ⟨520106341667081847876249389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346737561111387898584166259 520106341667081847876249389)
      ·
        refine ⟨195039878125155692953593521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 520106341667081847876249389 195039878125155692953593521)
        ·
          refine ⟨146279908593866769715195141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195039878125155692953593521 146279908593866769715195141)
          ·
            refine ⟨27427482861350019321599089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146279908593866769715195141 27427482861350019321599089)
            ·
              refine ⟨20570612146012514491199317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27427482861350019321599089 20570612146012514491199317)
              ·
                refine ⟨120530930543042077096871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20570612146012514491199317 120530930543042077096871)
                ·
                  rfl

theorem cell23_6337795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 9].length) (baseStart_6337795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337795 prefixEnd_6337795 := by exact prefixLift 6337795
  have htrace : WordTrace (prefixWord ++ tailWord_6337795) baseStart_6337795 baseEnd_6337795 := by
    simpa [prefixWord, tailWord_6337795, baseEnd_6337795] using wordTrace_append hprefix tailTrace_6337795
  have hstable : (prefixWord ++ tailWord_6337795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337795).length < 2 ^ (prefixWord ++ tailWord_6337795).sum := by decide
  have hdescent : baseEnd_6337795 < baseStart_6337795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337806 : List Nat := [4, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4]
def baseStart_6337806 : Nat := 118140960795 + 6337806 * 2 ^ 59
def prefixEnd_6337806 : Nat := 4983230072969 + 3 ^ 40 * 6337806 * 2
def baseEnd_6337806 : Nat := 3254340772949335538577967

theorem tailTrace_6337806 : CollatzResearch.WordTrace tailWord_6337806 prefixEnd_6337806 3254340772949335538577967 := by
  unfold tailWord_6337806
  simp only [CollatzResearch.WordTrace]
  refine ⟨28894846909652343491845159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154105850184812498623174181 28894846909652343491845159)
  ·
    refine ⟨43342270364478515237767739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28894846909652343491845159 43342270364478515237767739)
    ·
      refine ⟨65013405546717772856651609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43342270364478515237767739 65013405546717772856651609)
      ·
        refine ⟨48760054160038329642488707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65013405546717772856651609 48760054160038329642488707)
        ·
          refine ⟨73140081240057494463733061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48760054160038329642488707 73140081240057494463733061)
          ·
            refine ⟨13713765232510780211949949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73140081240057494463733061 13713765232510780211949949)
            ·
              refine ⟨5142661962191542579481231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13713765232510780211949949 5142661962191542579481231)
              ·
                refine ⟨7713992943287313869221847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142661962191542579481231 7713992943287313869221847)
                ·
                  refine ⟨11570989414930970803832771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7713992943287313869221847 11570989414930970803832771)
                  ·
                    refine ⟨17356484122396456205749157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11570989414930970803832771 17356484122396456205749157)
                    ·
                      refine ⟨3254340772949335538577967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17356484122396456205749157 3254340772949335538577967)
                      ·
                        rfl

theorem cell23_6337806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_6337806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337806 prefixEnd_6337806 := by exact prefixLift 6337806
  have htrace : WordTrace (prefixWord ++ tailWord_6337806) baseStart_6337806 baseEnd_6337806 := by
    simpa [prefixWord, tailWord_6337806, baseEnd_6337806] using wordTrace_append hprefix tailTrace_6337806
  have hstable : (prefixWord ++ tailWord_6337806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337806).length < 2 ^ (prefixWord ++ tailWord_6337806).sum := by decide
  have hdescent : baseEnd_6337806 < baseStart_6337806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337835 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 5]
def baseStart_6337835 : Nat := 118140960795 + 6337835 * 2 ^ 59
def prefixEnd_6337835 : Nat := 4983230072969 + 3 ^ 40 * 6337835 * 2
def baseEnd_6337835 : Nat := 3254355663888315925115333

theorem tailTrace_6337835 : CollatzResearch.WordTrace tailWord_6337835 prefixEnd_6337835 3254355663888315925115333 := by
  unfold tailWord_6337835
  simp only [CollatzResearch.WordTrace]
  refine ⟨231159832994113685887566959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154106555329409123925044639 231159832994113685887566959)
  ·
    refine ⟨346739749491170528831350439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231159832994113685887566959 346739749491170528831350439)
    ·
      refine ⟨520109624236755793247025659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346739749491170528831350439 520109624236755793247025659)
      ·
        refine ⟨780164436355133689870538489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520109624236755793247025659 780164436355133689870538489)
        ·
          refine ⟨585123327266350267402903867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780164436355133689870538489 585123327266350267402903867)
          ·
            refine ⟨877684990899525401104355801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585123327266350267402903867 877684990899525401104355801)
            ·
              refine ⟨658263743174644050828266851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 877684990899525401104355801 658263743174644050828266851)
              ·
                refine ⟨987395614761966076242400277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658263743174644050828266851 987395614761966076242400277)
                ·
                  refine ⟨46284169441967159823862513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 987395614761966076242400277 46284169441967159823862513)
                  ·
                    refine ⟨34713127081475369867896885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46284169441967159823862513 34713127081475369867896885)
                    ·
                      refine ⟨3254355663888315925115333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34713127081475369867896885 3254355663888315925115333)
                      ·
                        rfl

theorem cell23_6337835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 5].length) (baseStart_6337835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337835 prefixEnd_6337835 := by exact prefixLift 6337835
  have htrace : WordTrace (prefixWord ++ tailWord_6337835) baseStart_6337835 baseEnd_6337835 := by
    simpa [prefixWord, tailWord_6337835, baseEnd_6337835] using wordTrace_append hprefix tailTrace_6337835
  have hstable : (prefixWord ++ tailWord_6337835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337835).length < 2 ^ (prefixWord ++ tailWord_6337835).sum := by decide
  have hdescent : baseEnd_6337835 < baseStart_6337835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337860 : List Nat := [2, 3, 4, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_6337860 : Nat := 118140960795 + 6337860 * 2 ^ 59
def prefixEnd_6337860 : Nat := 4983230072969 + 3 ^ 40 * 6337860 * 2
def baseEnd_6337860 : Nat := 3254368500904678327302719

theorem tailTrace_6337860 : CollatzResearch.WordTrace tailWord_6337860 prefixEnd_6337860 3254368500904678327302719 := by
  unfold tailWord_6337860
  simp only [CollatzResearch.WordTrace]
  refine ⟨115580372409511557578613517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154107163212682076771484689 115580372409511557578613517)
  ·
    refine ⟨43342639653566834091980069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115580372409511557578613517 43342639653566834091980069)
    ·
      refine ⟨8126744935043781392246263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43342639653566834091980069 8126744935043781392246263)
      ·
        refine ⟨12190117402565672088369395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8126744935043781392246263 12190117402565672088369395)
        ·
          refine ⟨18285176103848508132554093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12190117402565672088369395 18285176103848508132554093)
          ·
            refine ⟨6856941038943190549707785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18285176103848508132554093 6856941038943190549707785)
            ·
              refine ⟨5142705779207392912280839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6856941038943190549707785 5142705779207392912280839)
              ·
                refine ⟨7714058668811089368421259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142705779207392912280839 7714058668811089368421259)
                ·
                  refine ⟨11571088003216634052631889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7714058668811089368421259 11571088003216634052631889)
                  ·
                    refine ⟨8678316002412475539473917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11571088003216634052631889 8678316002412475539473917)
                    ·
                      refine ⟨3254368500904678327302719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8678316002412475539473917 3254368500904678327302719)
                      ·
                        rfl

theorem cell23_6337860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_6337860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337860 prefixEnd_6337860 := by exact prefixLift 6337860
  have htrace : WordTrace (prefixWord ++ tailWord_6337860) baseStart_6337860 baseEnd_6337860 := by
    simpa [prefixWord, tailWord_6337860, baseEnd_6337860] using wordTrace_append hprefix tailTrace_6337860
  have hstable : (prefixWord ++ tailWord_6337860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337860).length < 2 ^ (prefixWord ++ tailWord_6337860).sum := by decide
  have hdescent : baseEnd_6337860 < baseStart_6337860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337882 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3]
def baseStart_6337882 : Nat := 118140960795 + 6337882 * 2 ^ 59
def prefixEnd_6337882 : Nat := 4983230072969 + 3 ^ 40 * 6337882 * 2
def baseEnd_6337882 : Nat := 3254379797479077241227617

theorem tailTrace_6337882 : CollatzResearch.WordTrace tailWord_6337882 prefixEnd_6337882 3254379797479077241227617 := by
  unfold tailWord_6337882
  simp only [CollatzResearch.WordTrace]
  refine ⟨57790386806235853228631975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154107698149962275276351933 57790386806235853228631975)
  ·
    refine ⟨86685580209353779842947963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57790386806235853228631975 86685580209353779842947963)
    ·
      refine ⟨130028370314030669764421945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86685580209353779842947963 130028370314030669764421945)
      ·
        refine ⟨97521277735523002323316459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130028370314030669764421945 97521277735523002323316459)
        ·
          refine ⟨146281916603284503484974689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97521277735523002323316459 146281916603284503484974689)
          ·
            refine ⟨109711437452463377613731017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146281916603284503484974689 109711437452463377613731017)
            ·
              refine ⟨82283578089347533210298263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109711437452463377613731017 82283578089347533210298263)
              ·
                refine ⟨123425367134021299815447395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82283578089347533210298263 123425367134021299815447395)
                ·
                  refine ⟨185138050701031949723171093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123425367134021299815447395 185138050701031949723171093)
                  ·
                    refine ⟨8678346126610872643273645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 185138050701031949723171093 8678346126610872643273645)
                    ·
                      refine ⟨3254379797479077241227617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8678346126610872643273645 3254379797479077241227617)
                      ·
                        rfl

theorem cell23_6337882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_6337882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6337882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6337882 prefixEnd_6337882 := by exact prefixLift 6337882
  have htrace : WordTrace (prefixWord ++ tailWord_6337882) baseStart_6337882 baseEnd_6337882 := by
    simpa [prefixWord, tailWord_6337882, baseEnd_6337882] using wordTrace_append hprefix tailTrace_6337882
  have hstable : (prefixWord ++ tailWord_6337882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337882).length < 2 ^ (prefixWord ++ tailWord_6337882).sum := by decide
  have hdescent : baseEnd_6337882 < baseStart_6337882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338009 : List Nat := [1, 2, 1, 2, 4, 2, 2, 3, 6]
def baseStart_6338009 : Nat := 118140960795 + 6338009 * 2 ^ 59
def prefixEnd_6338009 : Nat := 4983230072969 + 3 ^ 40 * 6338009 * 2
def baseEnd_6338009 : Nat := 361605001058022027148837

theorem tailTrace_6338009 : CollatzResearch.WordTrace tailWord_6338009 prefixEnd_6338009 361605001058022027148837 := by
  unfold tailWord_6338009
  simp only [CollatzResearch.WordTrace]
  refine ⟨231166179295483313604401081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154110786196988875736267387 231166179295483313604401081)
  ·
    refine ⟨173374634471612485203300811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231166179295483313604401081 173374634471612485203300811)
    ·
      refine ⟨260061951707418727804951217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173374634471612485203300811 260061951707418727804951217)
      ·
        refine ⟨195046463780564045853713413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260061951707418727804951217 195046463780564045853713413)
        ·
          refine ⟨36571211958855758597571265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195046463780564045853713413 36571211958855758597571265)
          ·
            refine ⟨27428408969141818948178449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36571211958855758597571265 27428408969141818948178449)
            ·
              refine ⟨20571306726856364211133837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27428408969141818948178449 20571306726856364211133837)
              ·
                refine ⟨7714240022571136579175189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20571306726856364211133837 7714240022571136579175189)
                ·
                  refine ⟨361605001058022027148837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7714240022571136579175189 361605001058022027148837)
                  ·
                    rfl

theorem cell23_6338009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 6].length) (baseStart_6338009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338009 prefixEnd_6338009 := by exact prefixLift 6338009
  have htrace : WordTrace (prefixWord ++ tailWord_6338009) baseStart_6338009 baseEnd_6338009 := by
    simpa [prefixWord, tailWord_6338009, baseEnd_6338009] using wordTrace_append hprefix tailTrace_6338009
  have hstable : (prefixWord ++ tailWord_6338009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338009).length < 2 ^ (prefixWord ++ tailWord_6338009).sum := by decide
  have hdescent : baseEnd_6338009 < baseStart_6338009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338023 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_6338023 : Nat := 118140960795 + 6338023 * 2 ^ 59
def prefixEnd_6338023 : Nat := 4983230072969 + 3 ^ 40 * 6338023 * 2
def baseEnd_6338023 : Nat := 3254452198251361189564469

theorem tailTrace_6338023 : CollatzResearch.WordTrace tailWord_6338023 prefixEnd_6338023 3254452198251361189564469 := by
  unfold tailWord_6338023
  simp only [CollatzResearch.WordTrace]
  refine ⟨231166689917432593995410723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154111126611621729330273815 231166689917432593995410723)
  ·
    refine ⟨346750034876148890993116085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231166689917432593995410723 346750034876148890993116085)
    ·
      refine ⟨32507815769638958530604633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 346750034876148890993116085 32507815769638958530604633)
      ·
        refine ⟨24380861827229218897953475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32507815769638958530604633 24380861827229218897953475)
        ·
          refine ⟨36571292740843828346930213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24380861827229218897953475 36571292740843828346930213)
          ·
            refine ⟨6857117388908217815049415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36571292740843828346930213 6857117388908217815049415)
            ·
              refine ⟨10285676083362326722574123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6857117388908217815049415 10285676083362326722574123)
              ·
                refine ⟨15428514125043490083861185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10285676083362326722574123 15428514125043490083861185)
                ·
                  refine ⟨11571385593782617562895889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15428514125043490083861185 11571385593782617562895889)
                  ·
                    refine ⟨8678539195336963172171917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11571385593782617562895889 8678539195336963172171917)
                    ·
                      refine ⟨3254452198251361189564469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8678539195336963172171917 3254452198251361189564469)
                      ·
                        rfl

theorem cell23_6338023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_6338023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338023 prefixEnd_6338023 := by exact prefixLift 6338023
  have htrace : WordTrace (prefixWord ++ tailWord_6338023) baseStart_6338023 baseEnd_6338023 := by
    simpa [prefixWord, tailWord_6338023, baseEnd_6338023] using wordTrace_append hprefix tailTrace_6338023
  have hstable : (prefixWord ++ tailWord_6338023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338023).length < 2 ^ (prefixWord ++ tailWord_6338023).sum := by decide
  have hdescent : baseEnd_6338023 < baseStart_6338023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338076 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_6338076 : Nat := 118140960795 + 6338076 * 2 ^ 59
def prefixEnd_6338076 : Nat := 4983230072969 + 3 ^ 40 * 6338076 * 2
def baseEnd_6338076 : Nat := 3254479412726049482201725

theorem tailTrace_6338076 : CollatzResearch.WordTrace tailWord_6338076 prefixEnd_6338076 3254479412726049482201725 := by
  unfold tailWord_6338076
  simp only [CollatzResearch.WordTrace]
  refine ⟨115584311493120292023545041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154112415324160389364726721 115584311493120292023545041)
  ·
    refine ⟨86688233619840219017658781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115584311493120292023545041 86688233619840219017658781)
    ·
      refine ⟨32508087607440082131622043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86688233619840219017658781 32508087607440082131622043)
      ·
        refine ⟨48762131411160123197433065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32508087607440082131622043 48762131411160123197433065)
        ·
          refine ⟨36571598558370092398074799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48762131411160123197433065 36571598558370092398074799)
          ·
            refine ⟨54857397837555138597112199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36571598558370092398074799 54857397837555138597112199)
            ·
              refine ⟨82286096756332707895668299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54857397837555138597112199 82286096756332707895668299)
              ·
                refine ⟨123429145134499061843502449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82286096756332707895668299 123429145134499061843502449)
                ·
                  refine ⟨92571858850874296382626837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123429145134499061843502449 92571858850874296382626837)
                  ·
                    refine ⟨4339305883634732642935633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92571858850874296382626837 4339305883634732642935633)
                    ·
                      refine ⟨3254479412726049482201725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4339305883634732642935633 3254479412726049482201725)
                      ·
                        rfl

theorem cell23_6338076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_6338076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338076 prefixEnd_6338076 := by exact prefixLift 6338076
  have htrace : WordTrace (prefixWord ++ tailWord_6338076) baseStart_6338076 baseEnd_6338076 := by
    simpa [prefixWord, tailWord_6338076, baseEnd_6338076] using wordTrace_append hprefix tailTrace_6338076
  have hstable : (prefixWord ++ tailWord_6338076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338076).length < 2 ^ (prefixWord ++ tailWord_6338076).sum := by decide
  have hdescent : baseEnd_6338076 < baseStart_6338076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338099 : List Nat := [1, 1, 1, 2, 4, 5, 9]
def baseStart_6338099 : Nat := 118140960795 + 6338099 * 2 ^ 59
def prefixEnd_6338099 : Nat := 4983230072969 + 3 ^ 40 * 6338099 * 2
def baseEnd_6338099 : Nat := 40178903984951887558199

theorem tailTrace_6338099 : CollatzResearch.WordTrace tailWord_6338099 prefixEnd_6338099 40178903984951887558199 := by
  unfold tailWord_6338099
  simp only [CollatzResearch.WordTrace]
  refine ⟨231169461865157258975177351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154112974576771505983451567 231169461865157258975177351)
  ·
    refine ⟨346754192797735888462766027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231169461865157258975177351 346754192797735888462766027)
    ·
      refine ⟨520131289196603832694149041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346754192797735888462766027 520131289196603832694149041)
      ·
        refine ⟨390098466897452874520611781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520131289196603832694149041 390098466897452874520611781)
        ·
          refine ⟨73143462543272413972614709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 390098466897452874520611781 73143462543272413972614709)
          ·
            refine ⟨6857199613431788809932629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73143462543272413972614709 6857199613431788809932629)
            ·
              refine ⟨40178903984951887558199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6857199613431788809932629 40178903984951887558199)
              ·
                rfl

theorem cell23_6338099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 9].length) (baseStart_6338099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338099 prefixEnd_6338099 := by exact prefixLift 6338099
  have htrace : WordTrace (prefixWord ++ tailWord_6338099) baseStart_6338099 baseEnd_6338099 := by
    simpa [prefixWord, tailWord_6338099, baseEnd_6338099] using wordTrace_append hprefix tailTrace_6338099
  have hstable : (prefixWord ++ tailWord_6338099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338099).length < 2 ^ (prefixWord ++ tailWord_6338099).sum := by decide
  have hdescent : baseEnd_6338099 < baseStart_6338099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338126 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_6338126 : Nat := 118140960795 + 6338126 * 2 ^ 59
def prefixEnd_6338126 : Nat := 4983230072969 + 3 ^ 40 * 6338126 * 2
def baseEnd_6338126 : Nat := 3254505086758774286576495

theorem tailTrace_6338126 : CollatzResearch.WordTrace tailWord_6338126 prefixEnd_6338126 3254505086758774286576495 := by
  unfold tailWord_6338126
  simp only [CollatzResearch.WordTrace]
  refine ⟨28896305829507430323301279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154113631090706295057606821 28896305829507430323301279)
  ·
    refine ⟨43344458744261145484951919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28896305829507430323301279 43344458744261145484951919)
    ·
      refine ⟨65016688116391718227427879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43344458744261145484951919 65016688116391718227427879)
      ·
        refine ⟨97525032174587577341141819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65016688116391718227427879 97525032174587577341141819)
        ·
          refine ⟨146287548261881366011712729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97525032174587577341141819 146287548261881366011712729)
          ·
            refine ⟨109715661196411024508784547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146287548261881366011712729 109715661196411024508784547)
            ·
              refine ⟨164573491794616536763176821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109715661196411024508784547 164573491794616536763176821)
              ·
                refine ⟨15428764855745300321547827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164573491794616536763176821 15428764855745300321547827)
                ·
                  refine ⟨23143147283617950482321741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15428764855745300321547827 23143147283617950482321741)
                  ·
                    refine ⟨8678680231356731430870653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23143147283617950482321741 8678680231356731430870653)
                    ·
                      refine ⟨3254505086758774286576495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8678680231356731430870653 3254505086758774286576495)
                      ·
                        rfl

theorem cell23_6338126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_6338126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338126 prefixEnd_6338126 := by exact prefixLift 6338126
  have htrace : WordTrace (prefixWord ++ tailWord_6338126) baseStart_6338126 baseEnd_6338126 := by
    simpa [prefixWord, tailWord_6338126, baseEnd_6338126] using wordTrace_append hprefix tailTrace_6338126
  have hstable : (prefixWord ++ tailWord_6338126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338126).length < 2 ^ (prefixWord ++ tailWord_6338126).sum := by decide
  have hdescent : baseEnd_6338126 < baseStart_6338126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338130 : List Nat := [3, 2, 2, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_6338130 : Nat := 118140960795 + 6338130 * 2 ^ 59
def prefixEnd_6338130 : Nat := 4983230072969 + 3 ^ 40 * 6338130 * 2
def baseEnd_6338130 : Nat := 3254507140681392270926477

theorem tailTrace_6338130 : CollatzResearch.WordTrace tailWord_6338130 prefixEnd_6338130 3254507140681392270926477 := by
  unfold tailWord_6338130
  simp only [CollatzResearch.WordTrace]
  refine ⟨57792648132011237817388961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154113728352029967513037229 57792648132011237817388961)
  ·
    refine ⟨43344486099008428363041721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57792648132011237817388961 43344486099008428363041721)
    ·
      refine ⟨32508364574256321272281291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43344486099008428363041721 32508364574256321272281291)
      ·
        refine ⟨48762546861384481908421937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32508364574256321272281291 48762546861384481908421937)
        ·
          refine ⟨36571910146038361431316453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48762546861384481908421937 36571910146038361431316453)
          ·
            refine ⟨6857233152382192768371835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36571910146038361431316453 6857233152382192768371835)
            ·
              refine ⟨10285849728573289152557753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6857233152382192768371835 10285849728573289152557753)
              ·
                refine ⟨7714387296429966864418315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10285849728573289152557753 7714387296429966864418315)
                ·
                  refine ⟨11571580944644950296627473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7714387296429966864418315 11571580944644950296627473)
                  ·
                    refine ⟨8678685708483712722470605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11571580944644950296627473 8678685708483712722470605)
                    ·
                      refine ⟨3254507140681392270926477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8678685708483712722470605 3254507140681392270926477)
                      ·
                        rfl

theorem cell23_6338130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_6338130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338130 prefixEnd_6338130 := by exact prefixLift 6338130
  have htrace : WordTrace (prefixWord ++ tailWord_6338130) baseStart_6338130 baseEnd_6338130 := by
    simpa [prefixWord, tailWord_6338130, baseEnd_6338130] using wordTrace_append hprefix tailTrace_6338130
  have hstable : (prefixWord ++ tailWord_6338130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338130).length < 2 ^ (prefixWord ++ tailWord_6338130).sum := by decide
  have hdescent : baseEnd_6338130 < baseStart_6338130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338153 : List Nat := [1, 2, 1, 1, 1, 4, 2, 5, 1, 3, 2]
def baseStart_6338153 : Nat := 118140960795 + 6338153 * 2 ^ 59
def prefixEnd_6338153 : Nat := 4983230072969 + 3 ^ 40 * 6338153 * 2
def baseEnd_6338153 : Nat := 3254518950736445680938871

theorem tailTrace_6338153 : CollatzResearch.WordTrace tailWord_6338153 prefixEnd_6338153 3254518950736445680938871 := by
  unfold tailWord_6338153
  simp only [CollatzResearch.WordTrace]
  refine ⟨231171431406961626197643113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154114287604641084131762075 231171431406961626197643113)
  ·
    refine ⟨173378573555221219648232335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231171431406961626197643113 173378573555221219648232335)
    ·
      refine ⟨260067860332831829472348503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173378573555221219648232335 260067860332831829472348503)
      ·
        refine ⟨390101790499247744208522755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260067860332831829472348503 390101790499247744208522755)
        ·
          refine ⟨585152685748871616312784133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390101790499247744208522755 585152685748871616312784133)
          ·
            refine ⟨109716128577913428058647025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 585152685748871616312784133 109716128577913428058647025)
            ·
              refine ⟨82287096433435071043985269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109716128577913428058647025 82287096433435071043985269)
              ·
                refine ⟨7714415290634537910373619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82287096433435071043985269 7714415290634537910373619)
                ·
                  refine ⟨11571622935951806865560429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7714415290634537910373619 11571622935951806865560429)
                  ·
                    refine ⟨4339358600981927574585161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11571622935951806865560429 4339358600981927574585161)
                    ·
                      refine ⟨3254518950736445680938871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4339358600981927574585161 3254518950736445680938871)
                      ·
                        rfl

theorem cell23_6338153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 3, 2].length) (baseStart_6338153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338153 prefixEnd_6338153 := by exact prefixLift 6338153
  have htrace : WordTrace (prefixWord ++ tailWord_6338153) baseStart_6338153 baseEnd_6338153 := by
    simpa [prefixWord, tailWord_6338153, baseEnd_6338153] using wordTrace_append hprefix tailTrace_6338153
  have hstable : (prefixWord ++ tailWord_6338153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338153).length < 2 ^ (prefixWord ++ tailWord_6338153).sum := by decide
  have hdescent : baseEnd_6338153 < baseStart_6338153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338159 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 2, 6]
def baseStart_6338159 : Nat := 118140960795 + 6338159 * 2 ^ 59
def prefixEnd_6338159 : Nat := 4983230072969 + 3 ^ 40 * 6338159 * 2
def baseEnd_6338159 : Nat := 1084840677206790885821281

theorem tailTrace_6338159 : CollatzResearch.WordTrace tailWord_6338159 prefixEnd_6338159 1084840677206790885821281 := by
  unfold tailWord_6338159
  simp only [CollatzResearch.WordTrace]
  refine ⟨231171650244939889222361531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154114433496626592814907687 231171650244939889222361531)
  ·
    refine ⟨346757475367409833833542297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231171650244939889222361531 346757475367409833833542297)
    ·
      refine ⟨260068106525557375375156723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346757475367409833833542297 260068106525557375375156723)
      ·
        refine ⟨390102159788336063062735085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260068106525557375375156723 390102159788336063062735085)
        ·
          refine ⟨146288309920626023648525657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390102159788336063062735085 146288309920626023648525657)
          ·
            refine ⟨109716232440469517736394243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146288309920626023648525657 109716232440469517736394243)
            ·
              refine ⟨164574348660704276604591365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109716232440469517736394243 164574348660704276604591365)
              ·
                refine ⟨30857690373882051863360881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164574348660704276604591365 30857690373882051863360881)
                ·
                  refine ⟨23143267780411538897520661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30857690373882051863360881 23143267780411538897520661)
                  ·
                    refine ⟨1084840677206790885821281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23143267780411538897520661 1084840677206790885821281)
                    ·
                      rfl

theorem cell23_6338159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_6338159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338159 prefixEnd_6338159 := by exact prefixLift 6338159
  have htrace : WordTrace (prefixWord ++ tailWord_6338159) baseStart_6338159 baseEnd_6338159 := by
    simpa [prefixWord, tailWord_6338159, baseEnd_6338159] using wordTrace_append hprefix tailTrace_6338159
  have hstable : (prefixWord ++ tailWord_6338159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338159).length < 2 ^ (prefixWord ++ tailWord_6338159).sum := by decide
  have hdescent : baseEnd_6338159 < baseStart_6338159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338160 : List Nat := [2, 1, 1, 1, 6, 2, 2, 2, 2, 1, 3]
def baseStart_6338160 : Nat := 118140960795 + 6338160 * 2 ^ 59
def prefixEnd_6338160 : Nat := 4983230072969 + 3 ^ 40 * 6338160 * 2
def baseEnd_6338160 : Nat := 3254522545101027153551339

theorem tailTrace_6338160 : CollatzResearch.WordTrace tailWord_6338160 prefixEnd_6338160 3254522545101027153551339 := by
  unfold tailWord_6338160
  simp only [CollatzResearch.WordTrace]
  refine ⟨115585843358968133196573967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154114457811957510928765289 115585843358968133196573967)
  ·
    refine ⟨173378765038452199794860951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115585843358968133196573967 173378765038452199794860951)
    ·
      refine ⟨260068147557678299692291427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173378765038452199794860951 260068147557678299692291427)
      ·
        refine ⟨390102221336517449538437141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260068147557678299692291427 390102221336517449538437141)
        ·
          refine ⟨18286041625149255447114241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 390102221336517449538437141 18286041625149255447114241)
          ·
            refine ⟨13714531218861941585335681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18286041625149255447114241 13714531218861941585335681)
            ·
              refine ⟨10285898414146456189001761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13714531218861941585335681 10285898414146456189001761)
              ·
                refine ⟨7714423810609842141751321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10285898414146456189001761 7714423810609842141751321)
                ·
                  refine ⟨5785817857957381606313491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7714423810609842141751321 5785817857957381606313491)
                  ·
                    refine ⟨8678726786936072409470237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5785817857957381606313491 8678726786936072409470237)
                    ·
                      refine ⟨3254522545101027153551339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8678726786936072409470237 3254522545101027153551339)
                      ·
                        rfl

theorem cell23_6338160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 2, 1, 3].length) (baseStart_6338160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338160 prefixEnd_6338160 := by exact prefixLift 6338160
  have htrace : WordTrace (prefixWord ++ tailWord_6338160) baseStart_6338160 baseEnd_6338160 := by
    simpa [prefixWord, tailWord_6338160, baseEnd_6338160] using wordTrace_append hprefix tailTrace_6338160
  have hstable : (prefixWord ++ tailWord_6338160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338160).length < 2 ^ (prefixWord ++ tailWord_6338160).sum := by decide
  have hdescent : baseEnd_6338160 < baseStart_6338160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338183 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 1, 4, 2]
def baseStart_6338183 : Nat := 118140960795 + 6338183 * 2 ^ 59
def prefixEnd_6338183 : Nat := 4983230072969 + 3 ^ 40 * 6338183 * 2
def baseEnd_6338183 : Nat := 3254534355156080563563733

theorem tailTrace_6338183 : CollatzResearch.WordTrace tailWord_6338183 prefixEnd_6338183 3254534355156080563563733 := by
  unfold tailWord_6338183
  simp only [CollatzResearch.WordTrace]
  refine ⟨231172525596852941321235203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154115017064568627547490135 231172525596852941321235203)
  ·
    refine ⟨346758788395279411981852805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231172525596852941321235203 346758788395279411981852805)
    ·
      refine ⟨65017272824114889746597401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346758788395279411981852805 65017272824114889746597401)
      ·
        refine ⟨48762954618086167309948051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65017272824114889746597401 48762954618086167309948051)
        ·
          refine ⟨73144431927129250964922077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48762954618086167309948051 73144431927129250964922077)
          ·
            refine ⟨27429161972673469111845779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73144431927129250964922077 27429161972673469111845779)
            ·
              refine ⟨41143742959010203667768669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27429161972673469111845779 41143742959010203667768669)
              ·
                refine ⟨15428903609628826375413251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41143742959010203667768669 15428903609628826375413251)
                ·
                  refine ⟨23143355414443239563119877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15428903609628826375413251 23143355414443239563119877)
                  ·
                    refine ⟨4339379140208107418084977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23143355414443239563119877 4339379140208107418084977)
                    ·
                      refine ⟨3254534355156080563563733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4339379140208107418084977 3254534355156080563563733)
                      ·
                        rfl

theorem cell23_6338183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_6338183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338183 prefixEnd_6338183 := by exact prefixLift 6338183
  have htrace : WordTrace (prefixWord ++ tailWord_6338183) baseStart_6338183 baseEnd_6338183 := by
    simpa [prefixWord, tailWord_6338183, baseEnd_6338183] using wordTrace_append hprefix tailTrace_6338183
  have hstable : (prefixWord ++ tailWord_6338183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338183).length < 2 ^ (prefixWord ++ tailWord_6338183).sum := by decide
  have hdescent : baseEnd_6338183 < baseStart_6338183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338204 : List Nat := [2, 2, 3, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_6338204 : Nat := 118140960795 + 6338204 * 2 ^ 59
def prefixEnd_6338204 : Nat := 4983230072969 + 3 ^ 40 * 6338204 * 2
def baseEnd_6338204 : Nat := 3254545138249824981401137

theorem tailTrace_6338204 : CollatzResearch.WordTrace tailWord_6338204 prefixEnd_6338204 3254545138249824981401137 := by
  unfold tailWord_6338204
  simp only [CollatzResearch.WordTrace]
  refine ⟨115586645764888430953874833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154115527686517907938499777 115586645764888430953874833)
  ·
    refine ⟨86689984323666323215406125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115586645764888430953874833 86689984323666323215406125)
    ·
      refine ⟨32508744121374871205777297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86689984323666323215406125 32508744121374871205777297)
      ·
        refine ⟨24381558091031153404332973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32508744121374871205777297 24381558091031153404332973)
        ·
          refine ⟨9143084284136682526624865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24381558091031153404332973 9143084284136682526624865)
          ·
            refine ⟨6857313213102511894968649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9143084284136682526624865 6857313213102511894968649)
            ·
              refine ⟨5142984909826883921226487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6857313213102511894968649 5142984909826883921226487)
              ·
                refine ⟨7714477364740325881839731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142984909826883921226487 7714477364740325881839731)
                ·
                  refine ⟨11571716047110488822759597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7714477364740325881839731 11571716047110488822759597)
                  ·
                    refine ⟨4339393517666433308534849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11571716047110488822759597 4339393517666433308534849)
                    ·
                      refine ⟨3254545138249824981401137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4339393517666433308534849 3254545138249824981401137)
                      ·
                        rfl

theorem cell23_6338204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_6338204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338204 prefixEnd_6338204 := by exact prefixLift 6338204
  have htrace : WordTrace (prefixWord ++ tailWord_6338204) baseStart_6338204 baseEnd_6338204 := by
    simpa [prefixWord, tailWord_6338204, baseEnd_6338204] using wordTrace_append hprefix tailTrace_6338204
  have hstable : (prefixWord ++ tailWord_6338204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338204).length < 2 ^ (prefixWord ++ tailWord_6338204).sum := by decide
  have hdescent : baseEnd_6338204 < baseStart_6338204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338230 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_6338230 : Nat := 118140960795 + 6338230 * 2 ^ 59
def prefixEnd_6338230 : Nat := 4983230072969 + 3 ^ 40 * 6338230 * 2
def baseEnd_6338230 : Nat := 3254558488746841879676017

theorem tailTrace_6338230 : CollatzResearch.WordTrace tailWord_6338230 prefixEnd_6338230 3254558488746841879676017 := by
  unfold tailWord_6338230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14448389989230166771762259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154116159885121778898797429 14448389989230166771762259)
  ·
    refine ⟨21672584983845250157643389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14448389989230166771762259 21672584983845250157643389)
    ·
      refine ⟨8127219368941968809116271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21672584983845250157643389 8127219368941968809116271)
      ·
        refine ⟨12190829053412953213674407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8127219368941968809116271 12190829053412953213674407)
        ·
          refine ⟨18286243580119429820511611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12190829053412953213674407 18286243580119429820511611)
          ·
            refine ⟨27429365370179144730767417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18286243580119429820511611 27429365370179144730767417)
            ·
              refine ⟨20572024027634358548075563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27429365370179144730767417 20572024027634358548075563)
              ·
                refine ⟨30858036041451537822113345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20572024027634358548075563 30858036041451537822113345)
                ·
                  refine ⟨23143527031088653366585009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30858036041451537822113345 23143527031088653366585009)
                  ·
                    refine ⟨17357645273316490024938757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23143527031088653366585009 17357645273316490024938757)
                    ·
                      refine ⟨3254558488746841879676017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17357645273316490024938757 3254558488746841879676017)
                      ·
                        rfl

theorem cell23_6338230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_6338230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338230 prefixEnd_6338230 := by exact prefixLift 6338230
  have htrace : WordTrace (prefixWord ++ tailWord_6338230) baseStart_6338230 baseEnd_6338230 := by
    simpa [prefixWord, tailWord_6338230, baseEnd_6338230] using wordTrace_append hprefix tailTrace_6338230
  have hstable : (prefixWord ++ tailWord_6338230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338230).length < 2 ^ (prefixWord ++ tailWord_6338230).sum := by decide
  have hdescent : baseEnd_6338230 < baseStart_6338230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338236 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 1, 7]
def baseStart_6338236 : Nat := 118140960795 + 6338236 * 2 ^ 59
def prefixEnd_6338236 : Nat := 4983230072969 + 3 ^ 40 * 6338236 * 2
def baseEnd_6338236 : Nat := 1084853856543589618733663

theorem tailTrace_6338236 : CollatzResearch.WordTrace tailWord_6338236 prefixEnd_6338236 1084853856543589618733663 := by
  unfold tailWord_6338236
  simp only [CollatzResearch.WordTrace]
  refine ⟨115587229332830465686457281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154116305777107287581943041 115587229332830465686457281)
  ·
    refine ⟨86690421999622849264842961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115587229332830465686457281 86690421999622849264842961)
    ·
      refine ⟨65017816499717136948632221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86690421999622849264842961 65017816499717136948632221)
      ·
        refine ⟨24381681187393926355737083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65017816499717136948632221 24381681187393926355737083)
        ·
          refine ⟨36572521781090889533605625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24381681187393926355737083 36572521781090889533605625)
          ·
            refine ⟨27429391335818167150204219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36572521781090889533605625 27429391335818167150204219)
            ·
              refine ⟨41144087003727250725306329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27429391335818167150204219 41144087003727250725306329)
              ·
                refine ⟨30858065252795438043979747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41144087003727250725306329 30858065252795438043979747)
                ·
                  refine ⟨46287097879193157065969621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30858065252795438043979747 46287097879193157065969621)
                  ·
                    refine ⟨1084853856543589618733663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46287097879193157065969621 1084853856543589618733663)
                    ·
                      rfl

theorem cell23_6338236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_6338236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338236 prefixEnd_6338236 := by exact prefixLift 6338236
  have htrace : WordTrace (prefixWord ++ tailWord_6338236) baseStart_6338236 baseEnd_6338236 := by
    simpa [prefixWord, tailWord_6338236, baseEnd_6338236] using wordTrace_append hprefix tailTrace_6338236
  have hstable : (prefixWord ++ tailWord_6338236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338236).length < 2 ^ (prefixWord ++ tailWord_6338236).sum := by decide
  have hdescent : baseEnd_6338236 < baseStart_6338236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338283 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 3, 4]
def baseStart_6338283 : Nat := 118140960795 + 6338283 * 2 ^ 59
def prefixEnd_6338283 : Nat := 4983230072969 + 3 ^ 40 * 6338283 * 2
def baseEnd_6338283 : Nat := 1084861901073843390771091

theorem tailTrace_6338283 : CollatzResearch.WordTrace tailWord_6338283 prefixEnd_6338283 1084861901073843390771091 := by
  unfold tailWord_6338283
  simp only [CollatzResearch.WordTrace]
  refine ⟨231176172896490658399875503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154117448597660438933250335 231176172896490658399875503)
  ·
    refine ⟨346764259344735987599813255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231176172896490658399875503 346764259344735987599813255)
    ·
      refine ⟨520146389017103981399719883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346764259344735987599813255 520146389017103981399719883)
      ·
        refine ⟨780219583525655972099579825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520146389017103981399719883 780219583525655972099579825)
        ·
          refine ⟨585164687644241979074684869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780219583525655972099579825 585164687644241979074684869)
          ·
            refine ⟨109718378933295371076503413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 585164687644241979074684869 109718378933295371076503413)
            ·
              refine ⟨10286098024996441038422195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109718378933295371076503413 10286098024996441038422195)
              ·
                refine ⟨15429147037494661557633293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10286098024996441038422195 15429147037494661557633293)
                ·
                  refine ⟨5785930139060498084112485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15429147037494661557633293 5785930139060498084112485)
                  ·
                    refine ⟨1084861901073843390771091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5785930139060498084112485 1084861901073843390771091)
                    ·
                      rfl

theorem cell23_6338283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 4].length) (baseStart_6338283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338283 prefixEnd_6338283 := by exact prefixLift 6338283
  have htrace : WordTrace (prefixWord ++ tailWord_6338283) baseStart_6338283 baseEnd_6338283 := by
    simpa [prefixWord, tailWord_6338283, baseEnd_6338283] using wordTrace_append hprefix tailTrace_6338283
  have hstable : (prefixWord ++ tailWord_6338283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338283).length < 2 ^ (prefixWord ++ tailWord_6338283).sum := by decide
  have hdescent : baseEnd_6338283 < baseStart_6338283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338323 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 7, 1, 3]
def baseStart_6338323 : Nat := 118140960795 + 6338323 * 2 ^ 59
def prefixEnd_6338323 : Nat := 4983230072969 + 3 ^ 40 * 6338323 * 2
def baseEnd_6338323 : Nat := 3254606242447710015813089

theorem tailTrace_6338323 : CollatzResearch.WordTrace tailWord_6338323 prefixEnd_6338323 3254606242447710015813089 := by
  unfold tailWord_6338323
  simp only [CollatzResearch.WordTrace]
  refine ⟨231177631816345745231331623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154118421210897163487554415 231177631816345745231331623)
  ·
    refine ⟨346766447724518617846997435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231177631816345745231331623 346766447724518617846997435)
    ·
      refine ⟨520149671586777926770496153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346766447724518617846997435 520149671586777926770496153)
      ·
        refine ⟨390112253690083445077872115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520149671586777926770496153 390112253690083445077872115)
        ·
          refine ⟨585168380535125167616808173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390112253690083445077872115 585168380535125167616808173)
          ·
            refine ⟨219438142700671937856303065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 585168380535125167616808173 219438142700671937856303065)
            ·
              refine ⟨164578607025503953392227299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219438142700671937856303065 164578607025503953392227299)
              ·
                refine ⟨246867910538255930088340949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164578607025503953392227299 246867910538255930088340949)
                ·
                  refine ⟨5785966653240373361445491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 246867910538255930088340949 5785966653240373361445491)
                  ·
                    refine ⟨8678949979860560042168237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5785966653240373361445491 8678949979860560042168237)
                    ·
                      refine ⟨3254606242447710015813089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8678949979860560042168237 3254606242447710015813089)
                      ·
                        rfl

theorem cell23_6338323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 1, 3].length) (baseStart_6338323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338323 prefixEnd_6338323 := by exact prefixLift 6338323
  have htrace : WordTrace (prefixWord ++ tailWord_6338323) baseStart_6338323 baseEnd_6338323 := by
    simpa [prefixWord, tailWord_6338323, baseEnd_6338323] using wordTrace_append hprefix tailTrace_6338323
  have hstable : (prefixWord ++ tailWord_6338323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338323).length < 2 ^ (prefixWord ++ tailWord_6338323).sum := by decide
  have hdescent : baseEnd_6338323 < baseStart_6338323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338357 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_6338357 : Nat := 118140960795 + 6338357 * 2 ^ 59
def prefixEnd_6338357 : Nat := 4983230072969 + 3 ^ 40 * 6338357 * 2
def baseEnd_6338357 : Nat := 3254623700789962882787933

theorem tailTrace_6338357 : CollatzResearch.WordTrace tailWord_6338357 prefixEnd_6338357 3254623700789962882787933 := by
  unfold tailWord_6338357
  simp only [CollatzResearch.WordTrace]
  refine ⟨231178871898222569038069325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154119247932148379358712883 231178871898222569038069325)
  ·
    refine ⟨86692076961833463389275997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231178871898222569038069325 86692076961833463389275997)
    ·
      refine ⟨32509528860687548770978499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86692076961833463389275997 32509528860687548770978499)
      ·
        refine ⟨48764293291031323156467749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32509528860687548770978499 48764293291031323156467749)
        ·
          refine ⟨9143304992068373091837703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48764293291031323156467749 9143304992068373091837703)
          ·
            refine ⟨13714957488102559637756555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9143304992068373091837703 13714957488102559637756555)
            ·
              refine ⟨20572436232153839456634833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13714957488102559637756555 20572436232153839456634833)
              ·
                refine ⟨15429327174115379592476125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20572436232153839456634833 15429327174115379592476125)
                ·
                  refine ⟨5785997690293267347178547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15429327174115379592476125 5785997690293267347178547)
                  ·
                    refine ⟨8678996535439901020767821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5785997690293267347178547 8678996535439901020767821)
                    ·
                      refine ⟨3254623700789962882787933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8678996535439901020767821 3254623700789962882787933)
                      ·
                        rfl

theorem cell23_6338357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_6338357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338357 prefixEnd_6338357 := by exact prefixLift 6338357
  have htrace : WordTrace (prefixWord ++ tailWord_6338357) baseStart_6338357 baseEnd_6338357 := by
    simpa [prefixWord, tailWord_6338357, baseEnd_6338357] using wordTrace_append hprefix tailTrace_6338357
  have hstable : (prefixWord ++ tailWord_6338357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338357).length < 2 ^ (prefixWord ++ tailWord_6338357).sum := by decide
  have hdescent : baseEnd_6338357 < baseStart_6338357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338373 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 4, 4]
def baseStart_6338373 : Nat := 118140960795 + 6338373 * 2 ^ 59
def prefixEnd_6338373 : Nat := 4983230072969 + 3 ^ 40 * 6338373 * 2
def baseEnd_6338373 : Nat := 1084877305493478273395953

theorem tailTrace_6338373 : CollatzResearch.WordTrace tailWord_6338373 prefixEnd_6338373 1084877305493478273395953 := by
  unfold tailWord_6338373
  simp only [CollatzResearch.WordTrace]
  refine ⟨231179455466164603770651773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154119636977443069180434515 231179455466164603770651773)
  ·
    refine ⟨86692295799811726413994415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231179455466164603770651773 86692295799811726413994415)
    ·
      refine ⟨130038443699717589620991623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86692295799811726413994415 130038443699717589620991623)
      ·
        refine ⟨195057665549576384431487435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130038443699717589620991623 195057665549576384431487435)
        ·
          refine ⟨292586498324364576647231153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195057665549576384431487435 292586498324364576647231153)
          ·
            refine ⟨219439873743273432485423365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292586498324364576647231153 219439873743273432485423365)
            ·
              refine ⟨41144976326863768591016881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 219439873743273432485423365 41144976326863768591016881)
              ·
                refine ⟨30858732245147826443262661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41144976326863768591016881 30858732245147826443262661)
                ·
                  refine ⟨5786012295965217458111749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30858732245147826443262661 5786012295965217458111749)
                  ·
                    refine ⟨1084877305493478273395953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5786012295965217458111749 1084877305493478273395953)
                    ·
                      rfl

theorem cell23_6338373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_6338373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338373 prefixEnd_6338373 := by exact prefixLift 6338373
  have htrace : WordTrace (prefixWord ++ tailWord_6338373) baseStart_6338373 baseEnd_6338373 := by
    simpa [prefixWord, tailWord_6338373, baseEnd_6338373] using wordTrace_append hprefix tailTrace_6338373
  have hstable : (prefixWord ++ tailWord_6338373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338373).length < 2 ^ (prefixWord ++ tailWord_6338373).sum := by decide
  have hdescent : baseEnd_6338373 < baseStart_6338373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338407 : List Nat := [1, 1, 5, 1, 2, 1, 5, 1, 2, 4]
def baseStart_6338407 : Nat := 118140960795 + 6338407 * 2 ^ 59
def prefixEnd_6338407 : Nat := 4983230072969 + 3 ^ 40 * 6338407 * 2
def baseEnd_6338407 : Nat := 1084883124940895895720901

theorem tailTrace_6338407 : CollatzResearch.WordTrace tailWord_6338407 prefixEnd_6338407 1084883124940895895720901 := by
  unfold tailWord_6338407
  simp only [CollatzResearch.WordTrace]
  refine ⟨231180695548041427577389475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154120463698694285051592983 231180695548041427577389475)
  ·
    refine ⟨346771043322062141366084213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231180695548041427577389475 346771043322062141366084213)
    ·
      refine ⟨32509785311443325753070395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 346771043322062141366084213 32509785311443325753070395)
      ·
        refine ⟨48764677967164988629605593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32509785311443325753070395 48764677967164988629605593)
        ·
          refine ⟨36573508475373741472204195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48764677967164988629605593 36573508475373741472204195)
          ·
            refine ⟨54860262713060612208306293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36573508475373741472204195 54860262713060612208306293)
            ·
              refine ⟨5143149629349432394528715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54860262713060612208306293 5143149629349432394528715)
              ·
                refine ⟨7714724444024148591793073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5143149629349432394528715 7714724444024148591793073)
                ·
                  refine ⟨5786043333018111443844805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7714724444024148591793073 5786043333018111443844805)
                  ·
                    refine ⟨1084883124940895895720901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5786043333018111443844805 1084883124940895895720901)
                    ·
                      rfl

theorem cell23_6338407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_6338407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338407 prefixEnd_6338407 := by exact prefixLift 6338407
  have htrace : WordTrace (prefixWord ++ tailWord_6338407) baseStart_6338407 baseEnd_6338407 := by
    simpa [prefixWord, tailWord_6338407, baseEnd_6338407] using wordTrace_append hprefix tailTrace_6338407
  have hstable : (prefixWord ++ tailWord_6338407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338407).length < 2 ^ (prefixWord ++ tailWord_6338407).sum := by decide
  have hdescent : baseEnd_6338407 < baseStart_6338407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338414 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_6338414 : Nat := 118140960795 + 6338414 * 2 ^ 59
def prefixEnd_6338414 : Nat := 4983230072969 + 3 ^ 40 * 6338414 * 2
def baseEnd_6338414 : Nat := 3254652969187269159775171

theorem tailTrace_6338414 : CollatzResearch.WordTrace tailWord_6338414 prefixEnd_6338414 3254652969187269159775171 := by
  unfold tailWord_6338414
  simp only [CollatzResearch.WordTrace]
  refine ⟨28897618857377008471611787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154120633906010711848596197 28897618857377008471611787)
  ·
    refine ⟨43346428286065512707417681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28897618857377008471611787 43346428286065512707417681)
    ·
      refine ⟨32509821214549134530563261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43346428286065512707417681 32509821214549134530563261)
      ·
        refine ⟨12191182955455925448961223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32509821214549134530563261 12191182955455925448961223)
        ·
          refine ⟨18286774433183888173441835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12191182955455925448961223 18286774433183888173441835)
          ·
            refine ⟨27430161649775832260162753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18286774433183888173441835 27430161649775832260162753)
            ·
              refine ⟨20572621237331874195122065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27430161649775832260162753 20572621237331874195122065)
              ·
                refine ⟨15429465927998905646341549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20572621237331874195122065 15429465927998905646341549)
                ·
                  refine ⟨5786049722999589617378081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15429465927998905646341549 5786049722999589617378081)
                  ·
                    refine ⟨4339537292249692213033561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5786049722999589617378081 4339537292249692213033561)
                    ·
                      refine ⟨3254652969187269159775171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4339537292249692213033561 3254652969187269159775171)
                      ·
                        rfl

theorem cell23_6338414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_6338414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338414 prefixEnd_6338414 := by exact prefixLift 6338414
  have htrace : WordTrace (prefixWord ++ tailWord_6338414) baseStart_6338414 baseEnd_6338414 := by
    simpa [prefixWord, tailWord_6338414, baseEnd_6338414] using wordTrace_append hprefix tailTrace_6338414
  have hstable : (prefixWord ++ tailWord_6338414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338414).length < 2 ^ (prefixWord ++ tailWord_6338414).sum := by decide
  have hdescent : baseEnd_6338414 < baseStart_6338414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338453 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_6338453 : Nat := 118140960795 + 6338453 * 2 ^ 59
def prefixEnd_6338453 : Nat := 4983230072969 + 3 ^ 40 * 6338453 * 2
def baseEnd_6338453 : Nat := 3254672994932794507187491

theorem tailTrace_6338453 : CollatzResearch.WordTrace tailWord_6338453 prefixEnd_6338453 3254672994932794507187491 := by
  unfold tailWord_6338453
  simp only [CollatzResearch.WordTrace]
  refine ⟨231182373305874777433564013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154121582203916518289042675 231182373305874777433564013)
  ·
    refine ⟨86693389989703041537586505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231182373305874777433564013 86693389989703041537586505)
    ·
      refine ⟨65020042492277281153189879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86693389989703041537586505 65020042492277281153189879)
      ·
        refine ⟨97530063738415921729784819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65020042492277281153189879 97530063738415921729784819)
        ·
          refine ⟨146295095607623882594677229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97530063738415921729784819 146295095607623882594677229)
          ·
            refine ⟨54860660852858955973003961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146295095607623882594677229 54860660852858955973003961)
            ·
              refine ⟨41145495639644216979752971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54860660852858955973003961 41145495639644216979752971)
              ·
                refine ⟨61718243459466325469629457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41145495639644216979752971 61718243459466325469629457)
                ·
                  refine ⟨46288682594599744102222093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61718243459466325469629457 46288682594599744102222093)
                  ·
                    refine ⟨17358255972974904038333285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46288682594599744102222093 17358255972974904038333285)
                    ·
                      refine ⟨3254672994932794507187491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17358255972974904038333285 3254672994932794507187491)
                      ·
                        rfl

theorem cell23_6338453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_6338453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338453 prefixEnd_6338453 := by exact prefixLift 6338453
  have htrace : WordTrace (prefixWord ++ tailWord_6338453) baseStart_6338453 baseEnd_6338453 := by
    simpa [prefixWord, tailWord_6338453, baseEnd_6338453] using wordTrace_append hprefix tailTrace_6338453
  have hstable : (prefixWord ++ tailWord_6338453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338453).length < 2 ^ (prefixWord ++ tailWord_6338453).sum := by decide
  have hdescent : baseEnd_6338453 < baseStart_6338453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338454 : List Nat := [5, 3, 1, 1, 2, 1, 2, 8]
def baseStart_6338454 : Nat := 118140960795 + 6338454 * 2 ^ 59
def prefixEnd_6338454 : Nat := 4983230072969 + 3 ^ 40 * 6338454 * 2
def baseEnd_6338454 : Nat := 120543463274572185306481

theorem tailTrace_6338454 : CollatzResearch.WordTrace tailWord_6338454 prefixEnd_6338454 120543463274572185306481 := by
  unfold tailWord_6338454
  simp only [CollatzResearch.WordTrace]
  refine ⟨14448900611179447162771901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154121606519247436402900277 14448900611179447162771901)
  ·
    refine ⟨5418337729192292686039463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14448900611179447162771901 5418337729192292686039463)
    ·
      refine ⟨8127506593788439029059195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5418337729192292686039463 8127506593788439029059195)
      ·
        refine ⟨12191259890682658543588793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8127506593788439029059195 12191259890682658543588793)
        ·
          refine ⟨9143444918011993907691595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12191259890682658543588793 9143444918011993907691595)
          ·
            refine ⟨13715167377017990861537393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9143444918011993907691595 13715167377017990861537393)
            ·
              refine ⟨10286375532763493146153045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13715167377017990861537393 10286375532763493146153045)
              ·
                refine ⟨120543463274572185306481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10286375532763493146153045 120543463274572185306481)
                ·
                  rfl

theorem cell23_6338454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_6338454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338454 prefixEnd_6338454 := by exact prefixLift 6338454
  have htrace : WordTrace (prefixWord ++ tailWord_6338454) baseStart_6338454 baseEnd_6338454 := by
    simpa [prefixWord, tailWord_6338454, baseEnd_6338454] using wordTrace_append hprefix tailTrace_6338454
  have hstable : (prefixWord ++ tailWord_6338454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338454).length < 2 ^ (prefixWord ++ tailWord_6338454).sum := by decide
  have hdescent : baseEnd_6338454 < baseStart_6338454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338473 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 4, 4, 3]
def baseStart_6338473 : Nat := 118140960795 + 6338473 * 2 ^ 59
def prefixEnd_6338473 : Nat := 4983230072969 + 3 ^ 40 * 6338473 * 2
def baseEnd_6338473 : Nat := 3254683264545884428937399

theorem tailTrace_6338473 : CollatzResearch.WordTrace tailWord_6338473 prefixEnd_6338473 3254683264545884428937399 := by
  unfold tailWord_6338473
  simp only [CollatzResearch.WordTrace]
  refine ⟨231183102765802320849292073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154122068510534880566194715 231183102765802320849292073)
  ·
    refine ⟨173387327074351740636969055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231183102765802320849292073 173387327074351740636969055)
    ·
      refine ⟨260080990611527610955453583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173387327074351740636969055 260080990611527610955453583)
      ·
        refine ⟨390121485917291416433180375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260080990611527610955453583 390121485917291416433180375)
        ·
          refine ⟨585182228875937124649770563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390121485917291416433180375 585182228875937124649770563)
          ·
            refine ⟨877773343313905686974655845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585182228875937124649770563 877773343313905686974655845)
            ·
              refine ⟨164582501871357316307747971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 877773343313905686974655845 164582501871357316307747971)
              ·
                refine ⟨246873752807035974461621957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164582501871357316307747971 246873752807035974461621957)
                ·
                  refine ⟨46288828651319245211554117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246873752807035974461621957 46288828651319245211554117)
                  ·
                    refine ⟨8679155372122358477166397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46288828651319245211554117 8679155372122358477166397)
                    ·
                      refine ⟨3254683264545884428937399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8679155372122358477166397 3254683264545884428937399)
                      ·
                        rfl

theorem cell23_6338473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 4, 3].length) (baseStart_6338473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338473 prefixEnd_6338473 := by exact prefixLift 6338473
  have htrace : WordTrace (prefixWord ++ tailWord_6338473) baseStart_6338473 baseEnd_6338473 := by
    simpa [prefixWord, tailWord_6338473, baseEnd_6338473] using wordTrace_append hprefix tailTrace_6338473
  have hstable : (prefixWord ++ tailWord_6338473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338473).length < 2 ^ (prefixWord ++ tailWord_6338473).sum := by decide
  have hdescent : baseEnd_6338473 < baseStart_6338473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338504 : List Nat := [2, 1, 3, 1, 4, 1, 1, 4, 2, 2, 2]
def baseStart_6338504 : Nat := 118140960795 + 6338504 * 2 ^ 59
def prefixEnd_6338504 : Nat := 4983230072969 + 3 ^ 40 * 6338504 * 2
def baseEnd_6338504 : Nat := 3254699182446173807649757

theorem tailTrace_6338504 : CollatzResearch.WordTrace tailWord_6338504 prefixEnd_6338504 3254699182446173807649757 := by
  unfold tailWord_6338504
  simp only [CollatzResearch.WordTrace]
  refine ⟨115592116714345006571835283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154122822285793342095780377 115592116714345006571835283)
  ·
    refine ⟨173388175071517509857752925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115592116714345006571835283 173388175071517509857752925)
    ·
      refine ⟨65020565651819066196657347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173388175071517509857752925 65020565651819066196657347)
      ·
        refine ⟨97530848477728599294986021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65020565651819066196657347 97530848477728599294986021)
        ·
          refine ⟨18287034089574112367809879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97530848477728599294986021 18287034089574112367809879)
          ·
            refine ⟨27430551134361168551714819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18287034089574112367809879 27430551134361168551714819)
            ·
              refine ⟨41145826701541752827572229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27430551134361168551714819 41145826701541752827572229)
              ·
                refine ⟨7714842506539078655169793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41145826701541752827572229 7714842506539078655169793)
                ·
                  refine ⟨5786131879904308991377345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7714842506539078655169793 5786131879904308991377345)
                  ·
                    refine ⟨4339598909928231743533009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5786131879904308991377345 4339598909928231743533009)
                    ·
                      refine ⟨3254699182446173807649757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4339598909928231743533009 3254699182446173807649757)
                      ·
                        rfl

theorem cell23_6338504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_6338504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338504 prefixEnd_6338504 := by exact prefixLift 6338504
  have htrace : WordTrace (prefixWord ++ tailWord_6338504) baseStart_6338504 baseEnd_6338504 := by
    simpa [prefixWord, tailWord_6338504, baseEnd_6338504] using wordTrace_append hprefix tailTrace_6338504
  have hstable : (prefixWord ++ tailWord_6338504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338504).length < 2 ^ (prefixWord ++ tailWord_6338504).sum := by decide
  have hdescent : baseEnd_6338504 < baseStart_6338504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338520 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 2, 3, 3]
def baseStart_6338520 : Nat := 118140960795 + 6338520 * 2 ^ 59
def prefixEnd_6338520 : Nat := 4983230072969 + 3 ^ 40 * 6338520 * 2
def baseEnd_6338520 : Nat := 3254707398136645745049683

theorem tailTrace_6338520 : CollatzResearch.WordTrace tailWord_6338520 prefixEnd_6338520 3254707398136645745049683 := by
  unfold tailWord_6338520
  simp only [CollatzResearch.WordTrace]
  refine ⟨115592408498316023938126507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154123211331088031917502009 115592408498316023938126507)
  ·
    refine ⟨173388612747474035907189761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115592408498316023938126507 173388612747474035907189761)
    ·
      refine ⟨130041459560605526930392321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173388612747474035907189761 130041459560605526930392321)
      ·
        refine ⟨97531094670454145197794241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130041459560605526930392321 97531094670454145197794241)
        ·
          refine ⟨73148321002840608898345681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97531094670454145197794241 73148321002840608898345681)
          ·
            refine ⟨54861240752130456673759261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73148321002840608898345681 54861240752130456673759261)
            ·
              refine ⟨20572965282048921252659723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54861240752130456673759261 20572965282048921252659723)
              ·
                refine ⟨30859447923073381878989585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20572965282048921252659723 30859447923073381878989585)
                ·
                  refine ⟨23144585942305036409242189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30859447923073381878989585 23144585942305036409242189)
                  ·
                    refine ⟨8679219728364388653465821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23144585942305036409242189 8679219728364388653465821)
                    ·
                      refine ⟨3254707398136645745049683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8679219728364388653465821 3254707398136645745049683)
                      ·
                        rfl

theorem cell23_6338520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_6338520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338520 prefixEnd_6338520 := by exact prefixLift 6338520
  have htrace : WordTrace (prefixWord ++ tailWord_6338520) baseStart_6338520 baseEnd_6338520 := by
    simpa [prefixWord, tailWord_6338520, baseEnd_6338520] using wordTrace_append hprefix tailTrace_6338520
  have hstable : (prefixWord ++ tailWord_6338520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338520).length < 2 ^ (prefixWord ++ tailWord_6338520).sum := by decide
  have hdescent : baseEnd_6338520 < baseStart_6338520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338563 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 5]
def baseStart_6338563 : Nat := 118140960795 + 6338563 * 2 ^ 59
def prefixEnd_6338563 : Nat := 4983230072969 + 3 ^ 40 * 6338563 * 2
def baseEnd_6338563 : Nat := 3254729477804789076811985

theorem tailTrace_6338563 : CollatzResearch.WordTrace tailWord_6338563 prefixEnd_6338563 3254729477804789076811985 := by
  unfold tailWord_6338563
  simp only [CollatzResearch.WordTrace]
  refine ⟨231186385335476266220068343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154124256890317510813378895 231186385335476266220068343)
  ·
    refine ⟨346779578003214399330102515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231186385335476266220068343 346779578003214399330102515)
    ·
      refine ⟨520169367004821598995153773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346779578003214399330102515 520169367004821598995153773)
      ·
        refine ⟨195063512626808099623182665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 520169367004821598995153773 195063512626808099623182665)
        ·
          refine ⟨146297634470106074717386999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195063512626808099623182665 146297634470106074717386999)
          ·
            refine ⟨219446451705159112076080499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146297634470106074717386999 219446451705159112076080499)
            ·
              refine ⟨329169677557738668114120749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219446451705159112076080499 329169677557738668114120749)
              ·
                refine ⟨123438629084152000542795281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329169677557738668114120749 123438629084152000542795281)
                ·
                  refine ⟨92578971813114000407096461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123438629084152000542795281 92578971813114000407096461)
                  ·
                    refine ⟨34717114429917750152661173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92578971813114000407096461 34717114429917750152661173)
                    ·
                      refine ⟨3254729477804789076811985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34717114429917750152661173 3254729477804789076811985)
                      ·
                        rfl

theorem cell23_6338563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_6338563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338563 prefixEnd_6338563 := by exact prefixLift 6338563
  have htrace : WordTrace (prefixWord ++ tailWord_6338563) baseStart_6338563 baseEnd_6338563 := by
    simpa [prefixWord, tailWord_6338563, baseEnd_6338563] using wordTrace_append hprefix tailTrace_6338563
  have hstable : (prefixWord ++ tailWord_6338563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338563).length < 2 ^ (prefixWord ++ tailWord_6338563).sum := by decide
  have hdescent : baseEnd_6338563 < baseStart_6338563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338603 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 8]
def baseStart_6338603 : Nat := 118140960795 + 6338603 * 2 ^ 59
def prefixEnd_6338603 : Nat := 4983230072969 + 3 ^ 40 * 6338603 * 2
def baseEnd_6338603 : Nat := 3254750017030968920311801

theorem tailTrace_6338603 : CollatzResearch.WordTrace tailWord_6338603 prefixEnd_6338603 3254750017030968920311801 := by
  unfold tailWord_6338603
  simp only [CollatzResearch.WordTrace]
  refine ⟨231187844255331353051524463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154125229503554235367682975 231187844255331353051524463)
  ·
    refine ⟨346781766382997029577286695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231187844255331353051524463 346781766382997029577286695)
    ·
      refine ⟨520172649574495544365930043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346781766382997029577286695 520172649574495544365930043)
      ·
        refine ⟨780258974361743316548895065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520172649574495544365930043 780258974361743316548895065)
        ·
          refine ⟨585194230771307487411671299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780258974361743316548895065 585194230771307487411671299)
          ·
            refine ⟨877791346156961231117506949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585194230771307487411671299 877791346156961231117506949)
            ·
              refine ⟨164585877404430230834532553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 877791346156961231117506949 164585877404430230834532553)
              ·
                refine ⟨123439408053322673125899415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164585877404430230834532553 123439408053322673125899415)
                ·
                  refine ⟨185159112079984009688849123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123439408053322673125899415 185159112079984009688849123)
                  ·
                    refine ⟨277738668119976014533273685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 185159112079984009688849123 277738668119976014533273685)
                    ·
                      refine ⟨3254750017030968920311801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 277738668119976014533273685 3254750017030968920311801)
                      ·
                        rfl

theorem cell23_6338603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_6338603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338603 prefixEnd_6338603 := by exact prefixLift 6338603
  have htrace : WordTrace (prefixWord ++ tailWord_6338603) baseStart_6338603 baseEnd_6338603 := by
    simpa [prefixWord, tailWord_6338603, baseEnd_6338603] using wordTrace_append hprefix tailTrace_6338603
  have hstable : (prefixWord ++ tailWord_6338603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338603).length < 2 ^ (prefixWord ++ tailWord_6338603).sum := by decide
  have hdescent : baseEnd_6338603 < baseStart_6338603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338614 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_6338614 : Nat := 118140960795 + 6338614 * 2 ^ 59
def prefixEnd_6338614 : Nat := 4983230072969 + 3 ^ 40 * 6338614 * 2
def baseEnd_6338614 : Nat := 3254755665318168377274251

theorem tailTrace_6338614 : CollatzResearch.WordTrace tailWord_6338614 prefixEnd_6338614 3254755665318168377274251 := by
  unfold tailWord_6338614
  simp only [CollatzResearch.WordTrace]
  refine ⟨14449265341143218870635931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154125496972194334620116597 14449265341143218870635931)
  ·
    refine ⟨21673898011714828305953897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14449265341143218870635931 21673898011714828305953897)
    ·
      refine ⟨16255423508786121229465423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21673898011714828305953897 16255423508786121229465423)
      ·
        refine ⟨24383135263179181844198135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16255423508786121229465423 24383135263179181844198135)
        ·
          refine ⟨36574702894768772766297203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24383135263179181844198135 36574702894768772766297203)
          ·
            refine ⟨54862054342153159149445805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36574702894768772766297203 54862054342153159149445805)
            ·
              refine ⟨20573270378307434681042177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54862054342153159149445805 20573270378307434681042177)
              ·
                refine ⟨15429952783730576010781633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20573270378307434681042177 15429952783730576010781633)
                ·
                  refine ⟨11572464587797932008086225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15429952783730576010781633 11572464587797932008086225)
                  ·
                    refine ⟨8679348440848449006064669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11572464587797932008086225 8679348440848449006064669)
                    ·
                      refine ⟨3254755665318168377274251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8679348440848449006064669 3254755665318168377274251)
                      ·
                        rfl

theorem cell23_6338614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_6338614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338614 prefixEnd_6338614 := by exact prefixLift 6338614
  have htrace : WordTrace (prefixWord ++ tailWord_6338614) baseStart_6338614 baseEnd_6338614 := by
    simpa [prefixWord, tailWord_6338614, baseEnd_6338614] using wordTrace_append hprefix tailTrace_6338614
  have hstable : (prefixWord ++ tailWord_6338614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338614).length < 2 ^ (prefixWord ++ tailWord_6338614).sum := by decide
  have hdescent : baseEnd_6338614 < baseStart_6338614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338621 : List Nat := [1, 4, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_6338621 : Nat := 118140960795 + 6338621 * 2 ^ 59
def prefixEnd_6338621 : Nat := 4983230072969 + 3 ^ 40 * 6338621 * 2
def baseEnd_6338621 : Nat := 1084919753227583283295573

theorem tailTrace_6338621 : CollatzResearch.WordTrace tailWord_6338621 prefixEnd_6338621 1084919753227583283295573 := by
  unfold tailWord_6338621
  simp only [CollatzResearch.WordTrace]
  refine ⟨231188500769266142125679717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154125667179510761417119811 231188500769266142125679717)
  ·
    refine ⟨43347843894237401648564947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231188500769266142125679717 43347843894237401648564947)
    ·
      refine ⟨65021765841356102472847421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43347843894237401648564947 65021765841356102472847421)
      ·
        refine ⟨24383162190508538427317783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65021765841356102472847421 24383162190508538427317783)
        ·
          refine ⟨36574743285762807640976675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24383162190508538427317783 36574743285762807640976675)
          ·
            refine ⟨54862114928644211461465013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36574743285762807640976675 54862114928644211461465013)
            ·
              refine ⟨5143323274560394824512345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54862114928644211461465013 5143323274560394824512345)
              ·
                refine ⟨3857492455920296118384259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5143323274560394824512345 3857492455920296118384259)
                ·
                  refine ⟨5786238683880444177576389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3857492455920296118384259 5786238683880444177576389)
                  ·
                    refine ⟨1084919753227583283295573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5786238683880444177576389 1084919753227583283295573)
                    ·
                      rfl

theorem cell23_6338621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_6338621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338621 prefixEnd_6338621 := by exact prefixLift 6338621
  have htrace : WordTrace (prefixWord ++ tailWord_6338621) baseStart_6338621 baseEnd_6338621 := by
    simpa [prefixWord, tailWord_6338621, baseEnd_6338621] using wordTrace_append hprefix tailTrace_6338621
  have hstable : (prefixWord ++ tailWord_6338621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338621).length < 2 ^ (prefixWord ++ tailWord_6338621).sum := by decide
  have hdescent : baseEnd_6338621 < baseStart_6338621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338627 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 3, 1, 3]
def baseStart_6338627 : Nat := 118140960795 + 6338627 * 2 ^ 59
def prefixEnd_6338627 : Nat := 4983230072969 + 3 ^ 40 * 6338627 * 2
def baseEnd_6338627 : Nat := 3254762340566676826411691

theorem tailTrace_6338627 : CollatzResearch.WordTrace tailWord_6338627 prefixEnd_6338627 3254762340566676826411691 := by
  unfold tailWord_6338627
  simp only [CollatzResearch.WordTrace]
  refine ⟨231188719607244405150398135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154125813071496270100265423 231188719607244405150398135)
  ·
    refine ⟨346783079410866607725597203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231188719607244405150398135 346783079410866607725597203)
    ·
      refine ⟨520174619116299911588395805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346783079410866607725597203 520174619116299911588395805)
      ·
        refine ⟨195065482168612466845648427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 520174619116299911588395805 195065482168612466845648427)
        ·
          refine ⟨292598223252918700268472641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195065482168612466845648427 292598223252918700268472641)
          ·
            refine ⟨219448667439689025201354481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292598223252918700268472641 219448667439689025201354481)
            ·
              refine ⟨164586500579766768901015861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219448667439689025201354481 164586500579766768901015861)
              ·
                refine ⟨15429984429353134584470237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164586500579766768901015861 15429984429353134584470237)
                ·
                  refine ⟨5786244161007425469176339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15429984429353134584470237 5786244161007425469176339)
                  ·
                    refine ⟨8679366241511138203764509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5786244161007425469176339 8679366241511138203764509)
                    ·
                      refine ⟨3254762340566676826411691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8679366241511138203764509 3254762340566676826411691)
                      ·
                        rfl

theorem cell23_6338627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_6338627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338627 prefixEnd_6338627 := by exact prefixLift 6338627
  have htrace : WordTrace (prefixWord ++ tailWord_6338627) baseStart_6338627 baseEnd_6338627 := by
    simpa [prefixWord, tailWord_6338627, baseEnd_6338627] using wordTrace_append hprefix tailTrace_6338627
  have hstable : (prefixWord ++ tailWord_6338627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338627).length < 2 ^ (prefixWord ++ tailWord_6338627).sum := by decide
  have hdescent : baseEnd_6338627 < baseStart_6338627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338647 : List Nat := [1, 1, 3, 2, 2, 1, 5, 2, 1, 5]
def baseStart_6338647 : Nat := 118140960795 + 6338647 * 2 ^ 59
def prefixEnd_6338647 : Nat := 4983230072969 + 3 ^ 40 * 6338647 * 2
def baseEnd_6338647 : Nat := 1084924203393255582720533

theorem tailTrace_6338647 : CollatzResearch.WordTrace tailWord_6338647 prefixEnd_6338647 1084924203393255582720533 := by
  unfold tailWord_6338647
  simp only [CollatzResearch.WordTrace]
  refine ⟨231189449067171948566126195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154126299378114632377417463 231189449067171948566126195)
  ·
    refine ⟨346784173600757922849189293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231189449067171948566126195 346784173600757922849189293)
    ·
      refine ⟨130044065100284221068445985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346784173600757922849189293 130044065100284221068445985)
      ·
        refine ⟨97533048825213165801334489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130044065100284221068445985 97533048825213165801334489)
        ·
          refine ⟨73149786618909874351000867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97533048825213165801334489 73149786618909874351000867)
          ·
            refine ⟨109724679928364811526501301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73149786618909874351000867 109724679928364811526501301)
            ·
              refine ⟨10286688743284201080609497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109724679928364811526501301 10286688743284201080609497)
              ·
                refine ⟨7715016557463150810457123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10286688743284201080609497 7715016557463150810457123)
                ·
                  refine ⟨11572524836194726215685685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7715016557463150810457123 11572524836194726215685685)
                  ·
                    refine ⟨1084924203393255582720533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11572524836194726215685685 1084924203393255582720533)
                    ·
                      rfl

theorem cell23_6338647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_6338647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338647 prefixEnd_6338647 := by exact prefixLift 6338647
  have htrace : WordTrace (prefixWord ++ tailWord_6338647) baseStart_6338647 baseEnd_6338647 := by
    simpa [prefixWord, tailWord_6338647, baseEnd_6338647] using wordTrace_append hprefix tailTrace_6338647
  have hstable : (prefixWord ++ tailWord_6338647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338647).length < 2 ^ (prefixWord ++ tailWord_6338647).sum := by decide
  have hdescent : baseEnd_6338647 < baseStart_6338647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338660 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_6338660 : Nat := 118140960795 + 6338660 * 2 ^ 59
def prefixEnd_6338660 : Nat := 4983230072969 + 3 ^ 40 * 6338660 * 2
def baseEnd_6338660 : Nat := 1084926428476091732433013

theorem tailTrace_6338660 : CollatzResearch.WordTrace tailWord_6338660 prefixEnd_6338660 1084926428476091732433013 := by
  unfold tailWord_6338660
  simp only [CollatzResearch.WordTrace]
  refine ⟨115594961608062425893174717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154126615477416567857566289 115594961608062425893174717)
  ·
    refine ⟨43348110603023409709940519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115594961608062425893174717 43348110603023409709940519)
    ·
      refine ⟨65022165904535114564910779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43348110603023409709940519 65022165904535114564910779)
      ·
        refine ⟨97533248856802671847366169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65022165904535114564910779 97533248856802671847366169)
        ·
          refine ⟨73149936642602003885524627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97533248856802671847366169 73149936642602003885524627)
          ·
            refine ⟨109724904963903005828286941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73149936642602003885524627 109724904963903005828286941)
            ·
              refine ⟨41146839361463627185607603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109724904963903005828286941 41146839361463627185607603)
              ·
                refine ⟨61720259042195440778411405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41146839361463627185607603 61720259042195440778411405)
                ·
                  refine ⟨23145097140823290291904277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61720259042195440778411405 23145097140823290291904277)
                  ·
                    refine ⟨1084926428476091732433013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23145097140823290291904277 1084926428476091732433013)
                    ·
                      rfl

theorem cell23_6338660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_6338660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338660 prefixEnd_6338660 := by exact prefixLift 6338660
  have htrace : WordTrace (prefixWord ++ tailWord_6338660) baseStart_6338660 baseEnd_6338660 := by
    simpa [prefixWord, tailWord_6338660, baseEnd_6338660] using wordTrace_append hprefix tailTrace_6338660
  have hstable : (prefixWord ++ tailWord_6338660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338660).length < 2 ^ (prefixWord ++ tailWord_6338660).sum := by decide
  have hdescent : baseEnd_6338660 < baseStart_6338660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338678 : List Nat := [5, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_6338678 : Nat := 118140960795 + 6338678 * 2 ^ 59
def prefixEnd_6338678 : Nat := 4983230072969 + 3 ^ 40 * 6338678 * 2
def baseEnd_6338678 : Nat := 3254788528080056126873957

theorem tailTrace_6338678 : CollatzResearch.WordTrace tailWord_6338678 prefixEnd_6338678 3254788528080056126873957 := by
  unfold tailWord_6338678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14449411233128727553781543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154127053153373093907003125 14449411233128727553781543)
  ·
    refine ⟨21674116849693091330672315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14449411233128727553781543 21674116849693091330672315)
    ·
      refine ⟨32511175274539636996008473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21674116849693091330672315 32511175274539636996008473)
      ·
        refine ⟨24383381455904727747006355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32511175274539636996008473 24383381455904727747006355)
        ·
          refine ⟨36575072183857091620509533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24383381455904727747006355 36575072183857091620509533)
          ·
            refine ⟨13715652068946409357691075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36575072183857091620509533 13715652068946409357691075)
            ·
              refine ⟨20573478103419614036536613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13715652068946409357691075 20573478103419614036536613)
              ·
                refine ⟨3857527144391177631850615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20573478103419614036536613 3857527144391177631850615)
                ·
                  refine ⟨5786290716586766447775923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3857527144391177631850615 5786290716586766447775923)
                  ·
                    refine ⟨8679436074880149671663885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5786290716586766447775923 8679436074880149671663885)
                    ·
                      refine ⟨3254788528080056126873957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8679436074880149671663885 3254788528080056126873957)
                      ·
                        rfl

theorem cell23_6338678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_6338678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338678 prefixEnd_6338678 := by exact prefixLift 6338678
  have htrace : WordTrace (prefixWord ++ tailWord_6338678) baseStart_6338678 baseEnd_6338678 := by
    simpa [prefixWord, tailWord_6338678, baseEnd_6338678] using wordTrace_append hprefix tailTrace_6338678
  have hstable : (prefixWord ++ tailWord_6338678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338678).length < 2 ^ (prefixWord ++ tailWord_6338678).sum := by decide
  have hdescent : baseEnd_6338678 < baseStart_6338678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338680 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_6338680 : Nat := 118140960795 + 6338680 * 2 ^ 59
def prefixEnd_6338680 : Nat := 4983230072969 + 3 ^ 40 * 6338680 * 2
def baseEnd_6338680 : Nat := 3254789555041365119048947

theorem tailTrace_6338680 : CollatzResearch.WordTrace tailWord_6338680 prefixEnd_6338680 3254789555041365119048947 := by
  unfold tailWord_6338680
  simp only [CollatzResearch.WordTrace]
  refine ⟨115595326338026197601038747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154127101784034930134718329 115595326338026197601038747)
  ·
    refine ⟨173392989507039296401558121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115595326338026197601038747 173392989507039296401558121)
    ·
      refine ⟨130044742130279472301168591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173392989507039296401558121 130044742130279472301168591)
      ·
        refine ⟨195067113195419208451752887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130044742130279472301168591 195067113195419208451752887)
        ·
          refine ⟨292600669793128812677629331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195067113195419208451752887 292600669793128812677629331)
          ·
            refine ⟨438901004689693219016443997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292600669793128812677629331 438901004689693219016443997)
            ·
              refine ⟨164587876758634957131166499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 438901004689693219016443997 164587876758634957131166499)
              ·
                refine ⟨246881815137952435696749749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164587876758634957131166499 246881815137952435696749749)
                ·
                  refine ⟨23145170169183040846570289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 246881815137952435696749749 23145170169183040846570289)
                  ·
                    refine ⟨17358877626887280634927717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23145170169183040846570289 17358877626887280634927717)
                    ·
                      refine ⟨3254789555041365119048947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17358877626887280634927717 3254789555041365119048947)
                      ·
                        rfl

theorem cell23_6338680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_6338680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338680 prefixEnd_6338680 := by exact prefixLift 6338680
  have htrace : WordTrace (prefixWord ++ tailWord_6338680) baseStart_6338680 baseEnd_6338680 := by
    simpa [prefixWord, tailWord_6338680, baseEnd_6338680] using wordTrace_append hprefix tailTrace_6338680
  have hstable : (prefixWord ++ tailWord_6338680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338680).length < 2 ^ (prefixWord ++ tailWord_6338680).sum := by decide
  have hdescent : baseEnd_6338680 < baseStart_6338680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338697 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 1, 2, 4]
def baseStart_6338697 : Nat := 118140960795 + 6338697 * 2 ^ 59
def prefixEnd_6338697 : Nat := 4983230072969 + 3 ^ 40 * 6338697 * 2
def baseEnd_6338697 : Nat := 3254798284212491552536369

theorem tailTrace_6338697 : CollatzResearch.WordTrace tailWord_6338697 prefixEnd_6338697 3254798284212491552536369 := by
  unfold tailWord_6338697
  simp only [CollatzResearch.WordTrace]
  refine ⟨231191272716990807105446345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154127515144660538070297563 231191272716990807105446345)
  ·
    refine ⟨173393454537743105329084759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231191272716990807105446345 173393454537743105329084759)
    ·
      refine ⟨260090181806614657993627139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173393454537743105329084759 260090181806614657993627139)
      ·
        refine ⟨390135272709921986990440709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260090181806614657993627139 390135272709921986990440709)
        ·
          refine ⟨73150363633110372560707633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 390135272709921986990440709 73150363633110372560707633)
          ·
            refine ⟨54862772724832779420530725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73150363633110372560707633 54862772724832779420530725)
            ·
              refine ⟨10286769885906146141349511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54862772724832779420530725 10286769885906146141349511)
              ·
                refine ⟨15430154828859219212024267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10286769885906146141349511 15430154828859219212024267)
                ·
                  refine ⟨23145232243288828818036401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15430154828859219212024267 23145232243288828818036401)
                  ·
                    refine ⟨17358924182466621613527301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23145232243288828818036401 17358924182466621613527301)
                    ·
                      refine ⟨3254798284212491552536369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17358924182466621613527301 3254798284212491552536369)
                      ·
                        rfl

theorem cell23_6338697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 2, 4].length) (baseStart_6338697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338697 prefixEnd_6338697 := by exact prefixLift 6338697
  have htrace : WordTrace (prefixWord ++ tailWord_6338697) baseStart_6338697 baseEnd_6338697 := by
    simpa [prefixWord, tailWord_6338697, baseEnd_6338697] using wordTrace_append hprefix tailTrace_6338697
  have hstable : (prefixWord ++ tailWord_6338697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338697).length < 2 ^ (prefixWord ++ tailWord_6338697).sum := by decide
  have hdescent : baseEnd_6338697 < baseStart_6338697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338721 : List Nat := [1, 2, 3, 3, 1, 2, 4, 1, 1, 2, 3]
def baseStart_6338721 : Nat := 118140960795 + 6338721 * 2 ^ 59
def prefixEnd_6338721 : Nat := 4983230072969 + 3 ^ 40 * 6338721 * 2
def baseEnd_6338721 : Nat := 3254810607748199458636259

theorem tailTrace_6338721 : CollatzResearch.WordTrace tailWord_6338721 prefixEnd_6338721 3254810607748199458636259 := by
  unfold tailWord_6338721
  simp only [CollatzResearch.WordTrace]
  refine ⟨231192148068903859204320017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154128098712602572802880011 231192148068903859204320017)
  ·
    refine ⟨173394111051677894403240013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231192148068903859204320017 173394111051677894403240013)
    ·
      refine ⟨65022791644379210401215005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173394111051677894403240013 65022791644379210401215005)
      ·
        refine ⟨24383546866642203900455627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65022791644379210401215005 24383546866642203900455627)
        ·
          refine ⟨36575320299963305850683441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24383546866642203900455627 36575320299963305850683441)
          ·
            refine ⟨27431490224972479388012581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36575320299963305850683441 27431490224972479388012581)
            ·
              refine ⟨5143404417182339885252359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27431490224972479388012581 5143404417182339885252359)
              ·
                refine ⟨7715106625773509827878539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5143404417182339885252359 7715106625773509827878539)
                ·
                  refine ⟨11572659938660264741817809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7715106625773509827878539 11572659938660264741817809)
                  ·
                    refine ⟨8679494953995198556363357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11572659938660264741817809 8679494953995198556363357)
                    ·
                      refine ⟨3254810607748199458636259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8679494953995198556363357 3254810607748199458636259)
                      ·
                        rfl

theorem cell23_6338721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_6338721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338721 prefixEnd_6338721 := by exact prefixLift 6338721
  have htrace : WordTrace (prefixWord ++ tailWord_6338721) baseStart_6338721 baseEnd_6338721 := by
    simpa [prefixWord, tailWord_6338721, baseEnd_6338721] using wordTrace_append hprefix tailTrace_6338721
  have hstable : (prefixWord ++ tailWord_6338721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338721).length < 2 ^ (prefixWord ++ tailWord_6338721).sum := by decide
  have hdescent : baseEnd_6338721 < baseStart_6338721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338786 : List Nat := [3, 3, 4, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6338786 : Nat := 118140960795 + 6338786 * 2 ^ 59
def prefixEnd_6338786 : Nat := 4983230072969 + 3 ^ 40 * 6338786 * 2
def baseEnd_6338786 : Nat := 3254843983990741704323461

theorem tailTrace_6338786 : CollatzResearch.WordTrace tailWord_6338786 prefixEnd_6338786 3254843983990741704323461 := by
  unfold tailWord_6338786
  simp only [CollatzResearch.WordTrace]
  refine ⟨57798629703417093826359053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154129679209112250203624141 57798629703417093826359053)
  ·
    refine ⟨21674486138781410184884645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57798629703417093826359053 21674486138781410184884645)
    ·
      refine ⟨4063966151021514409665871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21674486138781410184884645 4063966151021514409665871)
      ·
        refine ⟨6095949226532271614498807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4063966151021514409665871 6095949226532271614498807)
        ·
          refine ⟨9143923839798407421748211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6095949226532271614498807 9143923839798407421748211)
          ·
            refine ⟨13715885759697611132622317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9143923839798407421748211 13715885759697611132622317)
            ·
              refine ⟨5143457159886604174733369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13715885759697611132622317 5143457159886604174733369)
              ·
                refine ⟨3857592869914953131050027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5143457159886604174733369 3857592869914953131050027)
                ·
                  refine ⟨5786389304872429696575041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3857592869914953131050027 5786389304872429696575041)
                  ·
                    refine ⟨4339791978654322272431281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5786389304872429696575041 4339791978654322272431281)
                    ·
                      refine ⟨3254843983990741704323461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4339791978654322272431281 3254843983990741704323461)
                      ·
                        rfl

theorem cell23_6338786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6338786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338786 prefixEnd_6338786 := by exact prefixLift 6338786
  have htrace : WordTrace (prefixWord ++ tailWord_6338786) baseStart_6338786 baseEnd_6338786 := by
    simpa [prefixWord, tailWord_6338786, baseEnd_6338786] using wordTrace_append hprefix tailTrace_6338786
  have hstable : (prefixWord ++ tailWord_6338786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338786).length < 2 ^ (prefixWord ++ tailWord_6338786).sum := by decide
  have hdescent : baseEnd_6338786 < baseStart_6338786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338837 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_6338837 : Nat := 118140960795 + 6338837 * 2 ^ 59
def prefixEnd_6338837 : Nat := 4983230072969 + 3 ^ 40 * 6338837 * 2
def baseEnd_6338837 : Nat := 3254870171504121004785725

theorem tailTrace_6338837 : CollatzResearch.WordTrace tailWord_6338837 prefixEnd_6338837 3254870171504121004785725 := by
  unfold tailWord_6338837
  simp only [CollatzResearch.WordTrace]
  refine ⟨231196378936483611015542765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154130919290989074010361843 231196378936483611015542765)
  ·
    refine ⟨86698642101181354130828537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231196378936483611015542765 86698642101181354130828537)
    ·
      refine ⟨65023981575886015598121403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86698642101181354130828537 65023981575886015598121403)
      ·
        refine ⟨97535972363829023397182105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65023981575886015598121403 97535972363829023397182105)
        ·
          refine ⟨73151979272871767547886579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97535972363829023397182105 73151979272871767547886579)
          ·
            refine ⟨109727968909307651321829869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73151979272871767547886579 109727968909307651321829869)
            ·
              refine ⟨41147988340990369245686201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109727968909307651321829869 41147988340990369245686201)
              ·
                refine ⟨30860991255742776934264651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41147988340990369245686201 30860991255742776934264651)
                ·
                  refine ⟨46291486883614165401396977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30860991255742776934264651 46291486883614165401396977)
                  ·
                    refine ⟨34718615162710624051047733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46291486883614165401396977 34718615162710624051047733)
                    ·
                      refine ⟨3254870171504121004785725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34718615162710624051047733 3254870171504121004785725)
                      ·
                        rfl

theorem cell23_6338837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_6338837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338837 prefixEnd_6338837 := by exact prefixLift 6338837
  have htrace : WordTrace (prefixWord ++ tailWord_6338837) baseStart_6338837 baseEnd_6338837 := by
    simpa [prefixWord, tailWord_6338837, baseEnd_6338837] using wordTrace_append hprefix tailTrace_6338837
  have hstable : (prefixWord ++ tailWord_6338837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338837).length < 2 ^ (prefixWord ++ tailWord_6338837).sum := by decide
  have hdescent : baseEnd_6338837 < baseStart_6338837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338848 : List Nat := [2, 1, 1, 5, 2, 3, 2, 2, 5]
def baseStart_6338848 : Nat := 118140960795 + 6338848 * 2 ^ 59
def prefixEnd_6338848 : Nat := 4983230072969 + 3 ^ 40 * 6338848 * 2
def baseEnd_6338848 : Nat := 361652868865702273527575

theorem tailTrace_6338848 : CollatzResearch.WordTrace tailWord_6338848 prefixEnd_6338848 361652868865702273527575 := by
  unfold tailWord_6338848
  simp only [CollatzResearch.WordTrace]
  refine ⟨115598390069721879947096599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154131186759629173262795465 115598390069721879947096599)
  ·
    refine ⟨173397585104582819920644899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115598390069721879947096599 173397585104582819920644899)
    ·
      refine ⟨260096377656874229880967349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173397585104582819920644899 260096377656874229880967349)
      ·
        refine ⟨24384035405331959051340689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 260096377656874229880967349 24384035405331959051340689)
        ·
          refine ⟨18288026553998969288505517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24384035405331959051340689 18288026553998969288505517)
          ·
            refine ⟨6858009957749613483189569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18288026553998969288505517 6858009957749613483189569)
            ·
              refine ⟨5143507468312210112392177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6858009957749613483189569 5143507468312210112392177)
              ·
                refine ⟨3857630601234157584294133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5143507468312210112392177 3857630601234157584294133)
                ·
                  refine ⟨361652868865702273527575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3857630601234157584294133 361652868865702273527575)
                  ·
                    rfl

theorem cell23_6338848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 5].length) (baseStart_6338848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338848 prefixEnd_6338848 := by exact prefixLift 6338848
  have htrace : WordTrace (prefixWord ++ tailWord_6338848) baseStart_6338848 baseEnd_6338848 := by
    simpa [prefixWord, tailWord_6338848, baseEnd_6338848] using wordTrace_append hprefix tailTrace_6338848
  have hstable : (prefixWord ++ tailWord_6338848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338848).length < 2 ^ (prefixWord ++ tailWord_6338848).sum := by decide
  have hdescent : baseEnd_6338848 < baseStart_6338848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338874 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 5, 4]
def baseStart_6338874 : Nat := 118140960795 + 6338874 * 2 ^ 59
def prefixEnd_6338874 : Nat := 4983230072969 + 3 ^ 40 * 6338874 * 2
def baseEnd_6338874 : Nat := 1084963056762779120007685

theorem tailTrace_6338874 : CollatzResearch.WordTrace tailWord_6338874 prefixEnd_6338874 1084963056762779120007685 := by
  unfold tailWord_6338874
  simp only [CollatzResearch.WordTrace]
  refine ⟨57799432109337391583659919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154131818958233044223093117 57799432109337391583659919)
  ·
    refine ⟨86699148164006087375489879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57799432109337391583659919 86699148164006087375489879)
    ·
      refine ⟨130048722246009131063234819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86699148164006087375489879 130048722246009131063234819)
      ·
        refine ⟨195073083369013696594852229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130048722246009131063234819 195073083369013696594852229)
        ·
          refine ⟨36576203131690068111534793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195073083369013696594852229 36576203131690068111534793)
          ·
            refine ⟨27432152348767551083651095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36576203131690068111534793 27432152348767551083651095)
            ·
              refine ⟨41148228523151326625476643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27432152348767551083651095 41148228523151326625476643)
              ·
                refine ⟨61722342784726989938214965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41148228523151326625476643 61722342784726989938214965)
                ·
                  refine ⟨5786469636068155306707653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61722342784726989938214965 5786469636068155306707653)
                  ·
                    refine ⟨1084963056762779120007685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5786469636068155306707653 1084963056762779120007685)
                    ·
                      rfl

theorem cell23_6338874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_6338874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338874 prefixEnd_6338874 := by exact prefixLift 6338874
  have htrace : WordTrace (prefixWord ++ tailWord_6338874) baseStart_6338874 baseEnd_6338874 := by
    simpa [prefixWord, tailWord_6338874, baseEnd_6338874] using wordTrace_append hprefix tailTrace_6338874
  have hstable : (prefixWord ++ tailWord_6338874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338874).length < 2 ^ (prefixWord ++ tailWord_6338874).sum := by decide
  have hdescent : baseEnd_6338874 < baseStart_6338874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338881 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_6338881 : Nat := 118140960795 + 6338881 * 2 ^ 59
def prefixEnd_6338881 : Nat := 4983230072969 + 3 ^ 40 * 6338881 * 2
def baseEnd_6338881 : Nat := 3254892764652918832635523

theorem tailTrace_6338881 : CollatzResearch.WordTrace tailWord_6338881 prefixEnd_6338881 3254892764652918832635523 := by
  unfold tailWord_6338881
  simp only [CollatzResearch.WordTrace]
  refine ⟨231197983748324206530144497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154131989165549471020096331 231197983748324206530144497)
  ·
    refine ⟨173398487811243154897608373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231197983748324206530144497 173398487811243154897608373)
    ·
      refine ⟨16256108232304045771650785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173398487811243154897608373 16256108232304045771650785)
      ·
        refine ⟨12192081174228034328738089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16256108232304045771650785 12192081174228034328738089)
        ·
          refine ⟨9144060880671025746553567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12192081174228034328738089 9144060880671025746553567)
          ·
            refine ⟨13716091321006538619830351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9144060880671025746553567 13716091321006538619830351)
            ·
              refine ⟨20574136981509807929745527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13716091321006538619830351 20574136981509807929745527)
              ·
                refine ⟨30861205472264711894618291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20574136981509807929745527 30861205472264711894618291)
                ·
                  refine ⟨46291808208397067841927437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30861205472264711894618291 46291808208397067841927437)
                  ·
                    refine ⟨17359428078148900440722789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46291808208397067841927437 17359428078148900440722789)
                    ·
                      refine ⟨3254892764652918832635523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17359428078148900440722789 3254892764652918832635523)
                      ·
                        rfl

theorem cell23_6338881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_6338881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338881 prefixEnd_6338881 := by exact prefixLift 6338881
  have htrace : WordTrace (prefixWord ++ tailWord_6338881) baseStart_6338881 baseEnd_6338881 := by
    simpa [prefixWord, tailWord_6338881, baseEnd_6338881] using wordTrace_append hprefix tailTrace_6338881
  have hstable : (prefixWord ++ tailWord_6338881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338881).length < 2 ^ (prefixWord ++ tailWord_6338881).sum := by decide
  have hdescent : baseEnd_6338881 < baseStart_6338881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338887 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 8]
def baseStart_6338887 : Nat := 118140960795 + 6338887 * 2 ^ 59
def prefixEnd_6338887 : Nat := 4983230072969 + 3 ^ 40 * 6338887 * 2
def baseEnd_6338887 : Nat := 361655093948538423240055

theorem tailTrace_6338887 : CollatzResearch.WordTrace tailWord_6338887 prefixEnd_6338887 361655093948538423240055 := by
  unfold tailWord_6338887
  simp only [CollatzResearch.WordTrace]
  refine ⟨231198202586302469554862915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154132135057534979703241943 231198202586302469554862915)
  ·
    refine ⟨346797303879453704332294373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231198202586302469554862915 346797303879453704332294373)
    ·
      refine ⟨65024494477397569562305195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346797303879453704332294373 65024494477397569562305195)
      ·
        refine ⟨97536741716096354343457793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65024494477397569562305195 97536741716096354343457793)
        ·
          refine ⟨73152556287072265757593345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97536741716096354343457793 73152556287072265757593345)
          ·
            refine ⟨54864417215304199318195009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73152556287072265757593345 54864417215304199318195009)
            ·
              refine ⟨41148312911478149488646257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54864417215304199318195009 41148312911478149488646257)
              ·
                refine ⟨30861234683608612116484693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41148312911478149488646257 30861234683608612116484693)
                ·
                  refine ⟨361655093948538423240055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30861234683608612116484693 361655093948538423240055)
                  ·
                    rfl

theorem cell23_6338887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 8].length) (baseStart_6338887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338887 prefixEnd_6338887 := by exact prefixLift 6338887
  have htrace : WordTrace (prefixWord ++ tailWord_6338887) baseStart_6338887 baseEnd_6338887 := by
    simpa [prefixWord, tailWord_6338887, baseEnd_6338887] using wordTrace_append hprefix tailTrace_6338887
  have hstable : (prefixWord ++ tailWord_6338887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338887).length < 2 ^ (prefixWord ++ tailWord_6338887).sum := by decide
  have hdescent : baseEnd_6338887 < baseStart_6338887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338941 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 1, 5, 2]
def baseStart_6338941 : Nat := 118140960795 + 6338941 * 2 ^ 59
def prefixEnd_6338941 : Nat := 4983230072969 + 3 ^ 40 * 6338941 * 2
def baseEnd_6338941 : Nat := 3254923573492188597885247

theorem tailTrace_6338941 : CollatzResearch.WordTrace tailWord_6338941 prefixEnd_6338941 3254923573492188597885247 := by
  unfold tailWord_6338941
  simp only [CollatzResearch.WordTrace]
  refine ⟨231200172128106836777328677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154133448085404557851552451 231200172128106836777328677)
  ·
    refine ⟨43350032274020031895749127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231200172128106836777328677 43350032274020031895749127)
    ·
      refine ⟨65025048411030047843623691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43350032274020031895749127 65025048411030047843623691)
      ·
        refine ⟨97537572616545071765435537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65025048411030047843623691 97537572616545071765435537)
        ·
          refine ⟨73153179462408803824076653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97537572616545071765435537 73153179462408803824076653)
          ·
            refine ⟨27432442298403301434028745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73153179462408803824076653 27432442298403301434028745)
            ·
              refine ⟨20574331723802476075521559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27432442298403301434028745 20574331723802476075521559)
              ·
                refine ⟨30861497585703714113282339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20574331723802476075521559 30861497585703714113282339)
                ·
                  refine ⟨46292246378555571169923509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30861497585703714113282339 46292246378555571169923509)
                  ·
                    refine ⟨4339898097989584797180329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46292246378555571169923509 4339898097989584797180329)
                    ·
                      refine ⟨3254923573492188597885247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4339898097989584797180329 3254923573492188597885247)
                      ·
                        rfl

theorem cell23_6338941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_6338941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338941 prefixEnd_6338941 := by exact prefixLift 6338941
  have htrace : WordTrace (prefixWord ++ tailWord_6338941) baseStart_6338941 baseEnd_6338941 := by
    simpa [prefixWord, tailWord_6338941, baseEnd_6338941] using wordTrace_append hprefix tailTrace_6338941
  have hstable : (prefixWord ++ tailWord_6338941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338941).length < 2 ^ (prefixWord ++ tailWord_6338941).sum := by decide
  have hdescent : baseEnd_6338941 < baseStart_6338941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338958 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2]
def baseStart_6338958 : Nat := 118140960795 + 6338958 * 2 ^ 59
def prefixEnd_6338958 : Nat := 4983230072969 + 3 ^ 40 * 6338958 * 2
def baseEnd_6338958 : Nat := 3254932302663315031372669

theorem tailTrace_6338958 : CollatzResearch.WordTrace tailWord_6338958 prefixEnd_6338958 3254932302663315031372669 := by
  unfold tailWord_6338958
  simp only [CollatzResearch.WordTrace]
  refine ⟨28900099021130656085087191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154133861446030165787131685 28900099021130656085087191)
  ·
    refine ⟨43350148531695984127630787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28900099021130656085087191 43350148531695984127630787)
    ·
      refine ⟨65025222797543976191446181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43350148531695984127630787 65025222797543976191446181)
      ·
        refine ⟨12192229274539495535896159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65025222797543976191446181 12192229274539495535896159)
        ·
          refine ⟨18288343911809243303844239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12192229274539495535896159 18288343911809243303844239)
          ·
            refine ⟨27432515867713864955766359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18288343911809243303844239 27432515867713864955766359)
            ·
              refine ⟨41148773801570797433649539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27432515867713864955766359 41148773801570797433649539)
              ·
                refine ⟨61723160702356196150474309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41148773801570797433649539 61723160702356196150474309)
                ·
                  refine ⟨11573092631691786778213933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61723160702356196150474309 11573092631691786778213933)
                  ·
                    refine ⟨4339909736884420041830225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11573092631691786778213933 4339909736884420041830225)
                    ·
                      refine ⟨3254932302663315031372669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4339909736884420041830225 3254932302663315031372669)
                      ·
                        rfl

theorem cell23_6338958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_6338958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338958 prefixEnd_6338958 := by exact prefixLift 6338958
  have htrace : WordTrace (prefixWord ++ tailWord_6338958) baseStart_6338958 baseEnd_6338958 := by
    simpa [prefixWord, tailWord_6338958, baseEnd_6338958] using wordTrace_append hprefix tailTrace_6338958
  have hstable : (prefixWord ++ tailWord_6338958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338958).length < 2 ^ (prefixWord ++ tailWord_6338958).sum := by decide
  have hdescent : baseEnd_6338958 < baseStart_6338958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338981 : List Nat := [1, 3, 1, 2, 1, 1, 5, 3, 2, 4]
def baseStart_6338981 : Nat := 118140960795 + 6338981 * 2 ^ 59
def prefixEnd_6338981 : Nat := 4983230072969 + 3 ^ 40 * 6338981 * 2
def baseEnd_6338981 : Nat := 1084981370906122813795021

theorem tailTrace_6338981 : CollatzResearch.WordTrace tailWord_6338981 prefixEnd_6338981 1084981370906122813795021 := by
  unfold tailWord_6338981
  simp only [CollatzResearch.WordTrace]
  refine ⟨231201631047961923608784797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154134420698641282405856531 231201631047961923608784797)
  ·
    refine ⟨86700611642985721353294299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231201631047961923608784797 86700611642985721353294299)
    ·
      refine ⟨130050917464478582029941449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86700611642985721353294299 130050917464478582029941449)
      ·
        refine ⟨97538188098358936522456087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130050917464478582029941449 97538188098358936522456087)
        ·
          refine ⟨146307282147538404783684131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97538188098358936522456087 146307282147538404783684131)
          ·
            refine ⟨219460923221307607175526197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146307282147538404783684131 219460923221307607175526197)
            ·
              refine ⟨20574461551997588172705581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219460923221307607175526197 20574461551997588172705581)
              ·
                refine ⟨7715423081999095564764593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20574461551997588172705581 7715423081999095564764593)
                ·
                  refine ⟨5786567311499321673573445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7715423081999095564764593 5786567311499321673573445)
                  ·
                    refine ⟨1084981370906122813795021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5786567311499321673573445 1084981370906122813795021)
                    ·
                      rfl

theorem cell23_6338981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_6338981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338981 prefixEnd_6338981 := by exact prefixLift 6338981
  have htrace : WordTrace (prefixWord ++ tailWord_6338981) baseStart_6338981 baseEnd_6338981 := by
    simpa [prefixWord, tailWord_6338981, baseEnd_6338981] using wordTrace_append hprefix tailTrace_6338981
  have hstable : (prefixWord ++ tailWord_6338981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338981).length < 2 ^ (prefixWord ++ tailWord_6338981).sum := by decide
  have hdescent : baseEnd_6338981 < baseStart_6338981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339001 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 1, 2, 4]
def baseStart_6339001 : Nat := 118140960795 + 6339001 * 2 ^ 59
def prefixEnd_6339001 : Nat := 4983230072969 + 3 ^ 40 * 6339001 * 2
def baseEnd_6339001 : Nat := 3254954382331458363134971

theorem tailTrace_6339001 : CollatzResearch.WordTrace tailWord_6339001 prefixEnd_6339001 3254954382331458363134971 := by
  unfold tailWord_6339001
  simp only [CollatzResearch.WordTrace]
  refine ⟨231202360507889467024512857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154134907005259644683008571 231202360507889467024512857)
  ·
    refine ⟨173401770380917100268384643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231202360507889467024512857 173401770380917100268384643)
    ·
      refine ⟨260102655571375650402576965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173401770380917100268384643 260102655571375650402576965)
      ·
        refine ⟨48769247919632934450483181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260102655571375650402576965 48769247919632934450483181)
        ·
          refine ⟨18288467969862350418931193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48769247919632934450483181 18288467969862350418931193)
          ·
            refine ⟨13716350977396762814198395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18288467969862350418931193 13716350977396762814198395)
            ·
              refine ⟨20574526466095144221297593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13716350977396762814198395 20574526466095144221297593)
              ·
                refine ⟨15430894849571358165973195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20574526466095144221297593 15430894849571358165973195)
                ·
                  refine ⟨23146342274357037248959793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15430894849571358165973195 23146342274357037248959793)
                  ·
                    refine ⟨17359756705767777936719845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23146342274357037248959793 17359756705767777936719845)
                    ·
                      refine ⟨3254954382331458363134971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17359756705767777936719845 3254954382331458363134971)
                      ·
                        rfl

theorem cell23_6339001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_6339001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339001 prefixEnd_6339001 := by exact prefixLift 6339001
  have htrace : WordTrace (prefixWord ++ tailWord_6339001) baseStart_6339001 baseEnd_6339001 := by
    simpa [prefixWord, tailWord_6339001, baseEnd_6339001] using wordTrace_append hprefix tailTrace_6339001
  have hstable : (prefixWord ++ tailWord_6339001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339001).length < 2 ^ (prefixWord ++ tailWord_6339001).sum := by decide
  have hdescent : baseEnd_6339001 < baseStart_6339001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339048 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_6339048 : Nat := 118140960795 + 6339048 * 2 ^ 59
def prefixEnd_6339048 : Nat := 4983230072969 + 3 ^ 40 * 6339048 * 2
def baseEnd_6339048 : Nat := 3254978515922219679247255

theorem tailTrace_6339048 : CollatzResearch.WordTrace tailWord_6339048 prefixEnd_6339048 3254978515922219679247255 := by
  unfold tailWord_6339048
  simp only [CollatzResearch.WordTrace]
  refine ⟨115602037369359597025736899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154136049825812796034315865 115602037369359597025736899)
  ·
    refine ⟨173403056054039395538605349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115602037369359597025736899 173403056054039395538605349)
    ·
      refine ⟨32513073010132386663488503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173403056054039395538605349 32513073010132386663488503)
      ·
        refine ⟨48769609515198579995232755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32513073010132386663488503 48769609515198579995232755)
        ·
          refine ⟨73154414272797869992849133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48769609515198579995232755 73154414272797869992849133)
          ·
            refine ⟨27432905352299201247318425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73154414272797869992849133 27432905352299201247318425)
            ·
              refine ⟨20574679014224400935488819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27432905352299201247318425 20574679014224400935488819)
              ·
                refine ⟨30862018521336601403233229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20574679014224400935488819 30862018521336601403233229)
                ·
                  refine ⟨11573256945501225526212461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30862018521336601403233229 11573256945501225526212461)
                  ·
                    refine ⟨4339971354562959572329673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11573256945501225526212461 4339971354562959572329673)
                    ·
                      refine ⟨3254978515922219679247255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4339971354562959572329673 3254978515922219679247255)
                      ·
                        rfl

theorem cell23_6339048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_6339048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339048 prefixEnd_6339048 := by exact prefixLift 6339048
  have htrace : WordTrace (prefixWord ++ tailWord_6339048) baseStart_6339048 baseEnd_6339048 := by
    simpa [prefixWord, tailWord_6339048, baseEnd_6339048] using wordTrace_append hprefix tailTrace_6339048
  have hstable : (prefixWord ++ tailWord_6339048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339048).length < 2 ^ (prefixWord ++ tailWord_6339048).sum := by decide
  have hdescent : baseEnd_6339048 < baseStart_6339048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339064 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_6339064 : Nat := 118140960795 + 6339064 * 2 ^ 59
def prefixEnd_6339064 : Nat := 4983230072969 + 3 ^ 40 * 6339064 * 2
def baseEnd_6339064 : Nat := 3254986731612691616647181

theorem tailTrace_6339064 : CollatzResearch.WordTrace tailWord_6339064 prefixEnd_6339064 3254986731612691616647181 := by
  unfold tailWord_6339064
  simp only [CollatzResearch.WordTrace]
  refine ⟨115602329153330614392028123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154136438871107485856037497 115602329153330614392028123)
  ·
    refine ⟨173403493729995921588042185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115602329153330614392028123 173403493729995921588042185)
    ·
      refine ⟨130052620297496941191031639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173403493729995921588042185 130052620297496941191031639)
      ·
        refine ⟨195078930446245411786547459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130052620297496941191031639 195078930446245411786547459)
        ·
          refine ⟨292618395669368117679821189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195078930446245411786547459 292618395669368117679821189)
          ·
            refine ⟨54865949188006522064966473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292618395669368117679821189 54865949188006522064966473)
            ·
              refine ⟨41149461891004891548724855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54865949188006522064966473 41149461891004891548724855)
              ·
                refine ⟨61724192836507337323087283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41149461891004891548724855 61724192836507337323087283)
                ·
                  refine ⟨92586289254761005984630925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61724192836507337323087283 92586289254761005984630925)
                  ·
                    refine ⟨34719858470535377244236597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92586289254761005984630925 34719858470535377244236597)
                    ·
                      refine ⟨3254986731612691616647181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34719858470535377244236597 3254986731612691616647181)
                      ·
                        rfl

theorem cell23_6339064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_6339064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339064 prefixEnd_6339064 := by exact prefixLift 6339064
  have htrace : WordTrace (prefixWord ++ tailWord_6339064) baseStart_6339064 baseEnd_6339064 := by
    simpa [prefixWord, tailWord_6339064, baseEnd_6339064] using wordTrace_append hprefix tailTrace_6339064
  have hstable : (prefixWord ++ tailWord_6339064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339064).length < 2 ^ (prefixWord ++ tailWord_6339064).sum := by decide
  have hdescent : baseEnd_6339064 < baseStart_6339064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339065 : List Nat := [1, 2, 1, 3, 1, 2, 6, 1, 1, 3, 2]
def baseStart_6339065 : Nat := 118140960795 + 6339065 * 2 ^ 59
def prefixEnd_6339065 : Nat := 4983230072969 + 3 ^ 40 * 6339065 * 2
def baseEnd_6339065 : Nat := 3254987245093346112734677

theorem tailTrace_6339065 : CollatzResearch.WordTrace tailWord_6339065 prefixEnd_6339065 3254987245093346112734677 := by
  unfold tailWord_6339065
  simp only [CollatzResearch.WordTrace]
  refine ⟨231204694779657605954842649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154136463186438403969895099 231204694779657605954842649)
  ·
    refine ⟨173403521084743204466131987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231204694779657605954842649 173403521084743204466131987)
    ·
      refine ⟨260105281627114806699197981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173403521084743204466131987 260105281627114806699197981)
      ·
        refine ⟨97539480610168052512199243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260105281627114806699197981 97539480610168052512199243)
        ·
          refine ⟨146309220915252078768298865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97539480610168052512199243 146309220915252078768298865)
          ·
            refine ⟨109731915686439059076224149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146309220915252078768298865 109731915686439059076224149)
            ·
              refine ⟨5143683547801830894198007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109731915686439059076224149 5143683547801830894198007)
              ·
                refine ⟨7715525321702746341297011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5143683547801830894198007 7715525321702746341297011)
                ·
                  refine ⟨11573287982554119511945517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7715525321702746341297011 11573287982554119511945517)
                  ·
                    refine ⟨4339982993457794816979569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11573287982554119511945517 4339982993457794816979569)
                    ·
                      refine ⟨3254987245093346112734677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4339982993457794816979569 3254987245093346112734677)
                      ·
                        rfl

theorem cell23_6339065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_6339065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339065 prefixEnd_6339065 := by exact prefixLift 6339065
  have htrace : WordTrace (prefixWord ++ tailWord_6339065) baseStart_6339065 baseEnd_6339065 := by
    simpa [prefixWord, tailWord_6339065, baseEnd_6339065] using wordTrace_append hprefix tailTrace_6339065
  have hstable : (prefixWord ++ tailWord_6339065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339065).length < 2 ^ (prefixWord ++ tailWord_6339065).sum := by decide
  have hdescent : baseEnd_6339065 < baseStart_6339065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339101 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 7]
def baseStart_6339101 : Nat := 118140960795 + 6339101 * 2 ^ 59
def prefixEnd_6339101 : Nat := 4983230072969 + 3 ^ 40 * 6339101 * 2
def baseEnd_6339101 : Nat := 361667303377434219098279

theorem tailTrace_6339101 : CollatzResearch.WordTrace tailWord_6339101 prefixEnd_6339101 361667303377434219098279 := by
  unfold tailWord_6339101
  simp only [CollatzResearch.WordTrace]
  refine ⟨231206007807527184103153157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154137338538351456068768771 231206007807527184103153157)
  ·
    refine ⟨43351126463911347019341217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231206007807527184103153157 43351126463911347019341217)
    ·
      refine ⟨32513344847933510264505913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43351126463911347019341217 32513344847933510264505913)
      ·
        refine ⟨24385008635950132698379435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32513344847933510264505913 24385008635950132698379435)
        ·
          refine ⟨36577512953925199047569153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24385008635950132698379435 36577512953925199047569153)
          ·
            refine ⟨27433134715443899285676865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36577512953925199047569153 27433134715443899285676865)
            ·
              refine ⟨20574851036582924464257649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27433134715443899285676865 20574851036582924464257649)
              ·
                refine ⟨15431138277437193348193237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20574851036582924464257649 15431138277437193348193237)
                ·
                  refine ⟨361667303377434219098279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15431138277437193348193237 361667303377434219098279)
                  ·
                    rfl

theorem cell23_6339101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_6339101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339101 prefixEnd_6339101 := by exact prefixLift 6339101
  have htrace : WordTrace (prefixWord ++ tailWord_6339101) baseStart_6339101 baseEnd_6339101 := by
    simpa [prefixWord, tailWord_6339101, baseEnd_6339101] using wordTrace_append hprefix tailTrace_6339101
  have hstable : (prefixWord ++ tailWord_6339101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339101).length < 2 ^ (prefixWord ++ tailWord_6339101).sum := by decide
  have hdescent : baseEnd_6339101 < baseStart_6339101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339141 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_6339141 : Nat := 118140960795 + 6339141 * 2 ^ 59
def prefixEnd_6339141 : Nat := 4983230072969 + 3 ^ 40 * 6339141 * 2
def baseEnd_6339141 : Nat := 3255026269623087815384327

theorem tailTrace_6339141 : CollatzResearch.WordTrace tailWord_6339141 prefixEnd_6339141 3255026269623087815384327 := by
  unfold tailWord_6339141
  simp only [CollatzResearch.WordTrace]
  refine ⟨231207466727382270934609277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154138311151588180623072851 231207466727382270934609277)
  ·
    refine ⟨86702800022768351600478479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231207466727382270934609277 86702800022768351600478479)
    ·
      refine ⟨130054200034152527400717719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86702800022768351600478479 130054200034152527400717719)
      ·
        refine ⟨195081300051228791101076579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130054200034152527400717719 195081300051228791101076579)
        ·
          refine ⟨292621950076843186651614869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195081300051228791101076579 292621950076843186651614869)
          ·
            refine ⟨13716653909852024374294447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 292621950076843186651614869 13716653909852024374294447)
            ·
              refine ⟨20574980864778036561441671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13716653909852024374294447 20574980864778036561441671)
              ·
                refine ⟨30862471297167054842162507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20574980864778036561441671 30862471297167054842162507)
                ·
                  refine ⟨46293706945750582263243761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30862471297167054842162507 46293706945750582263243761)
                  ·
                    refine ⟨34720280209312936697432821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46293706945750582263243761 34720280209312936697432821)
                    ·
                      refine ⟨3255026269623087815384327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34720280209312936697432821 3255026269623087815384327)
                      ·
                        rfl

theorem cell23_6339141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_6339141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339141 prefixEnd_6339141 := by exact prefixLift 6339141
  have htrace : WordTrace (prefixWord ++ tailWord_6339141) baseStart_6339141 baseEnd_6339141 := by
    simpa [prefixWord, tailWord_6339141, baseEnd_6339141] using wordTrace_append hprefix tailTrace_6339141
  have hstable : (prefixWord ++ tailWord_6339141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339141).length < 2 ^ (prefixWord ++ tailWord_6339141).sum := by decide
  have hdescent : baseEnd_6339141 < baseStart_6339141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339191 : List Nat := [1, 1, 3, 1, 1, 3, 3, 4, 6]
def baseStart_6339191 : Nat := 118140960795 + 6339191 * 2 ^ 59
def prefixEnd_6339191 : Nat := 4983230072969 + 3 ^ 40 * 6339191 * 2
def baseEnd_6339191 : Nat := 361672438183979179973233

theorem tailTrace_6339191 : CollatzResearch.WordTrace tailWord_6339191 prefixEnd_6339191 361672438183979179973233 := by
  unfold tailWord_6339191
  simp only [CollatzResearch.WordTrace]
  refine ⟨231209290377201129473929427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154139526918134086315952951 231209290377201129473929427)
  ·
    refine ⟨346813935565801694210894141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231209290377201129473929427 346813935565801694210894141)
    ·
      refine ⟨130055225837175635329085303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346813935565801694210894141 130055225837175635329085303)
      ·
        refine ⟨195082838755763452993627955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130055225837175635329085303 195082838755763452993627955)
        ·
          refine ⟨292624258133645179490441933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195082838755763452993627955 292624258133645179490441933)
          ·
            refine ⟨109734096800116942308915725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292624258133645179490441933 109734096800116942308915725)
            ·
              refine ⟨41150286300043853365843397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109734096800116942308915725 41150286300043853365843397)
              ·
                refine ⟨7715678681258222506095637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41150286300043853365843397 7715678681258222506095637)
                ·
                  refine ⟨361672438183979179973233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7715678681258222506095637 361672438183979179973233)
                  ·
                    rfl

theorem cell23_6339191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 6].length) (baseStart_6339191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339191 prefixEnd_6339191 := by exact prefixLift 6339191
  have htrace : WordTrace (prefixWord ++ tailWord_6339191) baseStart_6339191 baseEnd_6339191 := by
    simpa [prefixWord, tailWord_6339191, baseEnd_6339191] using wordTrace_append hprefix tailTrace_6339191
  have hstable : (prefixWord ++ tailWord_6339191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339191).length < 2 ^ (prefixWord ++ tailWord_6339191).sum := by decide
  have hdescent : baseEnd_6339191 < baseStart_6339191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339281 : List Nat := [1, 2, 2, 1, 2, 3, 3, 9]
def baseStart_6339281 : Nat := 118140960795 + 6339281 * 2 ^ 59
def prefixEnd_6339281 : Nat := 4983230072969 + 3 ^ 40 * 6339281 * 2
def baseEnd_6339281 : Nat := 120559190996841380282729

theorem tailTrace_6339281 : CollatzResearch.WordTrace tailWord_6339281 prefixEnd_6339281 120559190996841380282729 := by
  unfold tailWord_6339281
  simp only [CollatzResearch.WordTrace]
  refine ⟨231212572946875074844705697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154141715297916716563137131 231212572946875074844705697)
  ·
    refine ⟨173409429710156306133529273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231212572946875074844705697 173409429710156306133529273)
    ·
      refine ⟨130057072282617229600146955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173409429710156306133529273 130057072282617229600146955)
      ·
        refine ⟨195085608423925844400220433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130057072282617229600146955 195085608423925844400220433)
        ·
          refine ⟨146314206317944383300165325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195085608423925844400220433 146314206317944383300165325)
          ·
            refine ⟨54867827369229143737561997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146314206317944383300165325 54867827369229143737561997)
            ·
              refine ⟨20575435263460928901585749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54867827369229143737561997 20575435263460928901585749)
              ·
                refine ⟨120559190996841380282729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20575435263460928901585749 120559190996841380282729)
                ·
                  rfl

theorem cell23_6339281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 9].length) (baseStart_6339281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339281 prefixEnd_6339281 := by exact prefixLift 6339281
  have htrace : WordTrace (prefixWord ++ tailWord_6339281) baseStart_6339281 baseEnd_6339281 := by
    simpa [prefixWord, tailWord_6339281, baseEnd_6339281] using wordTrace_append hprefix tailTrace_6339281
  have hstable : (prefixWord ++ tailWord_6339281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339281).length < 2 ^ (prefixWord ++ tailWord_6339281).sum := by decide
  have hdescent : baseEnd_6339281 < baseStart_6339281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339292 : List Nat := [2, 2, 5, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_6339292 : Nat := 118140960795 + 6339292 * 2 ^ 59
def prefixEnd_6339292 : Nat := 4983230072969 + 3 ^ 40 * 6339292 * 2
def baseEnd_6339292 : Nat := 3255103805201916724596133

theorem tailTrace_6339292 : CollatzResearch.WordTrace tailWord_6339292 prefixEnd_6339292 3255103805201916724596133 := by
  unfold tailWord_6339292
  simp only [CollatzResearch.WordTrace]
  refine ⟨115606487074917611861678065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154141982766556815815570753 115606487074917611861678065)
  ·
    refine ⟨86704865306188208896258549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115606487074917611861678065 86704865306188208896258549)
    ·
      refine ⟨8128581122455144584024239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86704865306188208896258549 8128581122455144584024239)
      ·
        refine ⟨12192871683682716876036359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8128581122455144584024239 12192871683682716876036359)
        ·
          refine ⟨18289307525524075314054539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12192871683682716876036359 18289307525524075314054539)
          ·
            refine ⟨27433961288286112971081809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18289307525524075314054539 27433961288286112971081809)
            ·
              refine ⟨20575470966214584728311357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27433961288286112971081809 20575470966214584728311357)
              ·
                refine ⟨7715801612330469273116759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20575470966214584728311357 7715801612330469273116759)
                ·
                  refine ⟨11573702418495703909675139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7715801612330469273116759 11573702418495703909675139)
                  ·
                    refine ⟨17360553627743555864512709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11573702418495703909675139 17360553627743555864512709)
                    ·
                      refine ⟨3255103805201916724596133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17360553627743555864512709 3255103805201916724596133)
                      ·
                        rfl

theorem cell23_6339292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_6339292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339292 prefixEnd_6339292 := by exact prefixLift 6339292
  have htrace : WordTrace (prefixWord ++ tailWord_6339292) baseStart_6339292 baseEnd_6339292 := by
    simpa [prefixWord, tailWord_6339292, baseEnd_6339292] using wordTrace_append hprefix tailTrace_6339292
  have hstable : (prefixWord ++ tailWord_6339292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339292).length < 2 ^ (prefixWord ++ tailWord_6339292).sum := by decide
  have hdescent : baseEnd_6339292 < baseStart_6339292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339295 : List Nat := [1, 1, 2, 3, 2, 3, 2, 3, 1, 2, 3]
def baseStart_6339295 : Nat := 118140960795 + 6339295 * 2 ^ 59
def prefixEnd_6339295 : Nat := 4983230072969 + 3 ^ 40 * 6339295 * 2
def baseEnd_6339295 : Nat := 3255105345643880212858619

theorem tailTrace_6339295 : CollatzResearch.WordTrace tailWord_6339295 prefixEnd_6339295 3255105345643880212858619 := by
  unfold tailWord_6339295
  simp only [CollatzResearch.WordTrace]
  refine ⟨231213083568824355235715339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154142055712549570157143559 231213083568824355235715339)
  ·
    refine ⟨346819625353236532853573009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231213083568824355235715339 346819625353236532853573009)
    ·
      refine ⟨260114719014927399640179757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346819625353236532853573009 260114719014927399640179757)
      ·
        refine ⟨97543019630597774865067409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260114719014927399640179757 97543019630597774865067409)
        ·
          refine ⟨73157264722948331148800557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97543019630597774865067409 73157264722948331148800557)
          ·
            refine ⟨27433974271105624180800209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73157264722948331148800557 27433974271105624180800209)
            ·
              refine ⟨20575480703329218135600157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27433974271105624180800209 20575480703329218135600157)
              ·
                refine ⟨7715805263748456800850059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20575480703329218135600157 7715805263748456800850059)
                ·
                  refine ⟨11573707895622685201275089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7715805263748456800850059 11573707895622685201275089)
                  ·
                    refine ⟨8680280921717013900956317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11573707895622685201275089 8680280921717013900956317)
                    ·
                      refine ⟨3255105345643880212858619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8680280921717013900956317 3255105345643880212858619)
                      ·
                        rfl

theorem cell23_6339295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_6339295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339295 prefixEnd_6339295 := by exact prefixLift 6339295
  have htrace : WordTrace (prefixWord ++ tailWord_6339295) baseStart_6339295 baseEnd_6339295 := by
    simpa [prefixWord, tailWord_6339295, baseEnd_6339295] using wordTrace_append hprefix tailTrace_6339295
  have hstable : (prefixWord ++ tailWord_6339295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339295).length < 2 ^ (prefixWord ++ tailWord_6339295).sum := by decide
  have hdescent : baseEnd_6339295 < baseStart_6339295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339318 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_6339318 : Nat := 118140960795 + 6339318 * 2 ^ 59
def prefixEnd_6339318 : Nat := 4983230072969 + 3 ^ 40 * 6339318 * 2
def baseEnd_6339318 : Nat := 3255117155698933622871013

theorem tailTrace_6339318 : CollatzResearch.WordTrace tailWord_6339318 prefixEnd_6339318 3255117155698933622871013 := by
  unfold tailWord_6339318
  simp only [CollatzResearch.WordTrace]
  refine ⟨14450870152983814385237663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154142614965160686775868405 14450870152983814385237663)
  ·
    refine ⟨21676305229475721577856495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14450870152983814385237663 21676305229475721577856495)
    ·
      refine ⟨32514457844213582366784743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21676305229475721577856495 32514457844213582366784743)
      ·
        refine ⟨48771686766320373550177115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32514457844213582366784743 48771686766320373550177115)
        ·
          refine ⟨73157530149480560325265673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48771686766320373550177115 73157530149480560325265673)
          ·
            refine ⟨54868147612110420243949255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73157530149480560325265673 54868147612110420243949255)
            ·
              refine ⟨82302221418165630365923883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54868147612110420243949255 82302221418165630365923883)
              ·
                refine ⟨123453332127248445548885825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82302221418165630365923883 123453332127248445548885825)
                ·
                  refine ⟨92589999095436334161664369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123453332127248445548885825 92589999095436334161664369)
                  ·
                    refine ⟨69442499321577250621248277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92589999095436334161664369 69442499321577250621248277)
                    ·
                      refine ⟨3255117155698933622871013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69442499321577250621248277 3255117155698933622871013)
                      ·
                        rfl

theorem cell23_6339318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_6339318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339318 prefixEnd_6339318 := by exact prefixLift 6339318
  have htrace : WordTrace (prefixWord ++ tailWord_6339318) baseStart_6339318 baseEnd_6339318 := by
    simpa [prefixWord, tailWord_6339318, baseEnd_6339318] using wordTrace_append hprefix tailTrace_6339318
  have hstable : (prefixWord ++ tailWord_6339318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339318).length < 2 ^ (prefixWord ++ tailWord_6339318).sum := by decide
  have hdescent : baseEnd_6339318 < baseStart_6339318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339331 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 8]
def baseStart_6339331 : Nat := 118140960795 + 6339331 * 2 ^ 59
def prefixEnd_6339331 : Nat := 4983230072969 + 3 ^ 40 * 6339331 * 2
def baseEnd_6339331 : Nat := 3255123830947442072008453

theorem tailTrace_6339331 : CollatzResearch.WordTrace tailWord_6339331 prefixEnd_6339331 3255123830947442072008453 := by
  unfold tailWord_6339331
  simp only [CollatzResearch.WordTrace]
  refine ⟨231214396596693933384025847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154142931064462622256017231 231214396596693933384025847)
  ·
    refine ⟨346821594895040900076038771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231214396596693933384025847 346821594895040900076038771)
    ·
      refine ⟨520232392342561350114058157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346821594895040900076038771 520232392342561350114058157)
      ·
        refine ⟨195087147128460506292771809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 520232392342561350114058157 195087147128460506292771809)
        ·
          refine ⟨146315360346345379719578857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195087147128460506292771809 146315360346345379719578857)
          ·
            refine ⟨109736520259759034789684143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146315360346345379719578857 109736520259759034789684143)
            ·
              refine ⟨164604780389638552184526215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109736520259759034789684143 164604780389638552184526215)
              ·
                refine ⟨246907170584457828276789323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164604780389638552184526215 246907170584457828276789323)
                ·
                  refine ⟨370360755876686742415183985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246907170584457828276789323 370360755876686742415183985)
                  ·
                    refine ⟨277770566907515056811387989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 370360755876686742415183985 277770566907515056811387989)
                    ·
                      refine ⟨3255123830947442072008453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 277770566907515056811387989 3255123830947442072008453)
                      ·
                        rfl

theorem cell23_6339331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_6339331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339331 prefixEnd_6339331 := by exact prefixLift 6339331
  have htrace : WordTrace (prefixWord ++ tailWord_6339331) baseStart_6339331 baseEnd_6339331 := by
    simpa [prefixWord, tailWord_6339331, baseEnd_6339331] using wordTrace_append hprefix tailTrace_6339331
  have hstable : (prefixWord ++ tailWord_6339331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339331).length < 2 ^ (prefixWord ++ tailWord_6339331).sum := by decide
  have hdescent : baseEnd_6339331 < baseStart_6339331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339346 : List Nat := [3, 2, 4, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_6339346 : Nat := 118140960795 + 6339346 * 2 ^ 59
def prefixEnd_6339346 : Nat := 4983230072969 + 3 ^ 40 * 6339346 * 2
def baseEnd_6339346 : Nat := 3255131533157259513320885

theorem tailTrace_6339346 : CollatzResearch.WordTrace tailWord_6339346 prefixEnd_6339346 3255131533157259513320885 := by
  unfold tailWord_6339346
  simp only [CollatzResearch.WordTrace]
  refine ⟨57803735922909897736455473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154143295794426393963881261 57803735922909897736455473)
  ·
    refine ⟨43352801942182423302341605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57803735922909897736455473 43352801942182423302341605)
    ·
      refine ⟨8128650364159204369189051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43352801942182423302341605 8128650364159204369189051)
      ·
        refine ⟨12192975546238806553783577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8128650364159204369189051 12192975546238806553783577)
        ·
          refine ⟨9144731659679104915337683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12192975546238806553783577 9144731659679104915337683)
          ·
            refine ⟨13717097489518657373006525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9144731659679104915337683 13717097489518657373006525)
            ·
              refine ⟨5143911558569496514877447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13717097489518657373006525 5143911558569496514877447)
              ·
                refine ⟨7715867337854244772316171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5143911558569496514877447 7715867337854244772316171)
                ·
                  refine ⟨11573801006781367158474257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7715867337854244772316171 11573801006781367158474257)
                  ·
                    refine ⟨8680350755086025368855693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11573801006781367158474257 8680350755086025368855693)
                    ·
                      refine ⟨3255131533157259513320885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8680350755086025368855693 3255131533157259513320885)
                      ·
                        rfl

theorem cell23_6339346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_6339346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339346 prefixEnd_6339346 := by exact prefixLift 6339346
  have htrace : WordTrace (prefixWord ++ tailWord_6339346) baseStart_6339346 baseEnd_6339346 := by
    simpa [prefixWord, tailWord_6339346, baseEnd_6339346] using wordTrace_append hprefix tailTrace_6339346
  have hstable : (prefixWord ++ tailWord_6339346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339346).length < 2 ^ (prefixWord ++ tailWord_6339346).sum := by decide
  have hdescent : baseEnd_6339346 < baseStart_6339346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339365 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 3, 4, 2]
def baseStart_6339365 : Nat := 118140960795 + 6339365 * 2 ^ 59
def prefixEnd_6339365 : Nat := 4983230072969 + 3 ^ 40 * 6339365 * 2
def baseEnd_6339365 : Nat := 3255141289289694938983297

theorem tailTrace_6339365 : CollatzResearch.WordTrace tailWord_6339365 prefixEnd_6339365 3255141289289694938983297 := by
  unfold tailWord_6339365
  simp only [CollatzResearch.WordTrace]
  refine ⟨231215636678570757190763549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154143757785713838127175699 231215636678570757190763549)
  ·
    refine ⟨86705863754464033946536331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231215636678570757190763549 86705863754464033946536331)
    ·
      refine ⟨130058795631696050919804497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86705863754464033946536331 130058795631696050919804497)
      ·
        refine ⟨97544096723772038189853373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130058795631696050919804497 97544096723772038189853373)
        ·
          refine ⟨36579036271414514321195015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97544096723772038189853373 36579036271414514321195015)
          ·
            refine ⟨54868554407121771481792523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36579036271414514321195015 54868554407121771481792523)
            ·
              refine ⟨82302831610682657222688785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54868554407121771481792523 82302831610682657222688785)
              ·
                refine ⟨61727123708011992917016589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82302831610682657222688785 61727123708011992917016589)
                ·
                  refine ⟨23147671390504497343881221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61727123708011992917016589 23147671390504497343881221)
                  ·
                    refine ⟨4340188385719593251977729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23147671390504497343881221 4340188385719593251977729)
                    ·
                      refine ⟨3255141289289694938983297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4340188385719593251977729 3255141289289694938983297)
                      ·
                        rfl

theorem cell23_6339365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_6339365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339365 prefixEnd_6339365 := by exact prefixLift 6339365
  have htrace : WordTrace (prefixWord ++ tailWord_6339365) baseStart_6339365 baseEnd_6339365 := by
    simpa [prefixWord, tailWord_6339365, baseEnd_6339365] using wordTrace_append hprefix tailTrace_6339365
  have hstable : (prefixWord ++ tailWord_6339365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339365).length < 2 ^ (prefixWord ++ tailWord_6339365).sum := by decide
  have hdescent : baseEnd_6339365 < baseStart_6339365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339415 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 3]
def baseStart_6339415 : Nat := 118140960795 + 6339415 * 2 ^ 59
def prefixEnd_6339415 : Nat := 4983230072969 + 3 ^ 40 * 6339415 * 2
def baseEnd_6339415 : Nat := 3255166963322419743358067

theorem tailTrace_6339415 : CollatzResearch.WordTrace tailWord_6339415 prefixEnd_6339415 3255166963322419743358067 := by
  unfold tailWord_6339415
  simp only [CollatzResearch.WordTrace]
  refine ⟨231217460328389615730083699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154144973552259743820055799 231217460328389615730083699)
  ·
    refine ⟨346826190492584423595125549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231217460328389615730083699 346826190492584423595125549)
    ·
      refine ⟨130059821434719158848172081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346826190492584423595125549 130059821434719158848172081)
      ·
        refine ⟨97544866076039369136129061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130059821434719158848172081 97544866076039369136129061)
        ·
          refine ⟨18289662389257381713024199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97544866076039369136129061 18289662389257381713024199)
          ·
            refine ⟨27434493583886072569536299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18289662389257381713024199 27434493583886072569536299)
            ·
              refine ⟨41151740375829108854304449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27434493583886072569536299 41151740375829108854304449)
              ·
                refine ⟨30863805281871831640728337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41151740375829108854304449 30863805281871831640728337)
                ·
                  refine ⟨23147853961403873730546253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30863805281871831640728337 23147853961403873730546253)
                  ·
                    refine ⟨8680445235526452648954845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23147853961403873730546253 8680445235526452648954845)
                    ·
                      refine ⟨3255166963322419743358067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8680445235526452648954845 3255166963322419743358067)
                      ·
                        rfl

theorem cell23_6339415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_6339415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339415 prefixEnd_6339415 := by exact prefixLift 6339415
  have htrace : WordTrace (prefixWord ++ tailWord_6339415) baseStart_6339415 baseEnd_6339415 := by
    simpa [prefixWord, tailWord_6339415, baseEnd_6339415] using wordTrace_append hprefix tailTrace_6339415
  have hstable : (prefixWord ++ tailWord_6339415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339415).length < 2 ^ (prefixWord ++ tailWord_6339415).sum := by decide
  have hdescent : baseEnd_6339415 < baseStart_6339415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339425 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 2, 5, 2]
def baseStart_6339425 : Nat := 118140960795 + 6339425 * 2 ^ 59
def prefixEnd_6339425 : Nat := 4983230072969 + 3 ^ 40 * 6339425 * 2
def baseEnd_6339425 : Nat := 3255172098128964704233021

theorem tailTrace_6339425 : CollatzResearch.WordTrace tailWord_6339425 prefixEnd_6339425 3255172098128964704233021 := by
  unfold tailWord_6339425
  simp only [CollatzResearch.WordTrace]
  refine ⟨231217825058353387437947729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154145216705568924958631819 231217825058353387437947729)
  ·
    refine ⟨173413368793765040578460797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231217825058353387437947729 173413368793765040578460797)
    ·
      refine ⟨65030013297661890216922799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173413368793765040578460797 65030013297661890216922799)
      ·
        refine ⟨97545019946492835325384199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65030013297661890216922799 97545019946492835325384199)
        ·
          refine ⟨146317529919739252988076299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97545019946492835325384199 146317529919739252988076299)
          ·
            refine ⟨219476294879608879482114449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146317529919739252988076299 219476294879608879482114449)
            ·
              refine ⟨164607221159706659611585837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219476294879608879482114449 164607221159706659611585837)
              ·
                refine ⟨61727707934889997354344689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164607221159706659611585837 61727707934889997354344689)
                ·
                  refine ⟨46295780951167498015758517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61727707934889997354344689 46295780951167498015758517)
                  ·
                    refine ⟨4340229464171952938977361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46295780951167498015758517 4340229464171952938977361)
                    ·
                      refine ⟨3255172098128964704233021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4340229464171952938977361 3255172098128964704233021)
                      ·
                        rfl

theorem cell23_6339425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_6339425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339425 prefixEnd_6339425 := by exact prefixLift 6339425
  have htrace : WordTrace (prefixWord ++ tailWord_6339425) baseStart_6339425 baseEnd_6339425 := by
    simpa [prefixWord, tailWord_6339425, baseEnd_6339425] using wordTrace_append hprefix tailTrace_6339425
  have hstable : (prefixWord ++ tailWord_6339425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339425).length < 2 ^ (prefixWord ++ tailWord_6339425).sum := by decide
  have hdescent : baseEnd_6339425 < baseStart_6339425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339455 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 1, 6, 2]
def baseStart_6339455 : Nat := 118140960795 + 6339455 * 2 ^ 59
def prefixEnd_6339455 : Nat := 4983230072969 + 3 ^ 40 * 6339455 * 2
def baseEnd_6339455 : Nat := 3255187502548599586857883

theorem tailTrace_6339455 : CollatzResearch.WordTrace tailWord_6339455 prefixEnd_6339455 3255187502548599586857883 := by
  unfold tailWord_6339455
  simp only [CollatzResearch.WordTrace]
  refine ⟨231218919248244702561539819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154145946165496468374359879 231218919248244702561539819)
  ·
    refine ⟨346828378872367053842309729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231218919248244702561539819 346828378872367053842309729)
    ·
      refine ⟨260121284154275290381732297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346828378872367053842309729 260121284154275290381732297)
      ·
        refine ⟨195090963115706467786299223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260121284154275290381732297 195090963115706467786299223)
        ·
          refine ⟨292636444673559701679448835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195090963115706467786299223 292636444673559701679448835)
          ·
            refine ⟨438954667010339552519173253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292636444673559701679448835 438954667010339552519173253)
            ·
              refine ⟨82304000064438666097344985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 438954667010339552519173253 82304000064438666097344985)
              ·
                refine ⟨61728000048328999573008739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82304000064438666097344985 61728000048328999573008739)
                ·
                  refine ⟨92592000072493499359513109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61728000048328999573008739 92592000072493499359513109)
                  ·
                    refine ⟨4340250003398132782477177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92592000072493499359513109 4340250003398132782477177)
                    ·
                      refine ⟨3255187502548599586857883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4340250003398132782477177 3255187502548599586857883)
                      ·
                        rfl

theorem cell23_6339455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 6, 2].length) (baseStart_6339455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339455 prefixEnd_6339455 := by exact prefixLift 6339455
  have htrace : WordTrace (prefixWord ++ tailWord_6339455) baseStart_6339455 baseEnd_6339455 := by
    simpa [prefixWord, tailWord_6339455, baseEnd_6339455] using wordTrace_append hprefix tailTrace_6339455
  have hstable : (prefixWord ++ tailWord_6339455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339455).length < 2 ^ (prefixWord ++ tailWord_6339455).sum := by decide
  have hdescent : baseEnd_6339455 < baseStart_6339455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339468 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_6339468 : Nat := 118140960795 + 6339468 * 2 ^ 59
def prefixEnd_6339468 : Nat := 4983230072969 + 3 ^ 40 * 6339468 * 2
def baseEnd_6339468 : Nat := 3255194177797108035995323

theorem tailTrace_6339468 : CollatzResearch.WordTrace tailWord_6339468 prefixEnd_6339468 3255194177797108035995323 := by
  unfold tailWord_6339468
  simp only [CollatzResearch.WordTrace]
  refine ⟨115609696698598802890881529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154146262264798403854508705 115609696698598802890881529)
  ·
    refine ⟨86707272523949102168161147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115609696698598802890881529 86707272523949102168161147)
    ·
      refine ⟨130060908785923653252241721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86707272523949102168161147 130060908785923653252241721)
      ·
        refine ⟨97545681589442739939181291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130060908785923653252241721 97545681589442739939181291)
        ·
          refine ⟨146318522384164109908771937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97545681589442739939181291 146318522384164109908771937)
          ·
            refine ⟨109738891788123082431578953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146318522384164109908771937 109738891788123082431578953)
            ·
              refine ⟨82304168841092311823684215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109738891788123082431578953 82304168841092311823684215)
              ·
                refine ⟨123456253261638467735526323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82304168841092311823684215 123456253261638467735526323)
                ·
                  refine ⟨185184379892457701603289485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123456253261638467735526323 185184379892457701603289485)
                  ·
                    refine ⟨69444142459671638101233557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185184379892457701603289485 69444142459671638101233557)
                    ·
                      refine ⟨3255194177797108035995323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69444142459671638101233557 3255194177797108035995323)
                      ·
                        rfl

theorem cell23_6339468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_6339468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339468 prefixEnd_6339468 := by exact prefixLift 6339468
  have htrace : WordTrace (prefixWord ++ tailWord_6339468) baseStart_6339468 baseEnd_6339468 := by
    simpa [prefixWord, tailWord_6339468, baseEnd_6339468] using wordTrace_append hprefix tailTrace_6339468
  have hstable : (prefixWord ++ tailWord_6339468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339468).length < 2 ^ (prefixWord ++ tailWord_6339468).sum := by decide
  have hdescent : baseEnd_6339468 < baseStart_6339468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339562 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_6339562 : Nat := 118140960795 + 6339562 * 2 ^ 59
def prefixEnd_6339562 : Nat := 4983230072969 + 3 ^ 40 * 6339562 * 2
def baseEnd_6339562 : Nat := 3255242444978630668219891

theorem tailTrace_6339562 : CollatzResearch.WordTrace tailWord_6339562 prefixEnd_6339562 3255242444978630668219891 := by
  unfold tailWord_6339562
  simp only [CollatzResearch.WordTrace]
  refine ⟨57805705464714264958921235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154148547905904706557123293 57805705464714264958921235)
  ·
    refine ⟨86708558197071397438381853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57805705464714264958921235 86708558197071397438381853)
    ·
      refine ⟨32515709323901774039393195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86708558197071397438381853 32515709323901774039393195)
      ·
        refine ⟨48773563985852661059089793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32515709323901774039393195 48773563985852661059089793)
        ·
          refine ⟨36580172989389495794317345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48773563985852661059089793 36580172989389495794317345)
          ·
            refine ⟨27435129742042121845738009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36580172989389495794317345 27435129742042121845738009)
            ·
              refine ⟨20576347306531591384303507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27435129742042121845738009 20576347306531591384303507)
              ·
                refine ⟨30864520959797387076455261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20576347306531591384303507 30864520959797387076455261)
                ·
                  refine ⟨11574195359924020153670723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30864520959797387076455261 11574195359924020153670723)
                  ·
                    refine ⟨17361293039886030230506085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11574195359924020153670723 17361293039886030230506085)
                    ·
                      refine ⟨3255242444978630668219891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17361293039886030230506085 3255242444978630668219891)
                      ·
                        rfl

theorem cell23_6339562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_6339562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339562 prefixEnd_6339562 := by exact prefixLift 6339562
  have htrace : WordTrace (prefixWord ++ tailWord_6339562) baseStart_6339562 baseEnd_6339562 := by
    simpa [prefixWord, tailWord_6339562, baseEnd_6339562] using wordTrace_append hprefix tailTrace_6339562
  have hstable : (prefixWord ++ tailWord_6339562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339562).length < 2 ^ (prefixWord ++ tailWord_6339562).sum := by decide
  have hdescent : baseEnd_6339562 < baseStart_6339562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339585 : List Nat := [1, 2, 4, 1, 2, 3, 10]
def baseStart_6339585 : Nat := 118140960795 + 6339585 * 2 ^ 59
def prefixEnd_6339585 : Nat := 4983230072969 + 3 ^ 40 * 6339585 * 2
def baseEnd_6339585 : Nat := 40188324136218321953485

theorem tailTrace_6339585 : CollatzResearch.WordTrace tailWord_6339585 prefixEnd_6339585 40188324136218321953485 := by
  unfold tailWord_6339585
  simp only [CollatzResearch.WordTrace]
  refine ⟨231223660737773734763772209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154149107158515823175848139 231223660737773734763772209)
  ·
    refine ⟨173417745553330301072829157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231223660737773734763772209 173417745553330301072829157)
    ·
      refine ⟨32515827291249431451155467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173417745553330301072829157 32515827291249431451155467)
      ·
        refine ⟨48773740936874147176733201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32515827291249431451155467 48773740936874147176733201)
        ·
          refine ⟨36580305702655610382549901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48773740936874147176733201 36580305702655610382549901)
          ·
            refine ⟨13717614638495853893456213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36580305702655610382549901 13717614638495853893456213)
            ·
              refine ⟨40188324136218321953485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13717614638495853893456213 40188324136218321953485)
              ·
                rfl

theorem cell23_6339585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 10].length) (baseStart_6339585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339585 prefixEnd_6339585 := by exact prefixLift 6339585
  have htrace : WordTrace (prefixWord ++ tailWord_6339585) baseStart_6339585 baseEnd_6339585 := by
    simpa [prefixWord, tailWord_6339585, baseEnd_6339585] using wordTrace_append hprefix tailTrace_6339585
  have hstable : (prefixWord ++ tailWord_6339585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339585).length < 2 ^ (prefixWord ++ tailWord_6339585).sum := by decide
  have hdescent : baseEnd_6339585 < baseStart_6339585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339596 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 3, 2, 2]
def baseStart_6339596 : Nat := 118140960795 + 6339596 * 2 ^ 59
def prefixEnd_6339596 : Nat := 4983230072969 + 3 ^ 40 * 6339596 * 2
def baseEnd_6339596 : Nat := 3255259903320883535194735

theorem tailTrace_6339596 : CollatzResearch.WordTrace tailWord_6339596 prefixEnd_6339596 3255259903320883535194735 := by
  unfold tailWord_6339596
  simp only [CollatzResearch.WordTrace]
  refine ⟨115612030970366941821211321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154149374627155922428281761 115612030970366941821211321)
  ·
    refine ⟨86709023227775206365908491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115612030970366941821211321 86709023227775206365908491)
    ·
      refine ⟨130063534841662809548862737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86709023227775206365908491 130063534841662809548862737)
      ·
        refine ⟨97547651131247107161647053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130063534841662809548862737 97547651131247107161647053)
        ·
          refine ⟨36580369174217665185617645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97547651131247107161647053 36580369174217665185617645)
          ·
            refine ⟨13717638440331624444606617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36580369174217665185617645 13717638440331624444606617)
            ·
              refine ⟨10288228830248718333454963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13717638440331624444606617 10288228830248718333454963)
              ·
                refine ⟨15432343245373077500182445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10288228830248718333454963 15432343245373077500182445)
                ·
                  refine ⟨5787128717014904062568417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15432343245373077500182445 5787128717014904062568417)
                  ·
                    refine ⟨4340346537761178046926313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5787128717014904062568417 4340346537761178046926313)
                    ·
                      refine ⟨3255259903320883535194735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4340346537761178046926313 3255259903320883535194735)
                      ·
                        rfl

theorem cell23_6339596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_6339596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339596 prefixEnd_6339596 := by exact prefixLift 6339596
  have htrace : WordTrace (prefixWord ++ tailWord_6339596) baseStart_6339596 baseEnd_6339596 := by
    simpa [prefixWord, tailWord_6339596, baseEnd_6339596] using wordTrace_append hprefix tailTrace_6339596
  have hstable : (prefixWord ++ tailWord_6339596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339596).length < 2 ^ (prefixWord ++ tailWord_6339596).sum := by decide
  have hdescent : baseEnd_6339596 < baseStart_6339596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339635 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 4]
def baseStart_6339635 : Nat := 118140960795 + 6339635 * 2 ^ 59
def prefixEnd_6339635 : Nat := 4983230072969 + 3 ^ 40 * 6339635 * 2
def baseEnd_6339635 : Nat := 3255279929066408882607055

theorem tailTrace_6339635 : CollatzResearch.WordTrace tailWord_6339635 prefixEnd_6339635 3255279929066408882607055 := by
  unfold tailWord_6339635
  simp only [CollatzResearch.WordTrace]
  refine ⟨231225484387592593303092359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154150322925061728868728239 231225484387592593303092359)
  ·
    refine ⟨346838226581388889954638539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231225484387592593303092359 346838226581388889954638539)
    ·
      refine ⟨520257339872083334931957809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346838226581388889954638539 520257339872083334931957809)
      ·
        refine ⟨390193004904062501198968357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520257339872083334931957809 390193004904062501198968357)
        ·
          refine ⟨73161188419511718974806567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 390193004904062501198968357 73161188419511718974806567)
          ·
            refine ⟨109741782629267578462209851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73161188419511718974806567 109741782629267578462209851)
            ·
              refine ⟨164612673943901367693314777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109741782629267578462209851 164612673943901367693314777)
              ·
                refine ⟨123459505457926025769986083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164612673943901367693314777 123459505457926025769986083)
                ·
                  refine ⟨185189258186889038654979125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123459505457926025769986083 185189258186889038654979125)
                  ·
                    refine ⟨17361492955020847373904293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 185189258186889038654979125 17361492955020847373904293)
                    ·
                      refine ⟨3255279929066408882607055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17361492955020847373904293 3255279929066408882607055)
                      ·
                        rfl

theorem cell23_6339635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_6339635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339635 prefixEnd_6339635 := by exact prefixLift 6339635
  have htrace : WordTrace (prefixWord ++ tailWord_6339635) baseStart_6339635 baseEnd_6339635 := by
    simpa [prefixWord, tailWord_6339635, baseEnd_6339635] using wordTrace_append hprefix tailTrace_6339635
  have hstable : (prefixWord ++ tailWord_6339635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339635).length < 2 ^ (prefixWord ++ tailWord_6339635).sum := by decide
  have hdescent : baseEnd_6339635 < baseStart_6339635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339646 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_6339646 : Nat := 118140960795 + 6339646 * 2 ^ 59
def prefixEnd_6339646 : Nat := 4983230072969 + 3 ^ 40 * 6339646 * 2
def baseEnd_6339646 : Nat := 3255285577353608339569505

theorem tailTrace_6339646 : CollatzResearch.WordTrace tailWord_6339646 prefixEnd_6339646 3255285577353608339569505 := by
  unfold tailWord_6339646
  simp only [CollatzResearch.WordTrace]
  refine ⟨28903235698819092772717849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154150590393701828121161861 28903235698819092772717849)
  ·
    refine ⟨21677426774114319579538387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28903235698819092772717849 21677426774114319579538387)
    ·
      refine ⟨32516140161171479369307581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21677426774114319579538387 32516140161171479369307581)
      ·
        refine ⟨12193552560439304763490343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32516140161171479369307581 12193552560439304763490343)
        ·
          refine ⟨18290328840658957145235515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12193552560439304763490343 18290328840658957145235515)
          ·
            refine ⟨27435493260988435717853273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18290328840658957145235515 27435493260988435717853273)
            ·
              refine ⟨20576619945741326788389955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27435493260988435717853273 20576619945741326788389955)
              ·
                refine ⟨30864929918611990182584933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20576619945741326788389955 30864929918611990182584933)
                ·
                  refine ⟨5787174359739748159234675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30864929918611990182584933 5787174359739748159234675)
                  ·
                    refine ⟨8680761539609622238852013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5787174359739748159234675 8680761539609622238852013)
                    ·
                      refine ⟨3255285577353608339569505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8680761539609622238852013 3255285577353608339569505)
                      ·
                        rfl

theorem cell23_6339646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_6339646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339646 prefixEnd_6339646 := by exact prefixLift 6339646
  have htrace : WordTrace (prefixWord ++ tailWord_6339646) baseStart_6339646 baseEnd_6339646 := by
    simpa [prefixWord, tailWord_6339646, baseEnd_6339646] using wordTrace_append hprefix tailTrace_6339646
  have hstable : (prefixWord ++ tailWord_6339646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339646).length < 2 ^ (prefixWord ++ tailWord_6339646).sum := by decide
  have hdescent : baseEnd_6339646 < baseStart_6339646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339669 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 1, 4, 2]
def baseStart_6339669 : Nat := 118140960795 + 6339669 * 2 ^ 59
def prefixEnd_6339669 : Nat := 4983230072969 + 3 ^ 40 * 6339669 * 2
def baseEnd_6339669 : Nat := 3255297387408661749581899

theorem tailTrace_6339669 : CollatzResearch.WordTrace tailWord_6339669 prefixEnd_6339669 3255297387408661749581899 := by
  unfold tailWord_6339669
  simp only [CollatzResearch.WordTrace]
  refine ⟨231226724469469417109830061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154151149646312944739886707 231226724469469417109830061)
  ·
    refine ⟨86710021676051031416186273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231226724469469417109830061 86710021676051031416186273)
    ·
      refine ⟨65032516257038273562139705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86710021676051031416186273 65032516257038273562139705)
      ·
        refine ⟨48774387192778705171604779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65032516257038273562139705 48774387192778705171604779)
        ·
          refine ⟨73161580789168057757407169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48774387192778705171604779 73161580789168057757407169)
          ·
            refine ⟨54871185591876043318055377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73161580789168057757407169 54871185591876043318055377)
            ·
              refine ⟨41153389193907032488541533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54871185591876043318055377 41153389193907032488541533)
              ·
                refine ⟨15432520947715137183203075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41153389193907032488541533 15432520947715137183203075)
                ·
                  refine ⟨23148781421572705774804613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15432520947715137183203075 23148781421572705774804613)
                  ·
                    refine ⟨4340396516544882332775865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23148781421572705774804613 4340396516544882332775865)
                    ·
                      refine ⟨3255297387408661749581899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4340396516544882332775865 3255297387408661749581899)
                      ·
                        rfl

theorem cell23_6339669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_6339669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339669 prefixEnd_6339669 := by exact prefixLift 6339669
  have htrace : WordTrace (prefixWord ++ tailWord_6339669) baseStart_6339669 baseEnd_6339669 := by
    simpa [prefixWord, tailWord_6339669, baseEnd_6339669] using wordTrace_append hprefix tailTrace_6339669
  have hstable : (prefixWord ++ tailWord_6339669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339669).length < 2 ^ (prefixWord ++ tailWord_6339669).sum := by decide
  have hdescent : baseEnd_6339669 < baseStart_6339669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339709 : List Nat := [1, 4, 1, 1, 3, 1, 3, 4, 5]
def baseStart_6339709 : Nat := 118140960795 + 6339709 * 2 ^ 59
def prefixEnd_6339709 : Nat := 4983230072969 + 3 ^ 40 * 6339709 * 2
def baseEnd_6339709 : Nat := 361701991848315732564635

theorem tailTrace_6339709 : CollatzResearch.WordTrace tailWord_6339709 prefixEnd_6339709 361701991848315732564635 := by
  unfold tailWord_6339709
  simp only [CollatzResearch.WordTrace]
  refine ⟨231228183389324503941286181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154152122259549669294190787 231228183389324503941286181)
  ·
    refine ⟨43355284385498344488991159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231228183389324503941286181 43355284385498344488991159)
    ·
      refine ⟨65032926578247516733486739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43355284385498344488991159 65032926578247516733486739)
      ·
        refine ⟨97549389867371275100230109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65032926578247516733486739 97549389867371275100230109)
        ·
          refine ⟨36581021200264228162586291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97549389867371275100230109 36581021200264228162586291)
          ·
            refine ⟨54871531800396342243879437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36581021200264228162586291 54871531800396342243879437)
            ·
              refine ⟨20576824425148628341454789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54871531800396342243879437 20576824425148628341454789)
              ·
                refine ⟨3858154579715367814022773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20576824425148628341454789 3858154579715367814022773)
                ·
                  refine ⟨361701991848315732564635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3858154579715367814022773 361701991848315732564635)
                  ·
                    rfl

theorem cell23_6339709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_6339709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339709 prefixEnd_6339709 := by exact prefixLift 6339709
  have htrace : WordTrace (prefixWord ++ tailWord_6339709) baseStart_6339709 baseEnd_6339709 := by
    simpa [prefixWord, tailWord_6339709, baseEnd_6339709] using wordTrace_append hprefix tailTrace_6339709
  have hstable : (prefixWord ++ tailWord_6339709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339709).length < 2 ^ (prefixWord ++ tailWord_6339709).sum := by decide
  have hdescent : baseEnd_6339709 < baseStart_6339709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339722 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 1, 7]
def baseStart_6339722 : Nat := 118140960795 + 6339722 * 2 ^ 59
def prefixEnd_6339722 : Nat := 4983230072969 + 3 ^ 40 * 6339722 * 2
def baseEnd_6339722 : Nat := 1085108200627783347406385

theorem tailTrace_6339722 : CollatzResearch.WordTrace tailWord_6339722 prefixEnd_6339722 1085108200627783347406385 := by
  unfold tailWord_6339722
  simp only [CollatzResearch.WordTrace]
  refine ⟨57807164384569351790377355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154152438358851604774339613 57807164384569351790377355)
  ·
    refine ⟨86710746576854027685566033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57807164384569351790377355 86710746576854027685566033)
    ·
      refine ⟨65033059932640520764174525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86710746576854027685566033 65033059932640520764174525)
      ·
        refine ⟨24387397474740195286565447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65033059932640520764174525 24387397474740195286565447)
        ·
          refine ⟨36581096212110292929848171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24387397474740195286565447 36581096212110292929848171)
          ·
            refine ⟨54871644318165439394772257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36581096212110292929848171 54871644318165439394772257)
            ·
              refine ⟨41153733238624079546079193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54871644318165439394772257 41153733238624079546079193)
              ·
                refine ⟨30865299928968059659559395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41153733238624079546079193 30865299928968059659559395)
                ·
                  refine ⟨46297949893452089489339093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30865299928968059659559395 46297949893452089489339093)
                  ·
                    refine ⟨1085108200627783347406385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46297949893452089489339093 1085108200627783347406385)
                    ·
                      rfl

theorem cell23_6339722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_6339722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339722 prefixEnd_6339722 := by exact prefixLift 6339722
  have htrace : WordTrace (prefixWord ++ tailWord_6339722) baseStart_6339722 baseEnd_6339722 := by
    simpa [prefixWord, tailWord_6339722, baseEnd_6339722] using wordTrace_append hprefix tailTrace_6339722
  have hstable : (prefixWord ++ tailWord_6339722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339722).length < 2 ^ (prefixWord ++ tailWord_6339722).sum := by decide
  have hdescent : baseEnd_6339722 < baseStart_6339722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339759 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 2, 4, 2]
def baseStart_6339759 : Nat := 118140960795 + 6339759 * 2 ^ 59
def prefixEnd_6339759 : Nat := 4983230072969 + 3 ^ 40 * 6339759 * 2
def baseEnd_6339759 : Nat := 3255343600667566397456485

theorem tailTrace_6339759 : CollatzResearch.WordTrace tailWord_6339759 prefixEnd_6339759 3255343600667566397456485 := by
  unfold tailWord_6339759
  simp only [CollatzResearch.WordTrace]
  refine ⟨231230007039143362480606331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154153338026095574987070887 231230007039143362480606331)
  ·
    refine ⟨346845010558715043720909497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231230007039143362480606331 346845010558715043720909497)
    ·
      refine ⟨260133757919036282790682123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346845010558715043720909497 260133757919036282790682123)
      ·
        refine ⟨390200636878554424186023185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260133757919036282790682123 390200636878554424186023185)
        ·
          refine ⟨292650477658915818139517389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390200636878554424186023185 292650477658915818139517389)
          ·
            refine ⟨109743929122093431802319021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292650477658915818139517389 109743929122093431802319021)
            ·
              refine ⟨41153973420785036925869633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109743929122093431802319021 41153973420785036925869633)
              ·
                refine ⟨30865480065588777694402225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41153973420785036925869633 30865480065588777694402225)
                ·
                  refine ⟨23149110049191583270801669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30865480065588777694402225 23149110049191583270801669)
                  ·
                    refine ⟨4340458134223421863275313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23149110049191583270801669 4340458134223421863275313)
                    ·
                      refine ⟨3255343600667566397456485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4340458134223421863275313 3255343600667566397456485)
                      ·
                        rfl

theorem cell23_6339759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 4, 2].length) (baseStart_6339759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339759 prefixEnd_6339759 := by exact prefixLift 6339759
  have htrace : WordTrace (prefixWord ++ tailWord_6339759) baseStart_6339759 baseEnd_6339759 := by
    simpa [prefixWord, tailWord_6339759, baseEnd_6339759] using wordTrace_append hprefix tailTrace_6339759
  have hstable : (prefixWord ++ tailWord_6339759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339759).length < 2 ^ (prefixWord ++ tailWord_6339759).sum := by decide
  have hdescent : baseEnd_6339759 < baseStart_6339759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339769 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 3, 4]
def baseStart_6339769 : Nat := 118140960795 + 6339769 * 2 ^ 59
def prefixEnd_6339769 : Nat := 4983230072969 + 3 ^ 40 * 6339769 * 2
def baseEnd_6339769 : Nat := 1085116245158037119443813

theorem tailTrace_6339769 : CollatzResearch.WordTrace tailWord_6339769 prefixEnd_6339769 1085116245158037119443813 := by
  unfold tailWord_6339769
  simp only [CollatzResearch.WordTrace]
  refine ⟨231230371769107134188470361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154153581179404756125646907 231230371769107134188470361)
  ·
    refine ⟨173422778826830350641352771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231230371769107134188470361 173422778826830350641352771)
    ·
      refine ⟨260134168240245525962029157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173422778826830350641352771 260134168240245525962029157)
      ·
        refine ⟨48775156545046036117880467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260134168240245525962029157 48775156545046036117880467)
        ·
          refine ⟨73162734817569054176820701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48775156545046036117880467 73162734817569054176820701)
          ·
            refine ⟨27436025556588395316307763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73162734817569054176820701 27436025556588395316307763)
            ·
              refine ⟨41154038334882592974461645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27436025556588395316307763 41154038334882592974461645)
              ·
                refine ⟨15432764375580972365423117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41154038334882592974461645 15432764375580972365423117)
                ·
                  refine ⟨5787286640842864637033669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15432764375580972365423117 5787286640842864637033669)
                  ·
                    refine ⟨1085116245158037119443813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5787286640842864637033669 1085116245158037119443813)
                    ·
                      rfl

theorem cell23_6339769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 4].length) (baseStart_6339769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339769 prefixEnd_6339769 := by exact prefixLift 6339769
  have htrace : WordTrace (prefixWord ++ tailWord_6339769) baseStart_6339769 baseEnd_6339769 := by
    simpa [prefixWord, tailWord_6339769, baseEnd_6339769] using wordTrace_append hprefix tailTrace_6339769
  have hstable : (prefixWord ++ tailWord_6339769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339769).length < 2 ^ (prefixWord ++ tailWord_6339769).sum := by decide
  have hdescent : baseEnd_6339769 < baseStart_6339769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339832 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_6339832 : Nat := 118140960795 + 6339832 * 2 ^ 59
def prefixEnd_6339832 : Nat := 4983230072969 + 3 ^ 40 * 6339832 * 2
def baseEnd_6339832 : Nat := 3255381084755344611843649

theorem tailTrace_6339832 : CollatzResearch.WordTrace tailWord_6339832 prefixEnd_6339832 3255381084755344611843649 := by
  unfold tailWord_6339832
  simp only [CollatzResearch.WordTrace]
  refine ⟨115616334783939447974006875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154155113045252597298675833 115616334783939447974006875)
  ·
    refine ⟨173424502175909171961010313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115616334783939447974006875 173424502175909171961010313)
    ·
      refine ⟨130068376631931878970757735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173424502175909171961010313 130068376631931878970757735)
      ·
        refine ⟨195102564947897818456136603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130068376631931878970757735 195102564947897818456136603)
        ·
          refine ⟨292653847421846727684204905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195102564947897818456136603 292653847421846727684204905)
          ·
            refine ⟨219490385566385045763153679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292653847421846727684204905 219490385566385045763153679)
            ·
              refine ⟨329235578349577568644730519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219490385566385045763153679 329235578349577568644730519)
              ·
                refine ⟨493853367524366352967095779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329235578349577568644730519 493853367524366352967095779)
                ·
                  refine ⟨740780051286549529450643669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 493853367524366352967095779 740780051286549529450643669)
                  ·
                    refine ⟨17362032452028504596499461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 740780051286549529450643669 17362032452028504596499461)
                    ·
                      refine ⟨3255381084755344611843649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17362032452028504596499461 3255381084755344611843649)
                      ·
                        rfl

theorem cell23_6339832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_6339832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339832 prefixEnd_6339832 := by exact prefixLift 6339832
  have htrace : WordTrace (prefixWord ++ tailWord_6339832) baseStart_6339832 baseEnd_6339832 := by
    simpa [prefixWord, tailWord_6339832, baseEnd_6339832] using wordTrace_append hprefix tailTrace_6339832
  have hstable : (prefixWord ++ tailWord_6339832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339832).length < 2 ^ (prefixWord ++ tailWord_6339832).sum := by decide
  have hdescent : baseEnd_6339832 < baseStart_6339832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339849 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 3, 1, 4]
def baseStart_6339849 : Nat := 118140960795 + 6339849 * 2 ^ 59
def prefixEnd_6339849 : Nat := 4983230072969 + 3 ^ 40 * 6339849 * 2
def baseEnd_6339849 : Nat := 3255389813926471045331071

theorem tailTrace_6339849 : CollatzResearch.WordTrace tailWord_6339849 prefixEnd_6339849 3255389813926471045331071 := by
  unfold tailWord_6339849
  simp only [CollatzResearch.WordTrace]
  refine ⟨231233289608817307851382601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154155526405878205234255067 231233289608817307851382601)
  ·
    refine ⟨173424967206612980888536951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231233289608817307851382601 173424967206612980888536951)
    ·
      refine ⟨260137450809919471332805427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173424967206612980888536951 260137450809919471332805427)
      ·
        refine ⟨390206176214879206999208141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260137450809919471332805427 390206176214879206999208141)
        ·
          refine ⟨146327316080579702624703053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390206176214879206999208141 146327316080579702624703053)
          ·
            refine ⟨54872743530217388484263645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146327316080579702624703053 54872743530217388484263645)
            ·
              refine ⟨20577278823831520681598867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54872743530217388484263645 20577278823831520681598867)
              ·
                refine ⟨30865918235747281022398301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20577278823831520681598867 30865918235747281022398301)
                ·
                  refine ⟨11574719338405230383399363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30865918235747281022398301 11574719338405230383399363)
                  ·
                    refine ⟨17362079007607845575099045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11574719338405230383399363 17362079007607845575099045)
                    ·
                      refine ⟨3255389813926471045331071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17362079007607845575099045 3255389813926471045331071)
                      ·
                        rfl

theorem cell23_6339849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_6339849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339849 prefixEnd_6339849 := by exact prefixLift 6339849
  have htrace : WordTrace (prefixWord ++ tailWord_6339849) baseStart_6339849 baseEnd_6339849 := by
    simpa [prefixWord, tailWord_6339849, baseEnd_6339849] using wordTrace_append hprefix tailTrace_6339849
  have hstable : (prefixWord ++ tailWord_6339849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339849).length < 2 ^ (prefixWord ++ tailWord_6339849).sum := by decide
  have hdescent : baseEnd_6339849 < baseStart_6339849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339872 : List Nat := [2, 1, 1, 5, 14]
def baseStart_6339872 : Nat := 118140960795 + 6339872 * 2 ^ 59
def prefixEnd_6339872 : Nat := 4983230072969 + 3 ^ 40 * 6339872 * 2
def baseEnd_6339872 : Nat := 4465571500660527373585

theorem tailTrace_6339872 : CollatzResearch.WordTrace tailWord_6339872 prefixEnd_6339872 4465571500660527373585 := by
  unfold tailWord_6339872
  simp only [CollatzResearch.WordTrace]
  refine ⟨115617064243866991389734935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154156085658489321852979913 115617064243866991389734935)
  ·
    refine ⟨173425596365800487084602403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115617064243866991389734935 173425596365800487084602403)
    ·
      refine ⟨260138394548700730626903605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173425596365800487084602403 260138394548700730626903605)
      ·
        refine ⟨24387974488940693496272213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 260138394548700730626903605 24387974488940693496272213)
        ·
          refine ⟨4465571500660527373585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 24387974488940693496272213 4465571500660527373585)
          ·
            rfl

theorem cell23_6339872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 14].length) (baseStart_6339872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339872 prefixEnd_6339872 := by exact prefixLift 6339872
  have htrace : WordTrace (prefixWord ++ tailWord_6339872) baseStart_6339872 baseEnd_6339872 := by
    simpa [prefixWord, tailWord_6339872, baseEnd_6339872] using wordTrace_append hprefix tailTrace_6339872
  have hstable : (prefixWord ++ tailWord_6339872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339872).length < 2 ^ (prefixWord ++ tailWord_6339872).sum := by decide
  have hdescent : baseEnd_6339872 < baseStart_6339872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339877 : List Nat := [1, 3, 1, 2, 4, 3, 2, 2, 1, 1, 3]
def baseStart_6339877 : Nat := 118140960795 + 6339877 * 2 ^ 59
def prefixEnd_6339877 : Nat := 4983230072969 + 3 ^ 40 * 6339877 * 2
def baseEnd_6339877 : Nat := 3255404191384796935780943

theorem tailTrace_6339877 : CollatzResearch.WordTrace tailWord_6339877 prefixEnd_6339877 3255404191384796935780943 := by
  unfold tailWord_6339877
  simp only [CollatzResearch.WordTrace]
  refine ⟨231234310852715868633401885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154156207235143912422267923 231234310852715868633401885)
  ·
    refine ⟨86712866569768450737525707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231234310852715868633401885 86712866569768450737525707)
    ·
      refine ⟨130069299854652676106288561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86712866569768450737525707 130069299854652676106288561)
      ·
        refine ⟨97551974890989507079716421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130069299854652676106288561 97551974890989507079716421)
        ·
          refine ⟨18290995292060532577446829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97551974890989507079716421 18290995292060532577446829)
          ·
            refine ⟨6859123234522699716542561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18290995292060532577446829 6859123234522699716542561)
            ·
              refine ⟨5144342425892024787406921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6859123234522699716542561 5144342425892024787406921)
              ·
                refine ⟨3858256819419018590555191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5144342425892024787406921 3858256819419018590555191)
                ·
                  refine ⟨5787385229128527885832787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858256819419018590555191 5787385229128527885832787)
                  ·
                    refine ⟨8681077843692791828749181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5787385229128527885832787 8681077843692791828749181)
                    ·
                      refine ⟨3255404191384796935780943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8681077843692791828749181 3255404191384796935780943)
                      ·
                        rfl

theorem cell23_6339877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_6339877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339877 prefixEnd_6339877 := by exact prefixLift 6339877
  have htrace : WordTrace (prefixWord ++ tailWord_6339877) baseStart_6339877 baseEnd_6339877 := by
    simpa [prefixWord, tailWord_6339877, baseEnd_6339877] using wordTrace_append hprefix tailTrace_6339877
  have hstable : (prefixWord ++ tailWord_6339877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339877).length < 2 ^ (prefixWord ++ tailWord_6339877).sum := by decide
  have hdescent : baseEnd_6339877 < baseStart_6339877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339889 : List Nat := [1, 2, 2, 3, 3, 1, 3, 8]
def baseStart_6339889 : Nat := 118140960795 + 6339889 * 2 ^ 59
def prefixEnd_6339889 : Nat := 4983230072969 + 3 ^ 40 * 6339889 * 2
def baseEnd_6339889 : Nat := 120570753820468551438181

theorem tailTrace_6339889 : CollatzResearch.WordTrace tailWord_6339889 prefixEnd_6339889 120570753820468551438181 := by
  unfold tailWord_6339889
  simp only [CollatzResearch.WordTrace]
  refine ⟨231234748528672394682838721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154156499019114929788559147 231234748528672394682838721)
  ·
    refine ⟨173426061396504296012129041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231234748528672394682838721 173426061396504296012129041)
    ·
      refine ⟨130069546047378222009096781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173426061396504296012129041 130069546047378222009096781)
      ·
        refine ⟨48776079767766833253411293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130069546047378222009096781 48776079767766833253411293)
        ·
          refine ⟨18291029912912562470029235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48776079767766833253411293 18291029912912562470029235)
          ·
            refine ⟨27436544869368843705043853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18291029912912562470029235 27436544869368843705043853)
            ·
              refine ⟨10288704326013316389391445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27436544869368843705043853 10288704326013316389391445)
              ·
                refine ⟨120570753820468551438181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10288704326013316389391445 120570753820468551438181)
                ·
                  rfl

theorem cell23_6339889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 8].length) (baseStart_6339889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339889 prefixEnd_6339889 := by exact prefixLift 6339889
  have htrace : WordTrace (prefixWord ++ tailWord_6339889) baseStart_6339889 baseEnd_6339889 := by
    simpa [prefixWord, tailWord_6339889, baseEnd_6339889] using wordTrace_append hprefix tailTrace_6339889
  have hstable : (prefixWord ++ tailWord_6339889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339889).length < 2 ^ (prefixWord ++ tailWord_6339889).sum := by decide
  have hdescent : baseEnd_6339889 < baseStart_6339889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339916 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 1, 3, 3]
def baseStart_6339916 : Nat := 118140960795 + 6339916 * 2 ^ 59
def prefixEnd_6339916 : Nat := 4983230072969 + 3 ^ 40 * 6339916 * 2
def baseEnd_6339916 : Nat := 3255424217130322283193263

theorem tailTrace_6339916 : CollatzResearch.WordTrace tailWord_6339916 prefixEnd_6339916 3255424217130322283193263 := by
  unfold tailWord_6339916
  simp only [CollatzResearch.WordTrace]
  refine ⟨115617866649787289147035801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154157155533049718862714401 115617866649787289147035801)
  ·
    refine ⟨86713399987340466860276851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115617866649787289147035801 86713399987340466860276851)
    ·
      refine ⟨130070099981010700290415277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86713399987340466860276851 130070099981010700290415277)
      ·
        refine ⟨48776287492879012608905729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130070099981010700290415277 48776287492879012608905729)
        ·
          refine ⟨36582215619659259456679297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48776287492879012608905729 36582215619659259456679297)
          ·
            refine ⟨27436661714744444592509473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36582215619659259456679297 27436661714744444592509473)
            ·
              refine ⟨20577496286058333444382105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27436661714744444592509473 20577496286058333444382105)
              ·
                refine ⟨15433122214543750083286579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20577496286058333444382105 15433122214543750083286579)
                ·
                  refine ⟨23149683321815625124929869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15433122214543750083286579 23149683321815625124929869)
                  ·
                    refine ⟨8681131245680859421848701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23149683321815625124929869 8681131245680859421848701)
                    ·
                      refine ⟨3255424217130322283193263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8681131245680859421848701 3255424217130322283193263)
                      ·
                        rfl

theorem cell23_6339916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_6339916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339916 prefixEnd_6339916 := by exact prefixLift 6339916
  have htrace : WordTrace (prefixWord ++ tailWord_6339916) baseStart_6339916 baseEnd_6339916 := by
    simpa [prefixWord, tailWord_6339916, baseEnd_6339916] using wordTrace_append hprefix tailTrace_6339916
  have hstable : (prefixWord ++ tailWord_6339916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339916).length < 2 ^ (prefixWord ++ tailWord_6339916).sum := by decide
  have hdescent : baseEnd_6339916 < baseStart_6339916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339959 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_6339959 : Nat := 118140960795 + 6339959 * 2 ^ 59
def prefixEnd_6339959 : Nat := 4983230072969 + 3 ^ 40 * 6339959 * 2
def baseEnd_6339959 : Nat := 3255446296798465614955565

theorem tailTrace_6339959 : CollatzResearch.WordTrace tailWord_6339959 prefixEnd_6339959 3255446296798465614955565 := by
  unfold tailWord_6339959
  simp only [CollatzResearch.WordTrace]
  refine ⟨231237301638418796637886931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154158201092279197758591287 231237301638418796637886931)
  ·
    refine ⟨346855952457628194956830397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231237301638418796637886931 346855952457628194956830397)
    ·
      refine ⟨130070982171610573108811399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346855952457628194956830397 130070982171610573108811399)
      ·
        refine ⟨195106473257415859663217099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130070982171610573108811399 195106473257415859663217099)
        ·
          refine ⟨292659709886123789494825649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195106473257415859663217099 292659709886123789494825649)
          ·
            refine ⟨219494782414592842121119237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292659709886123789494825649 219494782414592842121119237)
            ·
              refine ⟨41155271702736157897709857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 219494782414592842121119237 41155271702736157897709857)
              ·
                refine ⟨30866453777052118423282393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41155271702736157897709857 30866453777052118423282393)
                ·
                  refine ⟨23149840332789088817461795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30866453777052118423282393 23149840332789088817461795)
                  ·
                    refine ⟨34724760499183633226192693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23149840332789088817461795 34724760499183633226192693)
                    ·
                      refine ⟨3255446296798465614955565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34724760499183633226192693 3255446296798465614955565)
                      ·
                        rfl

theorem cell23_6339959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_6339959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339959 prefixEnd_6339959 := by exact prefixLift 6339959
  have htrace : WordTrace (prefixWord ++ tailWord_6339959) baseStart_6339959 baseEnd_6339959 := by
    simpa [prefixWord, tailWord_6339959, baseEnd_6339959] using wordTrace_append hprefix tailTrace_6339959
  have hstable : (prefixWord ++ tailWord_6339959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339959).length < 2 ^ (prefixWord ++ tailWord_6339959).sum := by decide
  have hdescent : baseEnd_6339959 < baseStart_6339959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339973 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 4, 2, 2]
def baseStart_6339973 : Nat := 118140960795 + 6339973 * 2 ^ 59
def prefixEnd_6339973 : Nat := 4983230072969 + 3 ^ 40 * 6339973 * 2
def baseEnd_6339973 : Nat := 3255453485527628560180501

theorem tailTrace_6339973 : CollatzResearch.WordTrace tailWord_6339973 prefixEnd_6339973 3255453485527628560180501 := by
  unfold tailWord_6339973
  simp only [CollatzResearch.WordTrace]
  refine ⟨231237812260368077028896573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154158541506912051352597715 231237812260368077028896573)
  ·
    refine ⟨86714179597638028885836215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231237812260368077028896573 86714179597638028885836215)
    ·
      refine ⟨130071269396457043328754323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86714179597638028885836215 130071269396457043328754323)
      ·
        refine ⟨195106904094685564993131485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130071269396457043328754323 195106904094685564993131485)
        ·
          refine ⟨73165089035507086872424307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195106904094685564993131485 73165089035507086872424307)
          ·
            refine ⟨109747633553260630308636461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73165089035507086872424307 109747633553260630308636461)
            ·
              refine ⟨41155362582472736365738673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109747633553260630308636461 41155362582472736365738673)
              ·
                refine ⟨30866521936854552274304005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41155362582472736365738673 30866521936854552274304005)
                ·
                  refine ⟨5787472863160228551432001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30866521936854552274304005 5787472863160228551432001)
                  ·
                    refine ⟨4340604647370171413574001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5787472863160228551432001 4340604647370171413574001)
                    ·
                      refine ⟨3255453485527628560180501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4340604647370171413574001 3255453485527628560180501)
                      ·
                        rfl

theorem cell23_6339973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 2, 2].length) (baseStart_6339973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339973 prefixEnd_6339973 := by exact prefixLift 6339973
  have htrace : WordTrace (prefixWord ++ tailWord_6339973) baseStart_6339973 baseEnd_6339973 := by
    simpa [prefixWord, tailWord_6339973, baseEnd_6339973] using wordTrace_append hprefix tailTrace_6339973
  have hstable : (prefixWord ++ tailWord_6339973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339973).length < 2 ^ (prefixWord ++ tailWord_6339973).sum := by decide
  have hdescent : baseEnd_6339973 < baseStart_6339973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6339976 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_6339976 : Nat := 118140960795 + 6339976 * 2 ^ 59
def prefixEnd_6339976 : Nat := 4983230072969 + 3 ^ 40 * 6339976 * 2
def baseEnd_6339976 : Nat := 3255455025969592048442987

theorem tailTrace_6339976 : CollatzResearch.WordTrace tailWord_6339976 prefixEnd_6339976 3255455025969592048442987 := by
  unfold tailWord_6339976
  simp only [CollatzResearch.WordTrace]
  refine ⟨115618960839678604270627891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154158614452904805694170521 115618960839678604270627891)
  ·
    refine ⟨173428441259517906405941837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115618960839678604270627891 173428441259517906405941837)
    ·
      refine ⟨65035665472319214902228189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173428441259517906405941837 65035665472319214902228189)
      ·
        refine ⟨24388374552119705588335571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65035665472319214902228189 24388374552119705588335571)
        ·
          refine ⟨36582561828179558382503357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24388374552119705588335571 36582561828179558382503357)
          ·
            refine ⟨13718460685567334393438759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36582561828179558382503357 13718460685567334393438759)
            ·
              refine ⟨20577691028351001590158139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13718460685567334393438759 20577691028351001590158139)
              ·
                refine ⟨30866536542526502385237209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20577691028351001590158139 30866536542526502385237209)
                ·
                  refine ⟨23149902406894876788927907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30866536542526502385237209 23149902406894876788927907)
                  ·
                    refine ⟨34724853610342315183391861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23149902406894876788927907 34724853610342315183391861)
                    ·
                      refine ⟨3255455025969592048442987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34724853610342315183391861 3255455025969592048442987)
                      ·
                        rfl

theorem cell23_6339976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_6339976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6339976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6339976 prefixEnd_6339976 := by exact prefixLift 6339976
  have htrace : WordTrace (prefixWord ++ tailWord_6339976) baseStart_6339976 baseEnd_6339976 := by
    simpa [prefixWord, tailWord_6339976, baseEnd_6339976] using wordTrace_append hprefix tailTrace_6339976
  have hstable : (prefixWord ++ tailWord_6339976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6339976).length < 2 ^ (prefixWord ++ tailWord_6339976).sum := by decide
  have hdescent : baseEnd_6339976 < baseStart_6339976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6339976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
