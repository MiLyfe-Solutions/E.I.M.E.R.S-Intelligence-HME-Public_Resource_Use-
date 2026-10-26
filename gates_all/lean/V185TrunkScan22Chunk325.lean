import V185TrunkScan22Chunk324

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2900055 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 4, 5]
def baseStart_2900055 : Nat := 118140960795 + 2900055 * 2 ^ 59
def prefixEnd_2900055 : Nat := 4983230072969 + 3 ^ 40 * 2900055 * 2
def baseEnd_2900055 : Nat := 992748092983170836783597

theorem tailTrace_2900055 : CollatzResearch.WordTrace tailWord_2900055 prefixEnd_2900055 992748092983170836783597 := by
  unfold tailWord_2900055
  simp only [CollatzResearch.WordTrace]
  refine ⟨105773695508603499807061619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70515797005735666538041079 105773695508603499807061619)
  ·
    refine ⟨158660543262905249710592429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105773695508603499807061619 158660543262905249710592429)
    ·
      refine ⟨59497703723589468641472161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158660543262905249710592429 59497703723589468641472161)
      ·
        refine ⟨44623277792692101481104121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59497703723589468641472161 44623277792692101481104121)
        ·
          refine ⟨33467458344519076110828091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44623277792692101481104121 33467458344519076110828091)
          ·
            refine ⟨50201187516778614166242137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33467458344519076110828091 50201187516778614166242137)
            ·
              refine ⟨37650890637583960624681603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50201187516778614166242137 37650890637583960624681603)
              ·
                refine ⟨56476335956375940937022405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37650890637583960624681603 56476335956375940937022405)
                ·
                  refine ⟨10589312991820488925691701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56476335956375940937022405 10589312991820488925691701)
                  ·
                    refine ⟨992748092983170836783597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10589312991820488925691701 992748092983170836783597)
                    ·
                      rfl

theorem cell22_2900055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_2900055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900055 prefixEnd_2900055 := by exact prefixLift 2900055
  have htrace : WordTrace (prefixWord ++ tailWord_2900055) baseStart_2900055 baseEnd_2900055 := by
    simpa [prefixWord, tailWord_2900055, baseEnd_2900055] using wordTrace_append hprefix tailTrace_2900055
  have hstable : (prefixWord ++ tailWord_2900055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900055).length < 2 ^ (prefixWord ++ tailWord_2900055).sum := by decide
  have hdescent : baseEnd_2900055 < baseStart_2900055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900061 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2900061 : Nat := 118140960795 + 2900061 * 2 ^ 59
def prefixEnd_2900061 : Nat := 4983230072969 + 3 ^ 40 * 2900061 * 2
def baseEnd_2900061 : Nat := 992750146905788821133579

theorem tailTrace_2900061 : CollatzResearch.WordTrace tailWord_2900061 prefixEnd_2900061 992750146905788821133579 := by
  unfold tailWord_2900061
  simp only [CollatzResearch.WordTrace]
  refine ⟨105773914346581762831780037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70515942897721175221186691 105773914346581762831780037)
  ·
    refine ⟨19832608939984080530958757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105773914346581762831780037 19832608939984080530958757)
    ·
      refine ⟨3718614176247015099554767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19832608939984080530958757 3718614176247015099554767)
      ·
        refine ⟨5577921264370522649332151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3718614176247015099554767 5577921264370522649332151)
        ·
          refine ⟨8366881896555783973998227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5577921264370522649332151 8366881896555783973998227)
          ·
            refine ⟨12550322844833675960997341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8366881896555783973998227 12550322844833675960997341)
            ·
              refine ⟨4706371066812628485374003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12550322844833675960997341 4706371066812628485374003)
              ·
                refine ⟨7059556600218942728061005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4706371066812628485374003 7059556600218942728061005)
                ·
                  refine ⟨2647333725082103523022877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7059556600218942728061005 2647333725082103523022877)
                  ·
                    refine ⟨992750146905788821133579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2647333725082103523022877 992750146905788821133579)
                    ·
                      rfl

theorem cell22_2900061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2900061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900061 prefixEnd_2900061 := by exact prefixLift 2900061
  have htrace : WordTrace (prefixWord ++ tailWord_2900061) baseStart_2900061 baseEnd_2900061 := by
    simpa [prefixWord, tailWord_2900061, baseEnd_2900061] using wordTrace_append hprefix tailTrace_2900061
  have hstable : (prefixWord ++ tailWord_2900061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900061).length < 2 ^ (prefixWord ++ tailWord_2900061).sum := by decide
  have hdescent : baseEnd_2900061 < baseStart_2900061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900074 : List Nat := [3, 1, 3, 2, 3, 1, 1, 3, 5]
def baseStart_2900074 : Nat := 118140960795 + 2900074 * 2 ^ 59
def prefixEnd_2900074 : Nat := 4983230072969 + 3 ^ 40 * 2900074 * 2
def baseEnd_2900074 : Nat := 330918199023820373519513

theorem tailTrace_2900074 : CollatzResearch.WordTrace tailWord_2900074 prefixEnd_2900074 330918199023820373519513 := by
  unfold tailWord_2900074
  simp only [CollatzResearch.WordTrace]
  refine ⟨26443597123883666513000819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70516258997023110701335517 26443597123883666513000819)
  ·
    refine ⟨39665395685825499769501229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26443597123883666513000819 39665395685825499769501229)
    ·
      refine ⟨14874523382184562413562961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39665395685825499769501229 14874523382184562413562961)
      ·
        refine ⟨11155892536638421810172221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14874523382184562413562961 11155892536638421810172221)
        ·
          refine ⟨4183459701239408178814583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11155892536638421810172221 4183459701239408178814583)
          ·
            refine ⟨6275189551859112268221875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4183459701239408178814583 6275189551859112268221875)
            ·
              refine ⟨9412784327788668402332813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6275189551859112268221875 9412784327788668402332813)
              ·
                refine ⟨3529794122920750650874805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9412784327788668402332813 3529794122920750650874805)
                ·
                  refine ⟨330918199023820373519513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3529794122920750650874805 330918199023820373519513)
                  ·
                    rfl

theorem cell22_2900074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_2900074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900074 prefixEnd_2900074 := by exact prefixLift 2900074
  have htrace : WordTrace (prefixWord ++ tailWord_2900074) baseStart_2900074 baseEnd_2900074 := by
    simpa [prefixWord, tailWord_2900074, baseEnd_2900074] using wordTrace_append hprefix tailTrace_2900074
  have hstable : (prefixWord ++ tailWord_2900074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900074).length < 2 ^ (prefixWord ++ tailWord_2900074).sum := by decide
  have hdescent : baseEnd_2900074 < baseStart_2900074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900087 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 3, 4]
def baseStart_2900087 : Nat := 118140960795 + 2900087 * 2 ^ 59
def prefixEnd_2900087 : Nat := 4983230072969 + 3 ^ 40 * 2900087 * 2
def baseEnd_2900087 : Nat := 992759047237133419983499

theorem tailTrace_2900087 : CollatzResearch.WordTrace tailWord_2900087 prefixEnd_2900087 992759047237133419983499 := by
  unfold tailWord_2900087
  simp only [CollatzResearch.WordTrace]
  refine ⟨105774862644487569272226515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70516575096325046181484343 105774862644487569272226515)
  ·
    refine ⟨158662293966731353908339773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105774862644487569272226515 158662293966731353908339773)
    ·
      refine ⟨59498360237524257715627415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158662293966731353908339773 59498360237524257715627415)
      ·
        refine ⟨89247540356286386573441123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59498360237524257715627415 89247540356286386573441123)
        ·
          refine ⟨133871310534429579860161685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89247540356286386573441123 133871310534429579860161685)
          ·
            refine ⟨6275217681301386555945079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133871310534429579860161685 6275217681301386555945079)
            ·
              refine ⟨9412826521952079833917619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6275217681301386555945079 9412826521952079833917619)
              ·
                refine ⟨14119239782928119750876429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9412826521952079833917619 14119239782928119750876429)
                ·
                  refine ⟨5294714918598044906578661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14119239782928119750876429 5294714918598044906578661)
                  ·
                    refine ⟨992759047237133419983499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5294714918598044906578661 992759047237133419983499)
                    ·
                      rfl

theorem cell22_2900087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_2900087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900087 prefixEnd_2900087 := by exact prefixLift 2900087
  have htrace : WordTrace (prefixWord ++ tailWord_2900087) baseStart_2900087 baseEnd_2900087 := by
    simpa [prefixWord, tailWord_2900087, baseEnd_2900087] using wordTrace_append hprefix tailTrace_2900087
  have hstable : (prefixWord ++ tailWord_2900087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900087).length < 2 ^ (prefixWord ++ tailWord_2900087).sum := by decide
  have hdescent : baseEnd_2900087 < baseStart_2900087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900115 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 3, 6]
def baseStart_2900115 : Nat := 118140960795 + 2900115 * 2 ^ 59
def prefixEnd_2900115 : Nat := 4983230072969 + 3 ^ 40 * 2900115 * 2
def baseEnd_2900115 : Nat := 992768632209350680283413

theorem tailTrace_2900115 : CollatzResearch.WordTrace tailWord_2900115 prefixEnd_2900115 992768632209350680283413 := by
  unfold tailWord_2900115
  simp only [CollatzResearch.WordTrace]
  refine ⟨105775883888386130054245799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70517255925590753369497199 105775883888386130054245799)
  ·
    refine ⟨158663825832579195081368699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105775883888386130054245799 158663825832579195081368699)
    ·
      refine ⟨237995738748868792622053049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158663825832579195081368699 237995738748868792622053049)
      ·
        refine ⟨178496804061651594466539787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237995738748868792622053049 178496804061651594466539787)
        ·
          refine ⟨267745206092477391699809681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178496804061651594466539787 267745206092477391699809681)
          ·
            refine ⟨200808904569358043774857261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267745206092477391699809681 200808904569358043774857261)
            ·
              refine ⟨75303339213509266415571473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200808904569358043774857261 75303339213509266415571473)
              ·
                refine ⟨56477504410131949811678605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75303339213509266415571473 56477504410131949811678605)
                ·
                  refine ⟨21179064153799481179379477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56477504410131949811678605 21179064153799481179379477)
                  ·
                    refine ⟨992768632209350680283413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21179064153799481179379477 992768632209350680283413)
                    ·
                      rfl

theorem cell22_2900115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_2900115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900115 prefixEnd_2900115 := by exact prefixLift 2900115
  have htrace : WordTrace (prefixWord ++ tailWord_2900115) baseStart_2900115 baseEnd_2900115 := by
    simpa [prefixWord, tailWord_2900115, baseEnd_2900115] using wordTrace_append hprefix tailTrace_2900115
  have hstable : (prefixWord ++ tailWord_2900115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900115).length < 2 ^ (prefixWord ++ tailWord_2900115).sum := by decide
  have hdescent : baseEnd_2900115 < baseStart_2900115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900256 : List Nat := [2, 1, 1, 5, 2, 1, 3, 2, 1, 4]
def baseStart_2900256 : Nat := 118140960795 + 2900256 * 2 ^ 59
def prefixEnd_2900256 : Nat := 4983230072969 + 3 ^ 40 * 2900256 * 2
def baseEnd_2900256 : Nat := 992816899390873312507981

theorem tailTrace_2900256 : CollatzResearch.WordTrace tailWord_2900256 prefixEnd_2900256 992816899390873312507981 := by
  unfold tailWord_2900256
  simp only [CollatzResearch.WordTrace]
  refine ⟨52890513290437655567564311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70520684387250207423419081 52890513290437655567564311)
  ·
    refine ⟨79335769935656483351346467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52890513290437655567564311 79335769935656483351346467)
    ·
      refine ⟨119003654903484725027019701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79335769935656483351346467 119003654903484725027019701)
      ·
        refine ⟨11156592647201692971283097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119003654903484725027019701 11156592647201692971283097)
        ·
          refine ⟨8367444485401269728462323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11156592647201692971283097 8367444485401269728462323)
          ·
            refine ⟨12551166728101904592693485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8367444485401269728462323 12551166728101904592693485)
            ·
              refine ⟨4706687523038214222260057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12551166728101904592693485 4706687523038214222260057)
              ·
                refine ⟨3530015642278660666695043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4706687523038214222260057 3530015642278660666695043)
                ·
                  refine ⟨5295023463417991000042565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530015642278660666695043 5295023463417991000042565)
                  ·
                    refine ⟨992816899390873312507981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5295023463417991000042565 992816899390873312507981)
                    ·
                      rfl

theorem cell22_2900256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_2900256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900256 prefixEnd_2900256 := by exact prefixLift 2900256
  have htrace : WordTrace (prefixWord ++ tailWord_2900256) baseStart_2900256 baseEnd_2900256 := by
    simpa [prefixWord, tailWord_2900256, baseEnd_2900256] using wordTrace_append hprefix tailTrace_2900256
  have hstable : (prefixWord ++ tailWord_2900256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900256).length < 2 ^ (prefixWord ++ tailWord_2900256).sum := by decide
  have hdescent : baseEnd_2900256 < baseStart_2900256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900273 : List Nat := [1, 2, 2, 3, 4, 1, 3, 1, 1, 4]
def baseStart_2900273 : Nat := 118140960795 + 2900273 * 2 ^ 59
def prefixEnd_2900273 : Nat := 4983230072969 + 3 ^ 40 * 2900273 * 2
def baseEnd_2900273 : Nat := 992822718838290934832929

theorem tailTrace_2900273 : CollatzResearch.WordTrace tailWord_2900273 prefixEnd_2900273 992822718838290934832929 := by
  unfold tailWord_2900273
  simp only [CollatzResearch.WordTrace]
  refine ⟨105781646621813723038497473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70521097747875815358998315 105781646621813723038497473)
  ·
    refine ⟨79336234966360292278873105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105781646621813723038497473 79336234966360292278873105)
    ·
      refine ⟨59502176224770219209154829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79336234966360292278873105 59502176224770219209154829)
      ·
        refine ⟨22313316084288832203433061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59502176224770219209154829 22313316084288832203433061)
        ·
          refine ⟨4183746765804156038143699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22313316084288832203433061 4183746765804156038143699)
          ·
            refine ⟨6275620148706234057215549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4183746765804156038143699 6275620148706234057215549)
            ·
              refine ⟨2353357555764837771455831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6275620148706234057215549 2353357555764837771455831)
              ·
                refine ⟨3530036333647256657183747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2353357555764837771455831 3530036333647256657183747)
                ·
                  refine ⟨5295054500470884985775621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530036333647256657183747 5295054500470884985775621)
                  ·
                    refine ⟨992822718838290934832929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5295054500470884985775621 992822718838290934832929)
                    ·
                      rfl

theorem cell22_2900273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_2900273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900273 prefixEnd_2900273 := by exact prefixLift 2900273
  have htrace : WordTrace (prefixWord ++ tailWord_2900273) baseStart_2900273 baseEnd_2900273 := by
    simpa [prefixWord, tailWord_2900273, baseEnd_2900273] using wordTrace_append hprefix tailTrace_2900273
  have hstable : (prefixWord ++ tailWord_2900273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900273).length < 2 ^ (prefixWord ++ tailWord_2900273).sum := by decide
  have hdescent : baseEnd_2900273 < baseStart_2900273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900282 : List Nat := [3, 1, 1, 1, 4, 12]
def baseStart_2900282 : Nat := 118140960795 + 2900282 * 2 ^ 59
def prefixEnd_2900282 : Nat := 4983230072969 + 3 ^ 40 * 2900282 * 2
def baseEnd_2900282 : Nat := 12257108638545900140221

theorem tailTrace_2900282 : CollatzResearch.WordTrace tailWord_2900282 prefixEnd_2900282 12257108638545900140221 := by
  unfold tailWord_2900282
  simp only [CollatzResearch.WordTrace]
  refine ⟨26445493719695279393893775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70521316585854078383716733 26445493719695279393893775)
  ·
    refine ⟨39668240579542919090840663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26445493719695279393893775 39668240579542919090840663)
    ·
      refine ⟨59502360869314378636260995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39668240579542919090840663 59502360869314378636260995)
      ·
        refine ⟨89253541303971567954391493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59502360869314378636260995 89253541303971567954391493)
        ·
          refine ⟨16735038994494668991448405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89253541303971567954391493 16735038994494668991448405)
          ·
            refine ⟨12257108638545900140221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16735038994494668991448405 12257108638545900140221)
            ·
              rfl

theorem cell22_2900282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 12].length) (baseStart_2900282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900282 prefixEnd_2900282 := by exact prefixLift 2900282
  have htrace : WordTrace (prefixWord ++ tailWord_2900282) baseStart_2900282 baseEnd_2900282 := by
    simpa [prefixWord, tailWord_2900282, baseEnd_2900282] using wordTrace_append hprefix tailTrace_2900282
  have hstable : (prefixWord ++ tailWord_2900282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900282).length < 2 ^ (prefixWord ++ tailWord_2900282).sum := by decide
  have hdescent : baseEnd_2900282 < baseStart_2900282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900284 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_2900284 : Nat := 118140960795 + 2900284 * 2 ^ 59
def prefixEnd_2900284 : Nat := 4983230072969 + 3 ^ 40 * 2900284 * 2
def baseEnd_2900284 : Nat := 992826484363090572807895

theorem tailTrace_2900284 : CollatzResearch.WordTrace tailWord_2900284 prefixEnd_2900284 992826484363090572807895 := by
  unfold tailWord_2900284
  simp only [CollatzResearch.WordTrace]
  refine ⟨52891023912386935958573953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70521365216515914611431937 52891023912386935958573953)
  ·
    refine ⟨39668267934290201968930465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52891023912386935958573953 39668267934290201968930465)
    ·
      refine ⟨29751200950717651476697849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39668267934290201968930465 29751200950717651476697849)
      ·
        refine ⟨22313400713038238607523387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29751200950717651476697849 22313400713038238607523387)
        ·
          refine ⟨33470101069557357911285081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22313400713038238607523387 33470101069557357911285081)
          ·
            refine ⟨25102575802168018433463811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33470101069557357911285081 25102575802168018433463811)
            ·
              refine ⟨37653863703252027650195717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25102575802168018433463811 37653863703252027650195717)
              ·
                refine ⟨7060099444359755184411697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37653863703252027650195717 7060099444359755184411697)
                ·
                  refine ⟨5295074583269816388308773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7060099444359755184411697 5295074583269816388308773)
                  ·
                    refine ⟨992826484363090572807895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5295074583269816388308773 992826484363090572807895)
                    ·
                      rfl

theorem cell22_2900284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_2900284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900284 prefixEnd_2900284 := by exact prefixLift 2900284
  have htrace : WordTrace (prefixWord ++ tailWord_2900284) baseStart_2900284 baseEnd_2900284 := by
    simpa [prefixWord, tailWord_2900284, baseEnd_2900284] using wordTrace_append hprefix tailTrace_2900284
  have hstable : (prefixWord ++ tailWord_2900284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900284).length < 2 ^ (prefixWord ++ tailWord_2900284).sum := by decide
  have hdescent : baseEnd_2900284 < baseStart_2900284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900297 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 2, 7]
def baseStart_2900297 : Nat := 118140960795 + 2900297 * 2 ^ 59
def prefixEnd_2900297 : Nat := 4983230072969 + 3 ^ 40 * 2900297 * 2
def baseEnd_2900297 : Nat := 992830934528762872232855

theorem tailTrace_2900297 : CollatzResearch.WordTrace tailWord_2900297 prefixEnd_2900297 992830934528762872232855 := by
  unfold tailWord_2900297
  simp only [CollatzResearch.WordTrace]
  refine ⟨105782521973726775137371145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70521681315817850091580763 105782521973726775137371145)
  ·
    refine ⟨79336891480295081353028359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105782521973726775137371145 79336891480295081353028359)
    ·
      refine ⟨119005337220442622029542539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79336891480295081353028359 119005337220442622029542539)
      ·
        refine ⟨178508005830663933044313809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119005337220442622029542539 178508005830663933044313809)
        ·
          refine ⟨133881004372997949783235357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178508005830663933044313809 133881004372997949783235357)
          ·
            refine ⟨50205376639874231168713259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133881004372997949783235357 50205376639874231168713259)
            ·
              refine ⟨75308064959811346753069889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50205376639874231168713259 75308064959811346753069889)
              ·
                refine ⟨56481048719858510064802417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75308064959811346753069889 56481048719858510064802417)
                ·
                  refine ⟨42360786539893882548601813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56481048719858510064802417 42360786539893882548601813)
                  ·
                    refine ⟨992830934528762872232855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42360786539893882548601813 992830934528762872232855)
                    ·
                      rfl

theorem cell22_2900297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_2900297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900297 prefixEnd_2900297 := by exact prefixLift 2900297
  have htrace : WordTrace (prefixWord ++ tailWord_2900297) baseStart_2900297 baseEnd_2900297 := by
    simpa [prefixWord, tailWord_2900297, baseEnd_2900297] using wordTrace_append hprefix tailTrace_2900297
  have hstable : (prefixWord ++ tailWord_2900297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900297).length < 2 ^ (prefixWord ++ tailWord_2900297).sum := by decide
  have hdescent : baseEnd_2900297 < baseStart_2900297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900359 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 2, 5]
def baseStart_2900359 : Nat := 118140960795 + 2900359 * 2 ^ 59
def prefixEnd_2900359 : Nat := 4983230072969 + 3 ^ 40 * 2900359 * 2
def baseEnd_2900359 : Nat := 992852158395815377182665

theorem tailTrace_2900359 : CollatzResearch.WordTrace tailWord_2900359 prefixEnd_2900359 992852158395815377182665 := by
  unfold tailWord_2900359
  simp only [CollatzResearch.WordTrace]
  refine ⟨105784783299502159726128131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70523188866334773150752087 105784783299502159726128131)
  ·
    refine ⟨158677174949253239589192197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105784783299502159726128131 158677174949253239589192197)
    ·
      refine ⟨29751970302984982422973537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158677174949253239589192197 29751970302984982422973537)
      ·
        refine ⟨22313977727238736817230153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29751970302984982422973537 22313977727238736817230153)
        ·
          refine ⟨16735483295429052612922615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22313977727238736817230153 16735483295429052612922615)
          ·
            refine ⟨25103224943143578919383923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16735483295429052612922615 25103224943143578919383923)
            ·
              refine ⟨37654837414715368379075885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25103224943143578919383923 37654837414715368379075885)
              ·
                refine ⟨14120564030518263142153457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37654837414715368379075885 14120564030518263142153457)
                ·
                  refine ⟨10590423022888697356615093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14120564030518263142153457 10590423022888697356615093)
                  ·
                    refine ⟨992852158395815377182665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10590423022888697356615093 992852158395815377182665)
                    ·
                      rfl

theorem cell22_2900359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_2900359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900359 prefixEnd_2900359 := by exact prefixLift 2900359
  have htrace : WordTrace (prefixWord ++ tailWord_2900359) baseStart_2900359 baseEnd_2900359 := by
    simpa [prefixWord, tailWord_2900359, baseEnd_2900359] using wordTrace_append hprefix tailTrace_2900359
  have hstable : (prefixWord ++ tailWord_2900359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900359).length < 2 ^ (prefixWord ++ tailWord_2900359).sum := by decide
  have hdescent : baseEnd_2900359 < baseStart_2900359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900382 : List Nat := [4, 3, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_2900382 : Nat := 118140960795 + 2900382 * 2 ^ 59
def prefixEnd_2900382 : Nat := 4983230072969 + 3 ^ 40 * 2900382 * 2
def baseEnd_2900382 : Nat := 992860031765850983857595

theorem tailTrace_2900382 : CollatzResearch.WordTrace tailWord_2900382 prefixEnd_2900382 992860031765850983857595 := by
  unfold tailWord_2900382
  simp only [CollatzResearch.WordTrace]
  refine ⟨13223202772302354331776925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70523748118945889769476933 13223202772302354331776925)
  ·
    refine ⟨4958701039613382874416347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13223202772302354331776925 4958701039613382874416347)
    ·
      refine ⟨7438051559420074311624521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4958701039613382874416347 7438051559420074311624521)
      ·
        refine ⟨5578538669565055733718391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7438051559420074311624521 5578538669565055733718391)
        ·
          refine ⟨8367808004347583600577587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5578538669565055733718391 8367808004347583600577587)
          ·
            refine ⟨12551712006521375400866381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8367808004347583600577587 12551712006521375400866381)
            ·
              refine ⟨4706892002445515775324893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12551712006521375400866381 4706892002445515775324893)
              ·
                refine ⟨1765084500917068415746835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4706892002445515775324893 1765084500917068415746835)
                ·
                  refine ⟨2647626751375602623620253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765084500917068415746835 2647626751375602623620253)
                  ·
                    refine ⟨992860031765850983857595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2647626751375602623620253 992860031765850983857595)
                    ·
                      rfl

theorem cell22_2900382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_2900382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900382 prefixEnd_2900382 := by exact prefixLift 2900382
  have htrace : WordTrace (prefixWord ++ tailWord_2900382) baseStart_2900382 baseEnd_2900382 := by
    simpa [prefixWord, tailWord_2900382, baseEnd_2900382] using wordTrace_append hprefix tailTrace_2900382
  have hstable : (prefixWord ++ tailWord_2900382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900382).length < 2 ^ (prefixWord ++ tailWord_2900382).sum := by decide
  have hdescent : baseEnd_2900382 < baseStart_2900382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900419 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 6, 4]
def baseStart_2900419 : Nat := 118140960795 + 2900419 * 2 ^ 59
def prefixEnd_2900419 : Nat := 4983230072969 + 3 ^ 40 * 2900419 * 2
def baseEnd_2900419 : Nat := 992872697621995220682481

theorem tailTrace_2900419 : CollatzResearch.WordTrace tailWord_2900419 prefixEnd_2900419 992872697621995220682481 := by
  unfold tailWord_2900419
  simp only [CollatzResearch.WordTrace]
  refine ⟨105786971679284789973312311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70524647786189859982208207 105786971679284789973312311)
  ·
    refine ⟨158680457518927184959968467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105786971679284789973312311 158680457518927184959968467)
    ·
      refine ⟨238020686278390777439952701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158680457518927184959968467 238020686278390777439952701)
      ·
        refine ⟨89257757354396541539982263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238020686278390777439952701 89257757354396541539982263)
        ·
          refine ⟨133886636031594812309973395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89257757354396541539982263 133886636031594812309973395)
          ·
            refine ⟨200829954047392218464960093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133886636031594812309973395 200829954047392218464960093)
            ·
              refine ⟨75311232767772081924360035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200829954047392218464960093 75311232767772081924360035)
              ·
                refine ⟨112966849151658122886540053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75311232767772081924360035 112966849151658122886540053)
                ·
                  refine ⟨5295321053983974510306565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112966849151658122886540053 5295321053983974510306565)
                  ·
                    refine ⟨992872697621995220682481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5295321053983974510306565 992872697621995220682481)
                    ·
                      rfl

theorem cell22_2900419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 4].length) (baseStart_2900419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900419 prefixEnd_2900419 := by exact prefixLift 2900419
  have htrace : WordTrace (prefixWord ++ tailWord_2900419) baseStart_2900419 baseEnd_2900419 := by
    simpa [prefixWord, tailWord_2900419, baseEnd_2900419] using wordTrace_append hprefix tailTrace_2900419
  have hstable : (prefixWord ++ tailWord_2900419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900419).length < 2 ^ (prefixWord ++ tailWord_2900419).sum := by decide
  have hdescent : baseEnd_2900419 < baseStart_2900419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900438 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2900438 : Nat := 118140960795 + 2900438 * 2 ^ 59
def prefixEnd_2900438 : Nat := 4983230072969 + 3 ^ 40 * 2900438 * 2
def baseEnd_2900438 : Nat := 992879201710285504457423

theorem tailTrace_2900438 : CollatzResearch.WordTrace tailWord_2900438 prefixEnd_2900438 992879201710285504457423 := by
  unfold tailWord_2900438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6611729041638497263640873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70525109777477304145502645 6611729041638497263640873)
  ·
    refine ⟨4958796781228872947730655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6611729041638497263640873 4958796781228872947730655)
    ·
      refine ⟨7438195171843309421595983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4958796781228872947730655 7438195171843309421595983)
      ·
        refine ⟨11157292757764964132393975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7438195171843309421595983 11157292757764964132393975)
        ·
          refine ⟨16735939136647446198590963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11157292757764964132393975 16735939136647446198590963)
          ·
            refine ⟨25103908704971169297886445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16735939136647446198590963 25103908704971169297886445)
            ·
              refine ⟨9413965764364188486707417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25103908704971169297886445 9413965764364188486707417)
              ·
                refine ⟨7060474323273141365030563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9413965764364188486707417 7060474323273141365030563)
                ·
                  refine ⟨10590711484909712047545845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7060474323273141365030563 10590711484909712047545845)
                  ·
                    refine ⟨992879201710285504457423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10590711484909712047545845 992879201710285504457423)
                    ·
                      rfl

theorem cell22_2900438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2900438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900438 prefixEnd_2900438 := by exact prefixLift 2900438
  have htrace : WordTrace (prefixWord ++ tailWord_2900438) baseStart_2900438 baseEnd_2900438 := by
    simpa [prefixWord, tailWord_2900438, baseEnd_2900438] using wordTrace_append hprefix tailTrace_2900438
  have hstable : (prefixWord ++ tailWord_2900438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900438).length < 2 ^ (prefixWord ++ tailWord_2900438).sum := by decide
  have hdescent : baseEnd_2900438 < baseStart_2900438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900451 : List Nat := [1, 1, 1, 6, 4, 9]
def baseStart_2900451 : Nat := 118140960795 + 2900451 * 2 ^ 59
def prefixEnd_2900451 : Nat := 4983230072969 + 3 ^ 40 * 2900451 * 2
def baseEnd_2900451 : Nat := 12257822862666145726943

theorem tailTrace_2900451 : CollatzResearch.WordTrace tailWord_2900451 prefixEnd_2900451 12257822862666145726943 := by
  unfold tailWord_2900451
  simp only [CollatzResearch.WordTrace]
  refine ⟨105788138815168859438477207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70525425876779239625651471 105788138815168859438477207)
  ·
    refine ⟨158682208222753289157715811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105788138815168859438477207 158682208222753289157715811)
    ·
      refine ⟨238023312334129933736573717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158682208222753289157715811 238023312334129933736573717)
      ·
        refine ⟨11157342765662340643901893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 238023312334129933736573717 11157342765662340643901893)
        ·
          refine ⟨2092001768561688870731605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11157342765662340643901893 2092001768561688870731605)
          ·
            refine ⟨12257822862666145726943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2092001768561688870731605 12257822862666145726943)
            ·
              rfl

theorem cell22_2900451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 9].length) (baseStart_2900451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900451 prefixEnd_2900451 := by exact prefixLift 2900451
  have htrace : WordTrace (prefixWord ++ tailWord_2900451) baseStart_2900451 baseEnd_2900451 := by
    simpa [prefixWord, tailWord_2900451, baseEnd_2900451] using wordTrace_append hprefix tailTrace_2900451
  have hstable : (prefixWord ++ tailWord_2900451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900451).length < 2 ^ (prefixWord ++ tailWord_2900451).sum := by decide
  have hdescent : baseEnd_2900451 < baseStart_2900451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900464 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 1, 8]
def baseStart_2900464 : Nat := 118140960795 + 2900464 * 2 ^ 59
def prefixEnd_2900464 : Nat := 4983230072969 + 3 ^ 40 * 2900464 * 2
def baseEnd_2900464 : Nat := 992888102041630103307343

theorem tailTrace_2900464 : CollatzResearch.WordTrace tailWord_2900464 prefixEnd_2900464 992888102041630103307343 := by
  unfold tailWord_2900464
  simp only [CollatzResearch.WordTrace]
  refine ⟨52894306482060881329350223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70525741976081175105800297 52894306482060881329350223)
  ·
    refine ⟨79341459723091321994025335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52894306482060881329350223 79341459723091321994025335)
    ·
      refine ⟨119012189584636982991038003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79341459723091321994025335 119012189584636982991038003)
      ·
        refine ⟨178518284376955474486557005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119012189584636982991038003 178518284376955474486557005)
        ·
          refine ⟨66944356641358302932458877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178518284376955474486557005 66944356641358302932458877)
          ·
            refine ⟨25104133740509363599672079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66944356641358302932458877 25104133740509363599672079)
            ·
              refine ⟨37656200610764045399508119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25104133740509363599672079 37656200610764045399508119)
              ·
                refine ⟨56484300916146068099262179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37656200610764045399508119 56484300916146068099262179)
                ·
                  refine ⟨84726451374219102148893269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56484300916146068099262179 84726451374219102148893269)
                  ·
                    refine ⟨992888102041630103307343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84726451374219102148893269 992888102041630103307343)
                    ·
                      rfl

theorem cell22_2900464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_2900464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900464 prefixEnd_2900464 := by exact prefixLift 2900464
  have htrace : WordTrace (prefixWord ++ tailWord_2900464) baseStart_2900464 baseEnd_2900464 := by
    simpa [prefixWord, tailWord_2900464, baseEnd_2900464] using wordTrace_append hprefix tailTrace_2900464
  have hstable : (prefixWord ++ tailWord_2900464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900464).length < 2 ^ (prefixWord ++ tailWord_2900464).sum := by decide
  have hdescent : baseEnd_2900464 < baseStart_2900464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900543 : List Nat := [1, 1, 2, 2, 3, 2, 4, 2, 1, 4]
def baseStart_2900543 : Nat := 118140960795 + 2900543 * 2 ^ 59
def prefixEnd_2900543 : Nat := 4983230072969 + 3 ^ 40 * 2900543 * 2
def baseEnd_2900543 : Nat := 992915145356100230582101

theorem tailTrace_2900543 : CollatzResearch.WordTrace tailWord_2900543 prefixEnd_2900543 992915145356100230582101 := by
  unfold tailWord_2900543
  simp only [CollatzResearch.WordTrace]
  refine ⟨105791494330835559150826283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70527662887223706100550855 105791494330835559150826283)
  ·
    refine ⟨158687241496253338726239425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105791494330835559150826283 158687241496253338726239425)
    ·
      refine ⟨119015431122190004044679569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158687241496253338726239425 119015431122190004044679569)
      ·
        refine ⟨89261573341642503033509677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119015431122190004044679569 89261573341642503033509677)
        ·
          refine ⟨33473090003115938637566129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89261573341642503033509677 33473090003115938637566129)
          ·
            refine ⟨25104817502336953978174597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33473090003115938637566129 25104817502336953978174597)
            ·
              refine ⟨4707153281688178870907737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25104817502336953978174597 4707153281688178870907737)
              ·
                refine ⟨3530364961266134153180803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4707153281688178870907737 3530364961266134153180803)
                ·
                  refine ⟨5295547441899201229771205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530364961266134153180803 5295547441899201229771205)
                  ·
                    refine ⟨992915145356100230582101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5295547441899201229771205 992915145356100230582101)
                    ·
                      rfl

theorem cell22_2900543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_2900543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900543 prefixEnd_2900543 := by exact prefixLift 2900543
  have htrace : WordTrace (prefixWord ++ tailWord_2900543) baseStart_2900543 baseEnd_2900543 := by
    simpa [prefixWord, tailWord_2900543, baseEnd_2900543] using wordTrace_append hprefix tailTrace_2900543
  have hstable : (prefixWord ++ tailWord_2900543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900543).length < 2 ^ (prefixWord ++ tailWord_2900543).sum := by decide
  have hdescent : baseEnd_2900543 < baseStart_2900543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900556 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_2900556 : Nat := 118140960795 + 2900556 * 2 ^ 59
def prefixEnd_2900556 : Nat := 4983230072969 + 3 ^ 40 * 2900556 * 2
def baseEnd_2900556 : Nat := 992919595521772530007061

theorem tailTrace_2900556 : CollatzResearch.WordTrace tailWord_2900556 prefixEnd_2900556 992919595521772530007061 := by
  unfold tailWord_2900556
  simp only [CollatzResearch.WordTrace]
  refine ⟨52895984239894231185524761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70527978986525641580699681 52895984239894231185524761)
  ·
    refine ⟨39671988179920673389143571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52895984239894231185524761 39671988179920673389143571)
    ·
      refine ⟨59507982269881010083715357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39671988179920673389143571 59507982269881010083715357)
      ·
        refine ⟨22315493351205378781393259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59507982269881010083715357 22315493351205378781393259)
        ·
          refine ⟨33473240026808068172089889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22315493351205378781393259 33473240026808068172089889)
          ·
            refine ⟨25104930020106051129067417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33473240026808068172089889 25104930020106051129067417)
            ·
              refine ⟨18828697515079538346800563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25104930020106051129067417 18828697515079538346800563)
              ·
                refine ⟨28243046272619307520200845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18828697515079538346800563 28243046272619307520200845)
                ·
                  refine ⟨10591142352232240320075317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28243046272619307520200845 10591142352232240320075317)
                  ·
                    refine ⟨992919595521772530007061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10591142352232240320075317 992919595521772530007061)
                    ·
                      rfl

theorem cell22_2900556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_2900556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900556 prefixEnd_2900556 := by exact prefixLift 2900556
  have htrace : WordTrace (prefixWord ++ tailWord_2900556) baseStart_2900556 baseEnd_2900556 := by
    simpa [prefixWord, tailWord_2900556, baseEnd_2900556] using wordTrace_append hprefix tailTrace_2900556
  have hstable : (prefixWord ++ tailWord_2900556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900556).length < 2 ^ (prefixWord ++ tailWord_2900556).sum := by decide
  have hdescent : baseEnd_2900556 < baseStart_2900556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900605 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_2900605 : Nat := 118140960795 + 2900605 * 2 ^ 59
def prefixEnd_2900605 : Nat := 4983230072969 + 3 ^ 40 * 2900605 * 2
def baseEnd_2900605 : Nat := 992936369223152735531911

theorem tailTrace_2900605 : CollatzResearch.WordTrace tailWord_2900605 prefixEnd_2900605 992936369223152735531911 := by
  unfold tailWord_2900605
  simp only [CollatzResearch.WordTrace]
  refine ⟨105793755656610943739583269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70529170437740629159722179 105793755656610943739583269)
  ·
    refine ⟨19836329185614551951171863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105793755656610943739583269 19836329185614551951171863)
    ·
      refine ⟨29754493778421827926757795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19836329185614551951171863 29754493778421827926757795)
      ·
        refine ⟨44631740667632741890136693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29754493778421827926757795 44631740667632741890136693)
        ·
          refine ⟨4184225687590569552200315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44631740667632741890136693 4184225687590569552200315)
          ·
            refine ⟨6276338531385854328300473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4184225687590569552200315 6276338531385854328300473)
            ·
              refine ⟨4707253898539390746225355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6276338531385854328300473 4707253898539390746225355)
              ·
                refine ⟨7060880847809086119338033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4707253898539390746225355 7060880847809086119338033)
                ·
                  refine ⟨5295660635856814589503525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7060880847809086119338033 5295660635856814589503525)
                  ·
                    refine ⟨992936369223152735531911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5295660635856814589503525 992936369223152735531911)
                    ·
                      rfl

theorem cell22_2900605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_2900605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900605 prefixEnd_2900605 := by exact prefixLift 2900605
  have htrace : WordTrace (prefixWord ++ tailWord_2900605) baseStart_2900605 baseEnd_2900605 := by
    simpa [prefixWord, tailWord_2900605, baseEnd_2900605] using wordTrace_append hprefix tailTrace_2900605
  have hstable : (prefixWord ++ tailWord_2900605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900605).length < 2 ^ (prefixWord ++ tailWord_2900605).sum := by decide
  have hdescent : baseEnd_2900605 < baseStart_2900605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900712 : List Nat := [2, 1, 4, 1, 4, 1, 2, 2, 1, 4]
def baseStart_2900712 : Nat := 118140960795 + 2900712 * 2 ^ 59
def prefixEnd_2900712 : Nat := 4983230072969 + 3 ^ 40 * 2900712 * 2
def baseEnd_2900712 : Nat := 992972997509840123106583

theorem tailTrace_2900712 : CollatzResearch.WordTrace tailWord_2900712 prefixEnd_2900712 992972997509840123106583 := by
  unfold tailWord_2900712
  simp only [CollatzResearch.WordTrace]
  refine ⟨52898829133611650506864195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70531772178148867342485593 52898829133611650506864195)
  ·
    refine ⟨79348243700417475760296293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52898829133611650506864195 79348243700417475760296293)
    ·
      refine ⟨14877795693828276705055555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79348243700417475760296293 14877795693828276705055555)
      ·
        refine ⟨22316693540742415057583333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14877795693828276705055555 22316693540742415057583333)
        ·
          refine ⟨4184380038889202823296875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22316693540742415057583333 4184380038889202823296875)
          ·
            refine ⟨6276570058333804234945313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4184380038889202823296875 6276570058333804234945313)
            ·
              refine ⟨4707427543750353176208985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6276570058333804234945313 4707427543750353176208985)
              ·
                refine ⟨3530570657812764882156739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4707427543750353176208985 3530570657812764882156739)
                ·
                  refine ⟨5295855986719147323235109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530570657812764882156739 5295855986719147323235109)
                  ·
                    refine ⟨992972997509840123106583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5295855986719147323235109 992972997509840123106583)
                    ·
                      rfl

theorem cell22_2900712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_2900712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900712 prefixEnd_2900712 := by exact prefixLift 2900712
  have htrace : WordTrace (prefixWord ++ tailWord_2900712) baseStart_2900712 baseEnd_2900712 := by
    simpa [prefixWord, tailWord_2900712, baseEnd_2900712] using wordTrace_append hprefix tailTrace_2900712
  have hstable : (prefixWord ++ tailWord_2900712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900712).length < 2 ^ (prefixWord ++ tailWord_2900712).sum := by decide
  have hdescent : baseEnd_2900712 < baseStart_2900712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900723 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 2, 4]
def baseStart_2900723 : Nat := 118140960795 + 2900723 * 2 ^ 59
def prefixEnd_2900723 : Nat := 4983230072969 + 3 ^ 40 * 2900723 * 2
def baseEnd_2900723 : Nat := 992976763034639761081549

theorem tailTrace_2900723 : CollatzResearch.WordTrace tailWord_2900723 prefixEnd_2900723 992976763034639761081549 := by
  unfold tailWord_2900723
  simp only [CollatzResearch.WordTrace]
  refine ⟨105798059470183449892378823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70532039646788966594919215 105798059470183449892378823)
  ·
    refine ⟨158697089205275174838568235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105798059470183449892378823 158697089205275174838568235)
    ·
      refine ⟨238045633807912762257852353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158697089205275174838568235 238045633807912762257852353)
      ·
        refine ⟨178534225355934571693389265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238045633807912762257852353 178534225355934571693389265)
        ·
          refine ⟨133900669016950928770041949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178534225355934571693389265 133900669016950928770041949)
          ·
            refine ⟨50212750881356598288765731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133900669016950928770041949 50212750881356598288765731)
            ·
              refine ⟨75319126322034897433148597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50212750881356598288765731 75319126322034897433148597)
              ·
                refine ⟨7061168092690771634357681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75319126322034897433148597 7061168092690771634357681)
                ·
                  refine ⟨5295876069518078725768261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7061168092690771634357681 5295876069518078725768261)
                  ·
                    refine ⟨992976763034639761081549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5295876069518078725768261 992976763034639761081549)
                    ·
                      rfl

theorem cell22_2900723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 4].length) (baseStart_2900723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900723 prefixEnd_2900723 := by exact prefixLift 2900723
  have htrace : WordTrace (prefixWord ++ tailWord_2900723) baseStart_2900723 baseEnd_2900723 := by
    simpa [prefixWord, tailWord_2900723, baseEnd_2900723] using wordTrace_append hprefix tailTrace_2900723
  have hstable : (prefixWord ++ tailWord_2900723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900723).length < 2 ^ (prefixWord ++ tailWord_2900723).sum := by decide
  have hdescent : baseEnd_2900723 < baseStart_2900723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900740 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_2900740 : Nat := 118140960795 + 2900740 * 2 ^ 59
def prefixEnd_2900740 : Nat := 4983230072969 + 3 ^ 40 * 2900740 * 2
def baseEnd_2900740 : Nat := 992982582482057383406497

theorem tailTrace_2900740 : CollatzResearch.WordTrace tailWord_2900740 prefixEnd_2900740 992982582482057383406497 := by
  unfold tailWord_2900740
  simp only [CollatzResearch.WordTrace]
  refine ⟨52899339755560930897873837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70532453007414574530498449 52899339755560930897873837)
  ·
    refine ⟨19837252408335349086702689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52899339755560930897873837 19837252408335349086702689)
    ·
      refine ⟨14877939306251511815027017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19837252408335349086702689 14877939306251511815027017)
      ·
        refine ⟨11158454479688633861270263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14877939306251511815027017 11158454479688633861270263)
        ·
          refine ⟨16737681719532950791905395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11158454479688633861270263 16737681719532950791905395)
          ·
            refine ⟨25106522579299426187858093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16737681719532950791905395 25106522579299426187858093)
            ·
              refine ⟨9414945967237284820446785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25106522579299426187858093 9414945967237284820446785)
              ·
                refine ⟨7061209475427963615335089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9414945967237284820446785 7061209475427963615335089)
                ·
                  refine ⟨5295907106570972711501317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7061209475427963615335089 5295907106570972711501317)
                  ·
                    refine ⟨992982582482057383406497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5295907106570972711501317 992982582482057383406497)
                    ·
                      rfl

theorem cell22_2900740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_2900740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900740 prefixEnd_2900740 := by exact prefixLift 2900740
  have htrace : WordTrace (prefixWord ++ tailWord_2900740) baseStart_2900740 baseEnd_2900740 := by
    simpa [prefixWord, tailWord_2900740, baseEnd_2900740] using wordTrace_append hprefix tailTrace_2900740
  have hstable : (prefixWord ++ tailWord_2900740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900740).length < 2 ^ (prefixWord ++ tailWord_2900740).sum := by decide
  have hdescent : baseEnd_2900740 < baseStart_2900740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900806 : List Nat := [6, 1, 1, 2, 3, 1, 1, 7]
def baseStart_2900806 : Nat := 118140960795 + 2900806 * 2 ^ 59
def prefixEnd_2900806 : Nat := 4983230072969 + 3 ^ 40 * 2900806 * 2
def baseEnd_2900806 : Nat := 110333908403428356806255

theorem tailTrace_2900806 : CollatzResearch.WordTrace tailWord_2900806 prefixEnd_2900806 110333908403428356806255 := by
  unfold tailWord_2900806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3306283960277586095864071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70534057819255170045100181 3306283960277586095864071)
  ·
    refine ⟨4959425940416379143796107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3306283960277586095864071 4959425940416379143796107)
    ·
      refine ⟨7439138910624568715694161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4959425940416379143796107 7439138910624568715694161)
      ·
        refine ⟨5579354182968426536770621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7439138910624568715694161 5579354182968426536770621)
        ·
          refine ⟨2092257818613159951288983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5579354182968426536770621 2092257818613159951288983)
          ·
            refine ⟨3138386727919739926933475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092257818613159951288983 3138386727919739926933475)
            ·
              refine ⟨4707580091879609890400213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138386727919739926933475 4707580091879609890400213)
              ·
                refine ⟨110333908403428356806255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4707580091879609890400213 110333908403428356806255)
                ·
                  rfl

theorem cell22_2900806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_2900806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2900806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2900806 prefixEnd_2900806 := by exact prefixLift 2900806
  have htrace : WordTrace (prefixWord ++ tailWord_2900806) baseStart_2900806 baseEnd_2900806 := by
    simpa [prefixWord, tailWord_2900806, baseEnd_2900806] using wordTrace_append hprefix tailTrace_2900806
  have hstable : (prefixWord ++ tailWord_2900806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900806).length < 2 ^ (prefixWord ++ tailWord_2900806).sum := by decide
  have hdescent : baseEnd_2900806 < baseStart_2900806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901016 : List Nat := [2, 1, 2, 3, 2, 4, 2, 1, 1, 4]
def baseStart_2901016 : Nat := 118140960795 + 2901016 * 2 ^ 59
def prefixEnd_2901016 : Nat := 4983230072969 + 3 ^ 40 * 2901016 * 2
def baseEnd_2901016 : Nat := 993077062922484663505651

theorem tailTrace_2901016 : CollatzResearch.WordTrace tailWord_2901016 prefixEnd_2901016 993077062922484663505651 := by
  unfold tailWord_2901016
  simp only [CollatzResearch.WordTrace]
  refine ⟨52904373029060980466397451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70539164038747973955196601 52904373029060980466397451)
  ·
    refine ⟨79356559543591470699596177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52904373029060980466397451 79356559543591470699596177)
    ·
      refine ⟨59517419657693603024697133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79356559543591470699596177 59517419657693603024697133)
      ·
        refine ⟨22319032371635101134261425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59517419657693603024697133 22319032371635101134261425)
        ·
          refine ⟨16739274278726325850696069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22319032371635101134261425 16739274278726325850696069)
          ·
            refine ⟨3138613927261186097005513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16739274278726325850696069 3138613927261186097005513)
            ·
              refine ⟨2353960445445889572754135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3138613927261186097005513 2353960445445889572754135)
              ·
                refine ⟨3530940668168834359131203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2353960445445889572754135 3530940668168834359131203)
                ·
                  refine ⟨5296411002253251538696805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530940668168834359131203 5296411002253251538696805)
                  ·
                    refine ⟨993077062922484663505651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5296411002253251538696805 993077062922484663505651)
                    ·
                      rfl

theorem cell22_2901016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_2901016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901016 prefixEnd_2901016 := by exact prefixLift 2901016
  have htrace : WordTrace (prefixWord ++ tailWord_2901016) baseStart_2901016 baseEnd_2901016 := by
    simpa [prefixWord, tailWord_2901016, baseEnd_2901016] using wordTrace_append hprefix tailTrace_2901016
  have hstable : (prefixWord ++ tailWord_2901016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901016).length < 2 ^ (prefixWord ++ tailWord_2901016).sum := by decide
  have hdescent : baseEnd_2901016 < baseStart_2901016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901031 : List Nat := [1, 1, 7, 1, 1, 1, 2, 4, 4]
def baseStart_2901031 : Nat := 118140960795 + 2901031 * 2 ^ 59
def prefixEnd_2901031 : Nat := 4983230072969 + 3 ^ 40 * 2901031 * 2
def baseEnd_2901031 : Nat := 331027399243009874793535

theorem tailTrace_2901031 : CollatzResearch.WordTrace tailWord_2901031 prefixEnd_2901031 331027399243009874793535 := by
  unfold tailWord_2901031
  simp only [CollatzResearch.WordTrace]
  refine ⟨105809293153067618494590947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70539528768711745663060631 105809293153067618494590947)
  ·
    refine ⟨158713939729601427741886421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105809293153067618494590947 158713939729601427741886421)
    ·
      refine ⟨3719857962412533462700463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 158713939729601427741886421 3719857962412533462700463)
      ·
        refine ⟨5579786943618800194050695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3719857962412533462700463 5579786943618800194050695)
        ·
          refine ⟨8369680415428200291076043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5579786943618800194050695 8369680415428200291076043)
          ·
            refine ⟨12554520623142300436614065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8369680415428200291076043 12554520623142300436614065)
            ·
              refine ⟨9415890467356725327460549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12554520623142300436614065 9415890467356725327460549)
              ·
                refine ⟨1765479462629385998898853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9415890467356725327460549 1765479462629385998898853)
                ·
                  refine ⟨331027399243009874793535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1765479462629385998898853 331027399243009874793535)
                  ·
                    rfl

theorem cell22_2901031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 4].length) (baseStart_2901031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901031 prefixEnd_2901031 := by exact prefixLift 2901031
  have htrace : WordTrace (prefixWord ++ tailWord_2901031) baseStart_2901031 baseEnd_2901031 := by
    simpa [prefixWord, tailWord_2901031, baseEnd_2901031] using wordTrace_append hprefix tailTrace_2901031
  have hstable : (prefixWord ++ tailWord_2901031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901031).length < 2 ^ (prefixWord ++ tailWord_2901031).sum := by decide
  have hdescent : baseEnd_2901031 < baseStart_2901031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901044 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2901044 : Nat := 118140960795 + 2901044 * 2 ^ 59
def prefixEnd_2901044 : Nat := 4983230072969 + 3 ^ 40 * 2901044 * 2
def baseEnd_2901044 : Nat := 993086647894701923805565

theorem tailTrace_2901044 : CollatzResearch.WordTrace tailWord_2901044 prefixEnd_2901044 993086647894701923805565 := by
  unfold tailWord_2901044
  simp only [CollatzResearch.WordTrace]
  refine ⟨52904883651010260857407093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70539844868013681143209457 52904883651010260857407093)
  ·
    refine ⟨4959832842282211955381915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52904883651010260857407093 4959832842282211955381915)
    ·
      refine ⟨7439749263423317933072873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4959832842282211955381915 7439749263423317933072873)
      ·
        refine ⟨5579811947567488449804655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7439749263423317933072873 5579811947567488449804655)
        ·
          refine ⟨8369717921351232674706983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5579811947567488449804655 8369717921351232674706983)
          ·
            refine ⟨12554576882026849012060475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8369717921351232674706983 12554576882026849012060475)
            ·
              refine ⟨18831865323040273518090713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12554576882026849012060475 18831865323040273518090713)
              ·
                refine ⟨14123898992280205138568035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18831865323040273518090713 14123898992280205138568035)
                ·
                  refine ⟨21185848488420307707852053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14123898992280205138568035 21185848488420307707852053)
                  ·
                    refine ⟨993086647894701923805565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21185848488420307707852053 993086647894701923805565)
                    ·
                      rfl

theorem cell22_2901044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2901044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901044 prefixEnd_2901044 := by exact prefixLift 2901044
  have htrace : WordTrace (prefixWord ++ tailWord_2901044) baseStart_2901044 baseEnd_2901044 := by
    simpa [prefixWord, tailWord_2901044, baseEnd_2901044] using wordTrace_append hprefix tailTrace_2901044
  have hstable : (prefixWord ++ tailWord_2901044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901044).length < 2 ^ (prefixWord ++ tailWord_2901044).sum := by decide
  have hdescent : baseEnd_2901044 < baseStart_2901044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901046 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_2901046 : Nat := 118140960795 + 2901046 * 2 ^ 59
def prefixEnd_2901046 : Nat := 4983230072969 + 3 ^ 40 * 2901046 * 2
def baseEnd_2901046 : Nat := 993087332535574585255559

theorem tailTrace_2901046 : CollatzResearch.WordTrace tailWord_2901046 prefixEnd_2901046 993087332535574585255559 := by
  unfold tailWord_2901046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6613115015500829753524187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70539893498675517370924661 6613115015500829753524187)
  ·
    refine ⟨9919672523251244630286281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6613115015500829753524187 9919672523251244630286281)
    ·
      refine ⟨7439754392438433472714711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9919672523251244630286281 7439754392438433472714711)
      ·
        refine ⟨11159631588657650209072067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7439754392438433472714711 11159631588657650209072067)
        ·
          refine ⟨16739447382986475313608101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11159631588657650209072067 16739447382986475313608101)
          ·
            refine ⟨3138646384309964121301519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16739447382986475313608101 3138646384309964121301519)
            ·
              refine ⟨4707969576464946181952279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138646384309964121301519 4707969576464946181952279)
              ·
                refine ⟨7061954364697419272928419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4707969576464946181952279 7061954364697419272928419)
                ·
                  refine ⟨10592931547046128909392629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7061954364697419272928419 10592931547046128909392629)
                  ·
                    refine ⟨993087332535574585255559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10592931547046128909392629 993087332535574585255559)
                    ·
                      rfl

theorem cell22_2901046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_2901046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901046 prefixEnd_2901046 := by exact prefixLift 2901046
  have htrace : WordTrace (prefixWord ++ tailWord_2901046) baseStart_2901046 baseEnd_2901046 := by
    simpa [prefixWord, tailWord_2901046, baseEnd_2901046] using wordTrace_append hprefix tailTrace_2901046
  have hstable : (prefixWord ++ tailWord_2901046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901046).length < 2 ^ (prefixWord ++ tailWord_2901046).sum := by decide
  have hdescent : baseEnd_2901046 < baseStart_2901046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901078 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2901078 : Nat := 118140960795 + 2901078 * 2 ^ 59
def prefixEnd_2901078 : Nat := 4983230072969 + 3 ^ 40 * 2901078 * 2
def baseEnd_2901078 : Nat := 993098286789537168455461

theorem tailTrace_2901078 : CollatzResearch.WordTrace tailWord_2901078 prefixEnd_2901078 993098286789537168455461 := by
  unfold tailWord_2901078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6613187961493584095096993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70540671589264897014367925 6613187961493584095096993)
  ·
    refine ⟨4959890971120188071322745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6613187961493584095096993 4959890971120188071322745)
    ·
      refine ⟨3719918228340141053492059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4959890971120188071322745 3719918228340141053492059)
      ·
        refine ⟨5579877342510211580238089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3719918228340141053492059 5579877342510211580238089)
        ·
          refine ⟨4184908006882658685178567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5579877342510211580238089 4184908006882658685178567)
          ·
            refine ⟨6277362010323988027767851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4184908006882658685178567 6277362010323988027767851)
            ·
              refine ⟨9416043015485982041651777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6277362010323988027767851 9416043015485982041651777)
              ·
                refine ⟨7062032261614486531238833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9416043015485982041651777 7062032261614486531238833)
                ·
                  refine ⟨5296524196210864898429125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7062032261614486531238833 5296524196210864898429125)
                  ·
                    refine ⟨993098286789537168455461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5296524196210864898429125 993098286789537168455461)
                    ·
                      rfl

theorem cell22_2901078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2901078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901078 prefixEnd_2901078 := by exact prefixLift 2901078
  have htrace : WordTrace (prefixWord ++ tailWord_2901078) baseStart_2901078 baseEnd_2901078 := by
    simpa [prefixWord, tailWord_2901078, baseEnd_2901078] using wordTrace_append hprefix tailTrace_2901078
  have hstable : (prefixWord ++ tailWord_2901078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901078).length < 2 ^ (prefixWord ++ tailWord_2901078).sum := by decide
  have hdescent : baseEnd_2901078 < baseStart_2901078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901087 : List Nat := [1, 1, 2, 3, 1, 1, 4, 4, 5]
def baseStart_2901087 : Nat := 118140960795 + 2901087 * 2 ^ 59
def prefixEnd_2901087 : Nat := 4983230072969 + 3 ^ 40 * 2901087 * 2
def baseEnd_2901087 : Nat := 331033789224488048326811

theorem tailTrace_2901087 : CollatzResearch.WordTrace tailWord_2901087 prefixEnd_2901087 331033789224488048326811 := by
  unfold tailWord_2901087
  simp only [CollatzResearch.WordTrace]
  refine ⟨105811335640864740058629515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70540890427243160039086343 105811335640864740058629515)
  ·
    refine ⟨158717003461297110087944273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105811335640864740058629515 158717003461297110087944273)
    ·
      refine ⟨119037752595972832565958205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158717003461297110087944273 119037752595972832565958205)
      ·
        refine ⟨44639157223489812212234327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119037752595972832565958205 44639157223489812212234327)
        ·
          refine ⟨66958735835234718318351491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44639157223489812212234327 66958735835234718318351491)
          ·
            refine ⟨100438103752852077477527237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66958735835234718318351491 100438103752852077477527237)
            ·
              refine ⟨18832144453659764527036357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100438103752852077477527237 18832144453659764527036357)
              ·
                refine ⟨3531027085061205848819317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18832144453659764527036357 3531027085061205848819317)
                ·
                  refine ⟨331033789224488048326811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3531027085061205848819317 331033789224488048326811)
                  ·
                    rfl

theorem cell22_2901087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 5].length) (baseStart_2901087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901087 prefixEnd_2901087 := by exact prefixLift 2901087
  have htrace : WordTrace (prefixWord ++ tailWord_2901087) baseStart_2901087 baseEnd_2901087 := by
    simpa [prefixWord, tailWord_2901087, baseEnd_2901087] using wordTrace_append hprefix tailTrace_2901087
  have hstable : (prefixWord ++ tailWord_2901087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901087).length < 2 ^ (prefixWord ++ tailWord_2901087).sum := by decide
  have hdescent : baseEnd_2901087 < baseStart_2901087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901185 : List Nat := [1, 2, 6, 1, 1, 3, 2, 1, 1, 4]
def baseStart_2901185 : Nat := 118140960795 + 2901185 * 2 ^ 59
def prefixEnd_2901185 : Nat := 4983230072969 + 3 ^ 40 * 2901185 * 2
def baseEnd_2901185 : Nat := 993134915076224556030133

theorem tailTrace_2901185 : CollatzResearch.WordTrace tailWord_2901185 prefixEnd_2901185 993134915076224556030133 := by
  unfold tailWord_2901185
  simp only [CollatzResearch.WordTrace]
  refine ⟨105814909994509702795697009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70543273329673135197131339 105814909994509702795697009)
  ·
    refine ⟨79361182495882277096772757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105814909994509702795697009 79361182495882277096772757)
    ·
      refine ⟨3720055429494481738911223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79361182495882277096772757 3720055429494481738911223)
      ·
        refine ⟨5580083144241722608366835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3720055429494481738911223 5580083144241722608366835)
        ·
          refine ⟨8370124716362583912550253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5580083144241722608366835 8370124716362583912550253)
          ·
            refine ⟨3138796768635968967206345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8370124716362583912550253 3138796768635968967206345)
            ·
              refine ⟨2354097576476976725404759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3138796768635968967206345 2354097576476976725404759)
              ·
                refine ⟨3531146364715465088107139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354097576476976725404759 3531146364715465088107139)
                ·
                  refine ⟨5296719547073197632160709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3531146364715465088107139 5296719547073197632160709)
                  ·
                    refine ⟨993134915076224556030133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5296719547073197632160709 993134915076224556030133)
                    ·
                      rfl

theorem cell22_2901185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_2901185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901185 prefixEnd_2901185 := by exact prefixLift 2901185
  have htrace : WordTrace (prefixWord ++ tailWord_2901185) baseStart_2901185 baseEnd_2901185 := by
    simpa [prefixWord, tailWord_2901185, baseEnd_2901185] using wordTrace_append hprefix tailTrace_2901185
  have hstable : (prefixWord ++ tailWord_2901185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901185).length < 2 ^ (prefixWord ++ tailWord_2901185).sum := by decide
  have hdescent : baseEnd_2901185 < baseStart_2901185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901207 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 1, 8]
def baseStart_2901207 : Nat := 118140960795 + 2901207 * 2 ^ 59
def prefixEnd_2901207 : Nat := 4983230072969 + 3 ^ 40 * 2901207 * 2
def baseEnd_2901207 : Nat := 993142446125823831980065

theorem tailTrace_2901207 : CollatzResearch.WordTrace tailWord_2901207 prefixEnd_2901207 993142446125823831980065 := by
  unfold tailWord_2901207
  simp only [CollatzResearch.WordTrace]
  refine ⟨105815712400430000552997875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70543808266953333701998583 105815712400430000552997875)
  ·
    refine ⟨158723568600645000829496813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105815712400430000552997875 158723568600645000829496813)
    ·
      refine ⟨59521338225241875311061305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158723568600645000829496813 59521338225241875311061305)
      ·
        refine ⟨44641003668931406483295979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59521338225241875311061305 44641003668931406483295979)
        ·
          refine ⟨66961505503397109724943969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44641003668931406483295979 66961505503397109724943969)
          ·
            refine ⟨50221129127547832293707977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66961505503397109724943969 50221129127547832293707977)
            ·
              refine ⟨37665846845660874220280983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50221129127547832293707977 37665846845660874220280983)
              ·
                refine ⟨56498770268491311330421475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37665846845660874220280983 56498770268491311330421475)
                ·
                  refine ⟨84748155402736966995632213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56498770268491311330421475 84748155402736966995632213)
                  ·
                    refine ⟨993142446125823831980065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84748155402736966995632213 993142446125823831980065)
                    ·
                      rfl

theorem cell22_2901207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_2901207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901207 prefixEnd_2901207 := by exact prefixLift 2901207
  have htrace : WordTrace (prefixWord ++ tailWord_2901207) baseStart_2901207 baseEnd_2901207 := by
    simpa [prefixWord, tailWord_2901207, baseEnd_2901207] using wordTrace_append hprefix tailTrace_2901207
  have hstable : (prefixWord ++ tailWord_2901207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901207).length < 2 ^ (prefixWord ++ tailWord_2901207).sum := by decide
  have hdescent : baseEnd_2901207 < baseStart_2901207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901226 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 3, 3]
def baseStart_2901226 : Nat := 118140960795 + 2901226 * 2 ^ 59
def prefixEnd_2901226 : Nat := 4983230072969 + 3 ^ 40 * 2901226 * 2
def baseEnd_2901226 : Nat := 993148950214114115755007

theorem tailTrace_2901226 : CollatzResearch.WordTrace tailWord_2901226 prefixEnd_2901226 993148950214114115755007 := by
  unfold tailWord_2901226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26454101346840291699484883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70544270258240777865293021 26454101346840291699484883)
  ·
    refine ⟨39681152020260437549227325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26454101346840291699484883 39681152020260437549227325)
    ·
      refine ⟨14880432007597664080960247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39681152020260437549227325 14880432007597664080960247)
      ·
        refine ⟨22320648011396496121440371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14880432007597664080960247 22320648011396496121440371)
        ·
          refine ⟨33480972017094744182160557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22320648011396496121440371 33480972017094744182160557)
          ·
            refine ⟨12555364506410529068310209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33480972017094744182160557 12555364506410529068310209)
            ·
              refine ⟨9416523379807896801232657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12555364506410529068310209 9416523379807896801232657)
              ·
                refine ⟨7062392534855922600924493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9416523379807896801232657 7062392534855922600924493)
                ·
                  refine ⟨2648397200570970975346685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7062392534855922600924493 2648397200570970975346685)
                  ·
                    refine ⟨993148950214114115755007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2648397200570970975346685 993148950214114115755007)
                    ·
                      rfl

theorem cell22_2901226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_2901226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901226 prefixEnd_2901226 := by exact prefixLift 2901226
  have htrace : WordTrace (prefixWord ++ tailWord_2901226) baseStart_2901226 baseEnd_2901226 := by
    simpa [prefixWord, tailWord_2901226, baseEnd_2901226] using wordTrace_append hprefix tailTrace_2901226
  have hstable : (prefixWord ++ tailWord_2901226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901226).length < 2 ^ (prefixWord ++ tailWord_2901226).sum := by decide
  have hdescent : baseEnd_2901226 < baseStart_2901226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901260 : List Nat := [2, 2, 1, 2, 2, 4, 3, 2, 1, 3]
def baseStart_2901260 : Nat := 118140960795 + 2901260 * 2 ^ 59
def prefixEnd_2901260 : Nat := 4983230072969 + 3 ^ 40 * 2901260 * 2
def baseEnd_2901260 : Nat := 993160589108949360404903

theorem tailTrace_2901260 : CollatzResearch.WordTrace tailWord_2901260 prefixEnd_2901260 993160589108949360404903 := by
  unfold tailWord_2901260
  simp only [CollatzResearch.WordTrace]
  refine ⟨52908822734618995302338617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70545096979491993736451489 52908822734618995302338617)
  ·
    refine ⟨39681617050964246476753963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52908822734618995302338617 39681617050964246476753963)
    ·
      refine ⟨59522425576446369715130945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39681617050964246476753963 59522425576446369715130945)
      ·
        refine ⟨44641819182334777286348209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59522425576446369715130945 44641819182334777286348209)
        ·
          refine ⟨33481364386751082964761157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44641819182334777286348209 33481364386751082964761157)
          ·
            refine ⟨6277755822515828055892717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33481364386751082964761157 6277755822515828055892717)
            ·
              refine ⟨2354158433443435520959769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6277755822515828055892717 2354158433443435520959769)
              ·
                refine ⟨1765618825082576640719827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2354158433443435520959769 1765618825082576640719827)
                ·
                  refine ⟨2648428237623864961079741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765618825082576640719827 2648428237623864961079741)
                  ·
                    refine ⟨993160589108949360404903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2648428237623864961079741 993160589108949360404903)
                    ·
                      rfl

theorem cell22_2901260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_2901260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901260 prefixEnd_2901260 := by exact prefixLift 2901260
  have htrace : WordTrace (prefixWord ++ tailWord_2901260) baseStart_2901260 baseEnd_2901260 := by
    simpa [prefixWord, tailWord_2901260, baseEnd_2901260] using wordTrace_append hprefix tailTrace_2901260
  have hstable : (prefixWord ++ tailWord_2901260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901260).length < 2 ^ (prefixWord ++ tailWord_2901260).sum := by decide
  have hdescent : baseEnd_2901260 < baseStart_2901260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901269 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_2901269 : Nat := 118140960795 + 2901269 * 2 ^ 59
def prefixEnd_2901269 : Nat := 4983230072969 + 3 ^ 40 * 2901269 * 2
def baseEnd_2901269 : Nat := 993163669992876336929875

theorem tailTrace_2901269 : CollatzResearch.WordTrace tailWord_2901269 prefixEnd_2901269 993163669992876336929875 := by
  unfold tailWord_2901269
  simp only [CollatzResearch.WordTrace]
  refine ⟨105817973726205385141754861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70545315817470256761169907 105817973726205385141754861)
  ·
    refine ⟨39681740147327019428158073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105817973726205385141754861 39681740147327019428158073)
    ·
      refine ⟨29761305110495264571118555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39681740147327019428158073 29761305110495264571118555)
      ·
        refine ⟨44641957665742896856677833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29761305110495264571118555 44641957665742896856677833)
        ·
          refine ⟨33481468249307172642508375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44641957665742896856677833 33481468249307172642508375)
          ·
            refine ⟨50222202373960758963762563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33481468249307172642508375 50222202373960758963762563)
            ·
              refine ⟨75333303560941138445643845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50222202373960758963762563 75333303560941138445643845)
              ·
                refine ⟨14124994417676463458558221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75333303560941138445643845 14124994417676463458558221)
                ·
                  refine ⟨5296872906628673796959333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14124994417676463458558221 5296872906628673796959333)
                  ·
                    refine ⟨993163669992876336929875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5296872906628673796959333 993163669992876336929875)
                    ·
                      rfl

theorem cell22_2901269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_2901269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901269 prefixEnd_2901269 := by exact prefixLift 2901269
  have htrace : WordTrace (prefixWord ++ tailWord_2901269) baseStart_2901269 baseEnd_2901269 := by
    simpa [prefixWord, tailWord_2901269, baseEnd_2901269] using wordTrace_append hprefix tailTrace_2901269
  have hstable : (prefixWord ++ tailWord_2901269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901269).length < 2 ^ (prefixWord ++ tailWord_2901269).sum := by decide
  have hdescent : baseEnd_2901269 < baseStart_2901269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901284 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 8]
def baseStart_2901284 : Nat := 118140960795 + 2901284 * 2 ^ 59
def prefixEnd_2901284 : Nat := 4983230072969 + 3 ^ 40 * 2901284 * 2
def baseEnd_2901284 : Nat := 331056268266473765934943

theorem tailTrace_2901284 : CollatzResearch.WordTrace tailWord_2901284 prefixEnd_2901284 331056268266473765934943 := by
  unfold tailWord_2901284
  simp only [CollatzResearch.WordTrace]
  refine ⟨52909260410575521351775453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70545680547434028469033937 52909260410575521351775453)
  ·
    refine ⟨19840972653965820506915795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52909260410575521351775453 19840972653965820506915795)
    ·
      refine ⟨29761458980948730760373693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19840972653965820506915795 29761458980948730760373693)
      ·
        refine ⟨11160547117855774035140135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29761458980948730760373693 11160547117855774035140135)
        ·
          refine ⟨16740820676783661052710203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11160547117855774035140135 16740820676783661052710203)
          ·
            refine ⟨25111231015175491579065305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16740820676783661052710203 25111231015175491579065305)
            ·
              refine ⟨18833423261381618684298979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25111231015175491579065305 18833423261381618684298979)
              ·
                refine ⟨28250134892072428026448469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18833423261381618684298979 28250134892072428026448469)
                ·
                  refine ⟨331056268266473765934943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28250134892072428026448469 331056268266473765934943)
                  ·
                    rfl

theorem cell22_2901284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_2901284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901284 prefixEnd_2901284 := by exact prefixLift 2901284
  have htrace : WordTrace (prefixWord ++ tailWord_2901284) baseStart_2901284 baseEnd_2901284 := by
    simpa [prefixWord, tailWord_2901284, baseEnd_2901284] using wordTrace_append hprefix tailTrace_2901284
  have hstable : (prefixWord ++ tailWord_2901284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901284).length < 2 ^ (prefixWord ++ tailWord_2901284).sum := by decide
  have hdescent : baseEnd_2901284 < baseStart_2901284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901299 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 3, 5]
def baseStart_2901299 : Nat := 118140960795 + 2901299 * 2 ^ 59
def prefixEnd_2901299 : Nat := 4983230072969 + 3 ^ 40 * 2901299 * 2
def baseEnd_2901299 : Nat := 993173939605966258679783

theorem tailTrace_2901299 : CollatzResearch.WordTrace tailWord_2901299 prefixEnd_2901299 993173939605966258679783 := by
  unfold tailWord_2901299
  simp only [CollatzResearch.WordTrace]
  refine ⟨105819067916096700265346951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70546045277397800176897967 105819067916096700265346951)
  ·
    refine ⟨158728601874145050398020427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105819067916096700265346951 158728601874145050398020427)
    ·
      refine ⟨238092902811217575597030641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158728601874145050398020427 238092902811217575597030641)
      ·
        refine ⟨178569677108413181697772981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238092902811217575597030641 178569677108413181697772981)
        ·
          refine ⟨16740907228913735784166217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178569677108413181697772981 16740907228913735784166217)
          ·
            refine ⟨12555680421685301838124663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16740907228913735784166217 12555680421685301838124663)
            ·
              refine ⟨18833520632527952757186995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12555680421685301838124663 18833520632527952757186995)
              ·
                refine ⟨28250280948791929135780493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18833520632527952757186995 28250280948791929135780493)
                ·
                  refine ⟨10593855355796973425917685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28250280948791929135780493 10593855355796973425917685)
                  ·
                    refine ⟨993173939605966258679783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10593855355796973425917685 993173939605966258679783)
                    ·
                      rfl

theorem cell22_2901299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 5].length) (baseStart_2901299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901299 prefixEnd_2901299 := by exact prefixLift 2901299
  have htrace : WordTrace (prefixWord ++ tailWord_2901299) baseStart_2901299 baseEnd_2901299 := by
    simpa [prefixWord, tailWord_2901299, baseEnd_2901299] using wordTrace_append hprefix tailTrace_2901299
  have hstable : (prefixWord ++ tailWord_2901299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901299).length < 2 ^ (prefixWord ++ tailWord_2901299).sum := by decide
  have hdescent : baseEnd_2901299 < baseStart_2901299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901333 : List Nat := [1, 3, 2, 2, 3, 1, 2, 3, 2, 3]
def baseStart_2901333 : Nat := 118140960795 + 2901333 * 2 ^ 59
def prefixEnd_2901333 : Nat := 4983230072969 + 3 ^ 40 * 2901333 * 2
def baseEnd_2901333 : Nat := 993185578500801503329679

theorem tailTrace_2901333 : CollatzResearch.WordTrace tailWord_2901333 prefixEnd_2901333 993185578500801503329679 := by
  unfold tailWord_2901333
  simp only [CollatzResearch.WordTrace]
  refine ⟨105820307997973524072084653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70546871998649016048056435 105820307997973524072084653)
  ·
    refine ⟨39682615499240071527031745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105820307997973524072084653 39682615499240071527031745)
    ·
      refine ⟨29761961624430053645273809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39682615499240071527031745 29761961624430053645273809)
      ·
        refine ⟨22321471218322540233955357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29761961624430053645273809 22321471218322540233955357)
        ·
          refine ⟨8370551706870952587733259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22321471218322540233955357 8370551706870952587733259)
          ·
            refine ⟨12555827560306428881599889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8370551706870952587733259 12555827560306428881599889)
            ·
              refine ⟨9416870670229821661199917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12555827560306428881599889 9416870670229821661199917)
              ·
                refine ⟨3531326501336183122949969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9416870670229821661199917 3531326501336183122949969)
                ·
                  refine ⟨2648494876002137342212477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3531326501336183122949969 2648494876002137342212477)
                  ·
                    refine ⟨993185578500801503329679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2648494876002137342212477 993185578500801503329679)
                    ·
                      rfl

theorem cell22_2901333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_2901333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901333 prefixEnd_2901333 := by exact prefixLift 2901333
  have htrace : WordTrace (prefixWord ++ tailWord_2901333) baseStart_2901333 baseEnd_2901333 := by
    simpa [prefixWord, tailWord_2901333, baseEnd_2901333] using wordTrace_append hprefix tailTrace_2901333
  have hstable : (prefixWord ++ tailWord_2901333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901333).length < 2 ^ (prefixWord ++ tailWord_2901333).sum := by decide
  have hdescent : baseEnd_2901333 < baseStart_2901333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901348 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_2901348 : Nat := 118140960795 + 2901348 * 2 ^ 59
def prefixEnd_2901348 : Nat := 4983230072969 + 3 ^ 40 * 2901348 * 2
def baseEnd_2901348 : Nat := 993190713307346464204633

theorem tailTrace_2901348 : CollatzResearch.WordTrace tailWord_2901348 prefixEnd_2901348 993190713307346464204633 := by
  unfold tailWord_2901348
  simp only [CollatzResearch.WordTrace]
  refine ⟨52910427546459590816940349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70547236728612787755920465 52910427546459590816940349)
  ·
    refine ⟨19841410329922346556352631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52910427546459590816940349 19841410329922346556352631)
    ·
      refine ⟨29762115494883519834528947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19841410329922346556352631 29762115494883519834528947)
      ·
        refine ⟨44643173242325279751793421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29762115494883519834528947 44643173242325279751793421)
        ·
          refine ⟨16741189965871979906922533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44643173242325279751793421 16741189965871979906922533)
          ·
            refine ⟨3138973118600996232547975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16741189965871979906922533 3138973118600996232547975)
            ·
              refine ⟨4708459677901494348821963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138973118600996232547975 4708459677901494348821963)
              ·
                refine ⟨7062689516852241523232945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4708459677901494348821963 7062689516852241523232945)
                ·
                  refine ⟨5297017137639181142424709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7062689516852241523232945 5297017137639181142424709)
                  ·
                    refine ⟨993190713307346464204633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5297017137639181142424709 993190713307346464204633)
                    ·
                      rfl

theorem cell22_2901348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_2901348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901348 prefixEnd_2901348 := by exact prefixLift 2901348
  have htrace : WordTrace (prefixWord ++ tailWord_2901348) baseStart_2901348 baseEnd_2901348 := by
    simpa [prefixWord, tailWord_2901348, baseEnd_2901348] using wordTrace_append hprefix tailTrace_2901348
  have hstable : (prefixWord ++ tailWord_2901348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901348).length < 2 ^ (prefixWord ++ tailWord_2901348).sum := by decide
  have hdescent : baseEnd_2901348 < baseStart_2901348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901502 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_2901502 : Nat := 118140960795 + 2901502 * 2 ^ 59
def prefixEnd_2901502 : Nat := 4983230072969 + 3 ^ 40 * 2901502 * 2
def baseEnd_2901502 : Nat := 993243430654541395854161

theorem tailTrace_2901502 : CollatzResearch.WordTrace tailWord_2901502 prefixEnd_2901502 993243430654541395854161 := by
  unfold tailWord_2901502
  simp only [CollatzResearch.WordTrace]
  refine ⟨13228308991795158241873345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70550981289574177289991173 13228308991795158241873345)
  ·
    refine ⟨9921231743846368681405009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13228308991795158241873345 9921231743846368681405009)
    ·
      refine ⟨7440923807884776511053757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9921231743846368681405009 7440923807884776511053757)
      ·
        refine ⟨2790346427956791191645159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7440923807884776511053757 2790346427956791191645159)
        ·
          refine ⟨4185519641935186787467739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2790346427956791191645159 4185519641935186787467739)
          ·
            refine ⟨6278279462902780181201609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4185519641935186787467739 6278279462902780181201609)
            ·
              refine ⟨4708709597177085135901207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6278279462902780181201609 4708709597177085135901207)
              ·
                refine ⟨7063064395765627703851811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4708709597177085135901207 7063064395765627703851811)
                ·
                  refine ⟨10594596593648441555777717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7063064395765627703851811 10594596593648441555777717)
                  ·
                    refine ⟨993243430654541395854161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10594596593648441555777717 993243430654541395854161)
                    ·
                      rfl

theorem cell22_2901502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_2901502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901502 prefixEnd_2901502 := by exact prefixLift 2901502
  have htrace : WordTrace (prefixWord ++ tailWord_2901502) baseStart_2901502 baseEnd_2901502 := by
    simpa [prefixWord, tailWord_2901502, baseEnd_2901502] using wordTrace_append hprefix tailTrace_2901502
  have hstable : (prefixWord ++ tailWord_2901502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901502).length < 2 ^ (prefixWord ++ tailWord_2901502).sum := by decide
  have hdescent : baseEnd_2901502 < baseStart_2901502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901513 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 3, 3]
def baseStart_2901513 : Nat := 118140960795 + 2901513 * 2 ^ 59
def prefixEnd_2901513 : Nat := 4983230072969 + 3 ^ 40 * 2901513 * 2
def baseEnd_2901513 : Nat := 993247196179341033829127

theorem tailTrace_2901513 : CollatzResearch.WordTrace tailWord_2901513 prefixEnd_2901513 993247196179341033829127 := by
  unfold tailWord_2901513
  simp only [CollatzResearch.WordTrace]
  refine ⟨105826873137321414813637193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70551248758214276542424795 105826873137321414813637193)
  ·
    refine ⟨79370154852991061110227895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105826873137321414813637193 79370154852991061110227895)
    ·
      refine ⟨119055232279486591665341843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79370154852991061110227895 119055232279486591665341843)
      ·
        refine ⟨178582848419229887498012765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119055232279486591665341843 178582848419229887498012765)
        ·
          refine ⟨66968568157211207811754787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178582848419229887498012765 66968568157211207811754787)
          ·
            refine ⟨100452852235816811717632181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66968568157211207811754787 100452852235816811717632181)
            ·
              refine ⟨9417454897107826098528017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100452852235816811717632181 9417454897107826098528017)
              ·
                refine ⟨7063091172830869573896013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9417454897107826098528017 7063091172830869573896013)
                ·
                  refine ⟨2648659189811576090211005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7063091172830869573896013 2648659189811576090211005)
                  ·
                    refine ⟨993247196179341033829127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2648659189811576090211005 993247196179341033829127)
                    ·
                      rfl

theorem cell22_2901513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 3].length) (baseStart_2901513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901513 prefixEnd_2901513 := by exact prefixLift 2901513
  have htrace : WordTrace (prefixWord ++ tailWord_2901513) baseStart_2901513 baseEnd_2901513 := by
    simpa [prefixWord, tailWord_2901513, baseEnd_2901513] using wordTrace_append hprefix tailTrace_2901513
  have hstable : (prefixWord ++ tailWord_2901513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901513).length < 2 ^ (prefixWord ++ tailWord_2901513).sum := by decide
  have hdescent : baseEnd_2901513 < baseStart_2901513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901517 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2901517 : Nat := 118140960795 + 2901517 * 2 ^ 59
def prefixEnd_2901517 : Nat := 4983230072969 + 3 ^ 40 * 2901517 * 2
def baseEnd_2901517 : Nat := 993248565461086356729115

theorem tailTrace_2901517 : CollatzResearch.WordTrace tailWord_2901517 prefixEnd_2901517 993248565461086356729115 := by
  unfold tailWord_2901517
  simp only [CollatzResearch.WordTrace]
  refine ⟨105827019029306923496782805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70551346019537948997855203 105827019029306923496782805)
  ·
    refine ⟨2480320758499381019455847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 105827019029306923496782805 2480320758499381019455847)
    ·
      refine ⟨3720481137749071529183771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2480320758499381019455847 3720481137749071529183771)
      ·
        refine ⟨5580721706623607293775657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3720481137749071529183771 5580721706623607293775657)
        ·
          refine ⟨4185541279967705470331743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5580721706623607293775657 4185541279967705470331743)
          ·
            refine ⟨6278311919951558205497615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4185541279967705470331743 6278311919951558205497615)
            ·
              refine ⟨9417467879927337308246423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6278311919951558205497615 9417467879927337308246423)
              ·
                refine ⟨14126201819891005962369635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9417467879927337308246423 14126201819891005962369635)
                ·
                  refine ⟨21189302729836508943554453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14126201819891005962369635 21189302729836508943554453)
                  ·
                    refine ⟨993248565461086356729115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21189302729836508943554453 993248565461086356729115)
                    ·
                      rfl

theorem cell22_2901517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2901517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901517 prefixEnd_2901517 := by exact prefixLift 2901517
  have htrace : WordTrace (prefixWord ++ tailWord_2901517) baseStart_2901517 baseEnd_2901517 := by
    simpa [prefixWord, tailWord_2901517, baseEnd_2901517] using wordTrace_append hprefix tailTrace_2901517
  have hstable : (prefixWord ++ tailWord_2901517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901517).length < 2 ^ (prefixWord ++ tailWord_2901517).sum := by decide
  have hdescent : baseEnd_2901517 < baseStart_2901517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901560 : List Nat := [2, 1, 2, 1, 4, 3, 3, 1, 5]
def baseStart_2901560 : Nat := 118140960795 + 2901560 * 2 ^ 59
def prefixEnd_2901560 : Nat := 4983230072969 + 3 ^ 40 * 2901560 * 2
def baseEnd_2901560 : Nat := 331087761746616192634661

theorem tailTrace_2901560 : CollatzResearch.WordTrace tailWord_2901560 prefixEnd_2901560 331087761746616192634661 := by
  unfold tailWord_2901560
  simp only [CollatzResearch.WordTrace]
  refine ⟨52914293684075570920299067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70552391578767427893732089 52914293684075570920299067)
  ·
    refine ⟨79371440526113356380448601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52914293684075570920299067 79371440526113356380448601)
    ·
      refine ⟨59528580394585017285336451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79371440526113356380448601 59528580394585017285336451)
      ·
        refine ⟨89292870591877525928004677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59528580394585017285336451 89292870591877525928004677)
        ·
          refine ⟨16742413235977036111500877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89292870591877525928004677 16742413235977036111500877)
          ·
            refine ⟨6278404963491388541812829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16742413235977036111500877 6278404963491388541812829)
            ·
              refine ⟨2354401861309270703179811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6278404963491388541812829 2354401861309270703179811)
              ·
                refine ⟨3531602791963906054769717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354401861309270703179811 3531602791963906054769717)
                ·
                  refine ⟨331087761746616192634661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3531602791963906054769717 331087761746616192634661)
                  ·
                    rfl

theorem cell22_2901560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 5].length) (baseStart_2901560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901560 prefixEnd_2901560 := by exact prefixLift 2901560
  have htrace : WordTrace (prefixWord ++ tailWord_2901560) baseStart_2901560 baseEnd_2901560 := by
    simpa [prefixWord, tailWord_2901560, baseEnd_2901560] using wordTrace_append hprefix tailTrace_2901560
  have hstable : (prefixWord ++ tailWord_2901560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901560).length < 2 ^ (prefixWord ++ tailWord_2901560).sum := by decide
  have hdescent : baseEnd_2901560 < baseStart_2901560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901581 : List Nat := [1, 6, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_2901581 : Nat := 118140960795 + 2901581 * 2 ^ 59
def prefixEnd_2901581 : Nat := 4983230072969 + 3 ^ 40 * 2901581 * 2
def baseEnd_2901581 : Nat := 993270473969011523128919

theorem tailTrace_2901581 : CollatzResearch.WordTrace tailWord_2901581 prefixEnd_2901581 993270473969011523128919 := by
  unfold tailWord_2901581
  simp only [CollatzResearch.WordTrace]
  refine ⟨105829353301075062427112597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70552902200716708284741731 105829353301075062427112597)
  ·
    refine ⟨4960750935987893551270903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105829353301075062427112597 4960750935987893551270903)
    ·
      refine ⟨7441126403981840326906355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4960750935987893551270903 7441126403981840326906355)
      ·
        refine ⟨11161689605972760490359533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7441126403981840326906355 11161689605972760490359533)
        ·
          refine ⟨4185633602239785183884825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11161689605972760490359533 4185633602239785183884825)
          ·
            refine ⟨3139225201679838887913619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4185633602239785183884825 3139225201679838887913619)
            ·
              refine ⟨4708837802519758331870429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139225201679838887913619 4708837802519758331870429)
              ·
                refine ⟨1765814175944909374451411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4708837802519758331870429 1765814175944909374451411)
                ·
                  refine ⟨2648721263917364061677117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765814175944909374451411 2648721263917364061677117)
                  ·
                    refine ⟨993270473969011523128919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2648721263917364061677117 993270473969011523128919)
                    ·
                      rfl

theorem cell22_2901581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_2901581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901581 prefixEnd_2901581 := by exact prefixLift 2901581
  have htrace : WordTrace (prefixWord ++ tailWord_2901581) baseStart_2901581 baseEnd_2901581 := by
    simpa [prefixWord, tailWord_2901581, baseEnd_2901581] using wordTrace_append hprefix tailTrace_2901581
  have hstable : (prefixWord ++ tailWord_2901581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901581).length < 2 ^ (prefixWord ++ tailWord_2901581).sum := by decide
  have hdescent : baseEnd_2901581 < baseStart_2901581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901605 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 6]
def baseStart_2901605 : Nat := 118140960795 + 2901605 * 2 ^ 59
def prefixEnd_2901605 : Nat := 4983230072969 + 3 ^ 40 * 2901605 * 2
def baseEnd_2901605 : Nat := 331092896553161153509615

theorem tailTrace_2901605 : CollatzResearch.WordTrace tailWord_2901605 prefixEnd_2901605 331092896553161153509615 := by
  unfold tailWord_2901605
  simp only [CollatzResearch.WordTrace]
  refine ⟨105830228652988114525986269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70553485768658743017324179 105830228652988114525986269)
  ·
    refine ⟨39686335744870542947244851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105830228652988114525986269 39686335744870542947244851)
    ·
      refine ⟨59529503617305814420867277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39686335744870542947244851 59529503617305814420867277)
      ·
        refine ⟨22323563856489680407825229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59529503617305814420867277 22323563856489680407825229)
        ·
          refine ⟨8371336446183630152934461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22323563856489680407825229 8371336446183630152934461)
          ·
            refine ⟨3139251167318861307350423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8371336446183630152934461 3139251167318861307350423)
            ·
              refine ⟨4708876750978291961025635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139251167318861307350423 4708876750978291961025635)
              ·
                refine ⟨7063315126467437941538453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4708876750978291961025635 7063315126467437941538453)
                ·
                  refine ⟨331092896553161153509615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7063315126467437941538453 331092896553161153509615)
                  ·
                    rfl

theorem cell22_2901605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_2901605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901605 prefixEnd_2901605 := by exact prefixLift 2901605
  have htrace : WordTrace (prefixWord ++ tailWord_2901605) baseStart_2901605 baseEnd_2901605 := by
    simpa [prefixWord, tailWord_2901605, baseEnd_2901605] using wordTrace_append hprefix tailTrace_2901605
  have hstable : (prefixWord ++ tailWord_2901605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901605).length < 2 ^ (prefixWord ++ tailWord_2901605).sum := by decide
  have hdescent : baseEnd_2901605 < baseStart_2901605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901633 : List Nat := [1, 2, 4, 2, 1, 2, 2, 8]
def baseStart_2901633 : Nat := 118140960795 + 2901633 * 2 ^ 59
def prefixEnd_2901633 : Nat := 4983230072969 + 3 ^ 40 * 2901633 * 2
def baseEnd_2901633 : Nat := 110365363847966746758751

theorem tailTrace_2901633 : CollatzResearch.WordTrace tailWord_2901633 prefixEnd_2901633 110365363847966746758751 := by
  unfold tailWord_2901633
  simp only [CollatzResearch.WordTrace]
  refine ⟨105831249896886675308005553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70554166597924450205337035 105831249896886675308005553)
  ·
    refine ⟨79373437422665006481004165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105831249896886675308005553 79373437422665006481004165)
    ·
      refine ⟨14882519516749688715188281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79373437422665006481004165 14882519516749688715188281)
      ·
        refine ⟨11161889637562266536391211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14882519516749688715188281 11161889637562266536391211)
        ·
          refine ⟨16742834456343399804586817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11161889637562266536391211 16742834456343399804586817)
          ·
            refine ⟨12557125842257549853440113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16742834456343399804586817 12557125842257549853440113)
            ·
              refine ⟨9417844381693162390080085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12557125842257549853440113 9417844381693162390080085)
              ·
                refine ⟨110365363847966746758751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9417844381693162390080085 110365363847966746758751)
                ·
                  rfl

theorem cell22_2901633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 8].length) (baseStart_2901633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901633 prefixEnd_2901633 := by exact prefixLift 2901633
  have htrace : WordTrace (prefixWord ++ tailWord_2901633) baseStart_2901633 baseEnd_2901633 := by
    simpa [prefixWord, tailWord_2901633, baseEnd_2901633] using wordTrace_append hprefix tailTrace_2901633
  have hstable : (prefixWord ++ tailWord_2901633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901633).length < 2 ^ (prefixWord ++ tailWord_2901633).sum := by decide
  have hdescent : baseEnd_2901633 < baseStart_2901633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901650 : List Nat := [3, 2, 3, 1, 4, 9]
def baseStart_2901650 : Nat := 118140960795 + 2901650 * 2 ^ 59
def prefixEnd_2901650 : Nat := 4983230072969 + 3 ^ 40 * 2901650 * 2
def baseEnd_2901650 : Nat := 12262890050359485717947

theorem tailTrace_2901650 : CollatzResearch.WordTrace tailWord_2901650 prefixEnd_2901650 12262890050359485717947 := by
  unfold tailWord_2901650
  simp only [CollatzResearch.WordTrace]
  refine ⟨26457967484456271802843601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70554579958550058140916269 26457967484456271802843601)
  ·
    refine ⟨19843475613342203852132701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26457967484456271802843601 19843475613342203852132701)
    ·
      refine ⟨7441303355003326444549763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19843475613342203852132701 7441303355003326444549763)
      ·
        refine ⟨11161955032504989666824645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7441303355003326444549763 11161955032504989666824645)
        ·
          refine ⟨2092866568594685562529621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11161955032504989666824645 2092866568594685562529621)
          ·
            refine ⟨12262890050359485717947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2092866568594685562529621 12262890050359485717947)
            ·
              rfl

theorem cell22_2901650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 9].length) (baseStart_2901650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901650 prefixEnd_2901650 := by exact prefixLift 2901650
  have htrace : WordTrace (prefixWord ++ tailWord_2901650) baseStart_2901650 baseEnd_2901650 := by
    simpa [prefixWord, tailWord_2901650, baseEnd_2901650] using wordTrace_append hprefix tailTrace_2901650
  have hstable : (prefixWord ++ tailWord_2901650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901650).length < 2 ^ (prefixWord ++ tailWord_2901650).sum := by decide
  have hdescent : baseEnd_2901650 < baseStart_2901650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901693 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_2901693 : Nat := 118140960795 + 2901693 * 2 ^ 59
def prefixEnd_2901693 : Nat := 4983230072969 + 3 ^ 40 * 2901693 * 2
def baseEnd_2901693 : Nat := 993308813857880564328575

theorem tailTrace_2901693 : CollatzResearch.WordTrace tailWord_2901693 prefixEnd_2901693 993308813857880564328575 := by
  unfold tailWord_2901693
  simp only [CollatzResearch.WordTrace]
  refine ⟨105833438276669305555189733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70555625517779537036793155 105833438276669305555189733)
  ·
    refine ⟨19843769676875494791598075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105833438276669305555189733 19843769676875494791598075)
    ·
      refine ⟨29765654515313242187397113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19843769676875494791598075 29765654515313242187397113)
      ·
        refine ⟨22324240886484931640547835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29765654515313242187397113 22324240886484931640547835)
        ·
          refine ⟨33486361329727397460821753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22324240886484931640547835 33486361329727397460821753)
          ·
            refine ⟨25114770997295548095616315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33486361329727397460821753 25114770997295548095616315)
            ·
              refine ⟨37672156495943322143424473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25114770997295548095616315 37672156495943322143424473)
              ·
                refine ⟨28254117371957491607568355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37672156495943322143424473 28254117371957491607568355)
                ·
                  refine ⟨42381176057936237411352533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28254117371957491607568355 42381176057936237411352533)
                  ·
                    refine ⟨993308813857880564328575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42381176057936237411352533 993308813857880564328575)
                    ·
                      rfl

theorem cell22_2901693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_2901693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901693 prefixEnd_2901693 := by exact prefixLift 2901693
  have htrace : WordTrace (prefixWord ++ tailWord_2901693) baseStart_2901693 baseEnd_2901693 := by
    simpa [prefixWord, tailWord_2901693, baseEnd_2901693] using wordTrace_append hprefix tailTrace_2901693
  have hstable : (prefixWord ++ tailWord_2901693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901693).length < 2 ^ (prefixWord ++ tailWord_2901693).sum := by decide
  have hdescent : baseEnd_2901693 < baseStart_2901693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901742 : List Nat := [4, 1, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_2901742 : Nat := 118140960795 + 2901742 * 2 ^ 59
def prefixEnd_2901742 : Nat := 4983230072969 + 3 ^ 40 * 2901742 * 2
def baseEnd_2901742 : Nat := 993325587559260769853425

theorem tailTrace_2901742 : CollatzResearch.WordTrace tailWord_2901742 prefixEnd_2901742 993325587559260769853425 := by
  unfold tailWord_2901742
  simp only [CollatzResearch.WordTrace]
  refine ⟨13229403181686473365465435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70556816968994524615815653 13229403181686473365465435)
  ·
    refine ⟨19844104772529710048198153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13229403181686473365465435 19844104772529710048198153)
    ·
      refine ⟨14883078579397282536148615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19844104772529710048198153 14883078579397282536148615)
      ·
        refine ⟨22324617869095923804222923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14883078579397282536148615 22324617869095923804222923)
        ·
          refine ⟨33486926803643885706334385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22324617869095923804222923 33486926803643885706334385)
          ·
            refine ⟨25115195102732914279750789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33486926803643885706334385 25115195102732914279750789)
            ·
              refine ⟨4709099081762421427453273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25115195102732914279750789 4709099081762421427453273)
              ·
                refine ⟨3531824311321816070589955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4709099081762421427453273 3531824311321816070589955)
                ·
                  refine ⟨5297736466982724105884933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3531824311321816070589955 5297736466982724105884933)
                  ·
                    refine ⟨993325587559260769853425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5297736466982724105884933 993325587559260769853425)
                    ·
                      rfl

theorem cell22_2901742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_2901742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901742 prefixEnd_2901742 := by exact prefixLift 2901742
  have htrace : WordTrace (prefixWord ++ tailWord_2901742) baseStart_2901742 baseEnd_2901742 := by
    simpa [prefixWord, tailWord_2901742, baseEnd_2901742] using wordTrace_append hprefix tailTrace_2901742
  have hstable : (prefixWord ++ tailWord_2901742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901742).length < 2 ^ (prefixWord ++ tailWord_2901742).sum := by decide
  have hdescent : baseEnd_2901742 < baseStart_2901742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901770 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_2901770 : Nat := 118140960795 + 2901770 * 2 ^ 59
def prefixEnd_2901770 : Nat := 4983230072969 + 3 ^ 40 * 2901770 * 2
def baseEnd_2901770 : Nat := 993335172531478030153339

theorem tailTrace_2901770 : CollatzResearch.WordTrace tailWord_2901770 prefixEnd_2901770 993335172531478030153339 := by
  unfold tailWord_2901770
  simp only [CollatzResearch.WordTrace]
  refine ⟨26459061674347586926435691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70557497798260231803828509 26459061674347586926435691)
  ·
    refine ⟨39688592511521380389653537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26459061674347586926435691 39688592511521380389653537)
    ·
      refine ⟨29766444383641035292240153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39688592511521380389653537 29766444383641035292240153)
      ·
        refine ⟨22324833287730776469180115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29766444383641035292240153 22324833287730776469180115)
        ·
          refine ⟨33487249931596164703770173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22324833287730776469180115 33487249931596164703770173)
          ·
            refine ⟨12557718724348561763913815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33487249931596164703770173 12557718724348561763913815)
            ·
              refine ⟨18836578086522842645870723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12557718724348561763913815 18836578086522842645870723)
              ·
                refine ⟨28254867129784263968806085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18836578086522842645870723 28254867129784263968806085)
                ·
                  refine ⟨5297787586834549494151141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28254867129784263968806085 5297787586834549494151141)
                  ·
                    refine ⟨993335172531478030153339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5297787586834549494151141 993335172531478030153339)
                    ·
                      rfl

theorem cell22_2901770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_2901770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901770 prefixEnd_2901770 := by exact prefixLift 2901770
  have htrace : WordTrace (prefixWord ++ tailWord_2901770) baseStart_2901770 baseEnd_2901770 := by
    simpa [prefixWord, tailWord_2901770, baseEnd_2901770] using wordTrace_append hprefix tailTrace_2901770
  have hstable : (prefixWord ++ tailWord_2901770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901770).length < 2 ^ (prefixWord ++ tailWord_2901770).sum := by decide
  have hdescent : baseEnd_2901770 < baseStart_2901770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901780 : List Nat := [2, 4, 4, 1, 2, 1, 2, 1, 5]
def baseStart_2901780 : Nat := 118140960795 + 2901780 * 2 ^ 59
def prefixEnd_2901780 : Nat := 4983230072969 + 3 ^ 40 * 2901780 * 2
def baseEnd_2901780 : Nat := 331112865245280445801103

theorem tailTrace_2901780 : CollatzResearch.WordTrace tailWord_2901780 prefixEnd_2901780 331112865245280445801103 := by
  unfold tailWord_2901780
  simp only [CollatzResearch.WordTrace]
  refine ⟨52918305713677059706803397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70557740951569412942404529 52918305713677059706803397)
  ·
    refine ⟨9922182321314448695025637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52918305713677059706803397 9922182321314448695025637)
    ·
      refine ⟨1860409185246459130317307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9922182321314448695025637 1860409185246459130317307)
      ·
        refine ⟨2790613777869688695475961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1860409185246459130317307 2790613777869688695475961)
        ·
          refine ⟨2092960333402266521606971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2790613777869688695475961 2092960333402266521606971)
          ·
            refine ⟨3139440500103399782410457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092960333402266521606971 3139440500103399782410457)
            ·
              refine ⟨2354580375077549836807843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3139440500103399782410457 2354580375077549836807843)
              ·
                refine ⟨3531870562616324755211765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354580375077549836807843 3531870562616324755211765)
                ·
                  refine ⟨331112865245280445801103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3531870562616324755211765 331112865245280445801103)
                  ·
                    rfl

theorem cell22_2901780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_2901780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901780 prefixEnd_2901780 := by exact prefixLift 2901780
  have htrace : WordTrace (prefixWord ++ tailWord_2901780) baseStart_2901780 baseEnd_2901780 := by
    simpa [prefixWord, tailWord_2901780, baseEnd_2901780] using wordTrace_append hprefix tailTrace_2901780
  have hstable : (prefixWord ++ tailWord_2901780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901780).length < 2 ^ (prefixWord ++ tailWord_2901780).sum := by decide
  have hdescent : baseEnd_2901780 < baseStart_2901780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901834 : List Nat := [3, 1, 2, 1, 1, 1, 5, 4, 1, 3]
def baseStart_2901834 : Nat := 118140960795 + 2901834 * 2 ^ 59
def prefixEnd_2901834 : Nat := 4983230072969 + 3 ^ 40 * 2901834 * 2
def baseEnd_2901834 : Nat := 993357081039403196553143

theorem tailTrace_2901834 : CollatzResearch.WordTrace tailWord_2901834 prefixEnd_2901834 993357081039403196553143 := by
  unfold tailWord_2901834
  simp only [CollatzResearch.WordTrace]
  refine ⟨26459645242289621659018139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70559053979438991090715037 26459645242289621659018139)
  ·
    refine ⟨39689467863434432488527209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26459645242289621659018139 39689467863434432488527209)
    ·
      refine ⟨29767100897575824366395407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39689467863434432488527209 29767100897575824366395407)
      ·
        refine ⟨44650651346363736549593111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29767100897575824366395407 44650651346363736549593111)
        ·
          refine ⟨66975977019545604824389667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44650651346363736549593111 66975977019545604824389667)
          ·
            refine ⟨100463965529318407236584501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66975977019545604824389667 100463965529318407236584501)
            ·
              refine ⟨9418496768373600678429797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100463965529318407236584501 9418496768373600678429797)
              ·
                refine ⟨1765968144070050127205587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9418496768373600678429797 1765968144070050127205587)
                ·
                  refine ⟨2648952216105075190808381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765968144070050127205587 2648952216105075190808381)
                  ·
                    refine ⟨993357081039403196553143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2648952216105075190808381 993357081039403196553143)
                    ·
                      rfl

theorem cell22_2901834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_2901834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901834 prefixEnd_2901834 := by exact prefixLift 2901834
  have htrace : WordTrace (prefixWord ++ tailWord_2901834) baseStart_2901834 baseEnd_2901834 := by
    simpa [prefixWord, tailWord_2901834, baseEnd_2901834] using wordTrace_append hprefix tailTrace_2901834
  have hstable : (prefixWord ++ tailWord_2901834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901834).length < 2 ^ (prefixWord ++ tailWord_2901834).sum := by decide
  have hdescent : baseEnd_2901834 < baseStart_2901834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901845 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_2901845 : Nat := 118140960795 + 2901845 * 2 ^ 59
def prefixEnd_2901845 : Nat := 4983230072969 + 3 ^ 40 * 2901845 * 2
def baseEnd_2901845 : Nat := 993360846564202834528109

theorem tailTrace_2901845 : CollatzResearch.WordTrace tailWord_2901845 prefixEnd_2901845 993360846564202834528109 := by
  unfold tailWord_2901845
  simp only [CollatzResearch.WordTrace]
  refine ⟨105838982172118635514722989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70559321448079090343148659 105838982172118635514722989)
  ·
    refine ⟨39689618314544488318021121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105838982172118635514722989 39689618314544488318021121)
    ·
      refine ⟨29767213735908366238515841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39689618314544488318021121 29767213735908366238515841)
      ·
        refine ⟨22325410301931274678886881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29767213735908366238515841 22325410301931274678886881)
        ·
          refine ⟨16744057726448456009165161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22325410301931274678886881 16744057726448456009165161)
          ·
            refine ⟨12558043294836342006873871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16744057726448456009165161 12558043294836342006873871)
            ·
              refine ⟨18837064942254513010310807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12558043294836342006873871 18837064942254513010310807)
              ·
                refine ⟨28255597413381769515466211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18837064942254513010310807 28255597413381769515466211)
                ·
                  refine ⟨42383396120072654273199317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28255597413381769515466211 42383396120072654273199317)
                  ·
                    refine ⟨993360846564202834528109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42383396120072654273199317 993360846564202834528109)
                    ·
                      rfl

theorem cell22_2901845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_2901845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901845 prefixEnd_2901845 := by exact prefixLift 2901845
  have htrace : WordTrace (prefixWord ++ tailWord_2901845) baseStart_2901845 baseEnd_2901845 := by
    simpa [prefixWord, tailWord_2901845, baseEnd_2901845] using wordTrace_append hprefix tailTrace_2901845
  have hstable : (prefixWord ++ tailWord_2901845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901845).length < 2 ^ (prefixWord ++ tailWord_2901845).sum := by decide
  have hdescent : baseEnd_2901845 < baseStart_2901845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901905 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 1, 6]
def baseStart_2901905 : Nat := 118140960795 + 2901905 * 2 ^ 59
def prefixEnd_2901905 : Nat := 4983230072969 + 3 ^ 40 * 2901905 * 2
def baseEnd_2901905 : Nat := 993381385790382678027925

theorem tailTrace_2901905 : CollatzResearch.WordTrace tailWord_2901905 prefixEnd_2901905 993381385790382678027925 := by
  unfold tailWord_2901905
  simp only [CollatzResearch.WordTrace]
  refine ⟨105841170551901265761907169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70560780367934177174604779 105841170551901265761907169)
  ·
    refine ⟨79380877913925949321430377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105841170551901265761907169 79380877913925949321430377)
    ·
      refine ⟨59535658435444461991072783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79380877913925949321430377 59535658435444461991072783)
      ·
        refine ⟨89303487653166692986609175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59535658435444461991072783 89303487653166692986609175)
        ·
          refine ⟨133955231479750039479913763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89303487653166692986609175 133955231479750039479913763)
          ·
            refine ⟨200932847219625059219870645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133955231479750039479913763 200932847219625059219870645)
            ·
              refine ⟨18837454426839849301862873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200932847219625059219870645 18837454426839849301862873)
              ·
                refine ⟨14128090820129886976397155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18837454426839849301862873 14128090820129886976397155)
                ·
                  refine ⟨21192136230194830464595733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14128090820129886976397155 21192136230194830464595733)
                  ·
                    refine ⟨993381385790382678027925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21192136230194830464595733 993381385790382678027925)
                    ·
                      rfl

theorem cell22_2901905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_2901905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901905 prefixEnd_2901905 := by exact prefixLift 2901905
  have htrace : WordTrace (prefixWord ++ tailWord_2901905) baseStart_2901905 baseEnd_2901905 := by
    simpa [prefixWord, tailWord_2901905, baseEnd_2901905] using wordTrace_append hprefix tailTrace_2901905
  have hstable : (prefixWord ++ tailWord_2901905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901905).length < 2 ^ (prefixWord ++ tailWord_2901905).sum := by decide
  have hdescent : baseEnd_2901905 < baseStart_2901905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901937 : List Nat := [1, 2, 2, 4, 2, 3, 8]
def baseStart_2901937 : Nat := 118140960795 + 2901937 * 2 ^ 59
def prefixEnd_2901937 : Nat := 4983230072969 + 3 ^ 40 * 2901937 * 2
def baseEnd_2901937 : Nat := 36792308890531305971401

theorem tailTrace_2901937 : CollatzResearch.WordTrace tailWord_2901937 prefixEnd_2901937 36792308890531305971401 := by
  unfold tailWord_2901937
  simp only [CollatzResearch.WordTrace]
  refine ⟨105842337687785335227072065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70561558458523556818048043 105842337687785335227072065)
  ·
    refine ⟨79381753265839001420304049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105842337687785335227072065 79381753265839001420304049)
    ·
      refine ⟨59536314949379251065228037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79381753265839001420304049 59536314949379251065228037)
      ·
        refine ⟨11163059053008609574730257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59536314949379251065228037 11163059053008609574730257)
        ·
          refine ⟨8372294289756457181047693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11163059053008609574730257 8372294289756457181047693)
          ·
            refine ⟨3139610358658671442892885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8372294289756457181047693 3139610358658671442892885)
            ·
              refine ⟨36792308890531305971401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3139610358658671442892885 36792308890531305971401)
              ·
                rfl

theorem cell22_2901937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 8].length) (baseStart_2901937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2901937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2901937 prefixEnd_2901937 := by exact prefixLift 2901937
  have htrace : WordTrace (prefixWord ++ tailWord_2901937) baseStart_2901937 baseEnd_2901937 := by
    simpa [prefixWord, tailWord_2901937, baseEnd_2901937] using wordTrace_append hprefix tailTrace_2901937
  have hstable : (prefixWord ++ tailWord_2901937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901937).length < 2 ^ (prefixWord ++ tailWord_2901937).sum := by decide
  have hdescent : baseEnd_2901937 < baseStart_2901937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902012 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_2902012 : Nat := 118140960795 + 2902012 * 2 ^ 59
def prefixEnd_2902012 : Nat := 4983230072969 + 3 ^ 40 * 2902012 * 2
def baseEnd_2902012 : Nat := 993418014077070065602597

theorem tailTrace_2902012 : CollatzResearch.WordTrace tailWord_2902012 prefixEnd_2902012 993418014077070065602597 := by
  unfold tailWord_2902012
  simp only [CollatzResearch.WordTrace]
  refine ⟨52922536581256811518026145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70563382108342415357368193 52922536581256811518026145)
  ·
    refine ⟨39691902435942608638519609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52922536581256811518026145 39691902435942608638519609)
    ·
      refine ⟨29768926826956956478889707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39691902435942608638519609 29768926826956956478889707)
      ·
        refine ⟨44653390240435434718334561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29768926826956956478889707 44653390240435434718334561)
        ·
          refine ⟨33490042680326576038750921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44653390240435434718334561 33490042680326576038750921)
          ·
            refine ⟨25117532010244932029063191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33490042680326576038750921 25117532010244932029063191)
            ·
              refine ⟨37676298015367398043594787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25117532010244932029063191 37676298015367398043594787)
              ·
                refine ⟨56514447023051097065392181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37676298015367398043594787 56514447023051097065392181)
                ·
                  refine ⟨5298229408411040349880517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56514447023051097065392181 5298229408411040349880517)
                  ·
                    refine ⟨993418014077070065602597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5298229408411040349880517 993418014077070065602597)
                    ·
                      rfl

theorem cell22_2902012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_2902012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902012 prefixEnd_2902012 := by exact prefixLift 2902012
  have htrace : WordTrace (prefixWord ++ tailWord_2902012) baseStart_2902012 baseEnd_2902012 := by
    simpa [prefixWord, tailWord_2902012, baseEnd_2902012] using wordTrace_append hprefix tailTrace_2902012
  have hstable : (prefixWord ++ tailWord_2902012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902012).length < 2 ^ (prefixWord ++ tailWord_2902012).sum := by decide
  have hdescent : baseEnd_2902012 < baseStart_2902012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902014 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2902014 : Nat := 118140960795 + 2902014 * 2 ^ 59
def prefixEnd_2902014 : Nat := 4983230072969 + 3 ^ 40 * 2902014 * 2
def baseEnd_2902014 : Nat := 993418698717942727052591

theorem tailTrace_2902014 : CollatzResearch.WordTrace tailWord_2902014 prefixEnd_2902014 993418698717942727052591 := by
  unfold tailWord_2902014
  simp only [CollatzResearch.WordTrace]
  refine ⟨13230643263563297172203137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70563430739004251585083397 13230643263563297172203137)
  ·
    refine ⟨9922982447672472879152353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13230643263563297172203137 9922982447672472879152353)
    ·
      refine ⟨7442236835754354659364265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9922982447672472879152353 7442236835754354659364265)
      ·
        refine ⟨5581677626815765994523199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7442236835754354659364265 5581677626815765994523199)
        ·
          refine ⟨8372516440223648991784799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5581677626815765994523199 8372516440223648991784799)
          ·
            refine ⟨12558774660335473487677199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8372516440223648991784799 12558774660335473487677199)
            ·
              refine ⟨18838161990503210231515799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12558774660335473487677199 18838161990503210231515799)
              ·
                refine ⟨28257242985754815347273699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18838161990503210231515799 28257242985754815347273699)
                ·
                  refine ⟨42385864478632223020910549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28257242985754815347273699 42385864478632223020910549)
                  ·
                    refine ⟨993418698717942727052591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42385864478632223020910549 993418698717942727052591)
                    ·
                      rfl

theorem cell22_2902014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2902014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902014 prefixEnd_2902014 := by exact prefixLift 2902014
  have htrace : WordTrace (prefixWord ++ tailWord_2902014) baseStart_2902014 baseEnd_2902014 := by
    simpa [prefixWord, tailWord_2902014, baseEnd_2902014] using wordTrace_append hprefix tailTrace_2902014
  have hstable : (prefixWord ++ tailWord_2902014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902014).length < 2 ^ (prefixWord ++ tailWord_2902014).sum := by decide
  have hdescent : baseEnd_2902014 < baseStart_2902014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902027 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 6]
def baseStart_2902027 : Nat := 118140960795 + 2902027 * 2 ^ 59
def prefixEnd_2902027 : Nat := 4983230072969 + 3 ^ 40 * 2902027 * 2
def baseEnd_2902027 : Nat := 331141049627871675492517

theorem tailTrace_2902027 : CollatzResearch.WordTrace tailWord_2902027 prefixEnd_2902027 331141049627871675492517 := by
  unfold tailWord_2902027
  simp only [CollatzResearch.WordTrace]
  refine ⟨105845620257459280597848335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70563746838306187065232223 105845620257459280597848335)
  ·
    refine ⟨158768430386188920896772503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105845620257459280597848335 158768430386188920896772503)
    ·
      refine ⟨238152645579283381345158755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158768430386188920896772503 238152645579283381345158755)
      ·
        refine ⟨357228968368925072017738133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238152645579283381345158755 357228968368925072017738133)
        ·
          refine ⟨16745107892293362750831475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 357228968368925072017738133 16745107892293362750831475)
          ·
            refine ⟨25117661838440044126247213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16745107892293362750831475 25117661838440044126247213)
            ·
              refine ⟨9419123189415016547342705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25117661838440044126247213 9419123189415016547342705)
              ·
                refine ⟨7064342392061262410507029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9419123189415016547342705 7064342392061262410507029)
                ·
                  refine ⟨331141049627871675492517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7064342392061262410507029 331141049627871675492517)
                  ·
                    rfl

theorem cell22_2902027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 6].length) (baseStart_2902027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902027 prefixEnd_2902027 := by exact prefixLift 2902027
  have htrace : WordTrace (prefixWord ++ tailWord_2902027) baseStart_2902027 baseEnd_2902027 := by
    simpa [prefixWord, tailWord_2902027, baseEnd_2902027] using wordTrace_append hprefix tailTrace_2902027
  have hstable : (prefixWord ++ tailWord_2902027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902027).length < 2 ^ (prefixWord ++ tailWord_2902027).sum := by decide
  have hdescent : baseEnd_2902027 < baseStart_2902027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902059 : List Nat := [1, 1, 1, 1, 2, 1, 4, 6, 2, 3]
def baseStart_2902059 : Nat := 118140960795 + 2902059 * 2 ^ 59
def prefixEnd_2902059 : Nat := 4983230072969 + 3 ^ 40 * 2902059 * 2
def baseEnd_2902059 : Nat := 993434103137577609677453

theorem tailTrace_2902059 : CollatzResearch.WordTrace tailWord_2902059 prefixEnd_2902059 993434103137577609677453 := by
  unfold tailWord_2902059
  simp only [CollatzResearch.WordTrace]
  refine ⟨105846787393343350063013231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70564524928895566708675487 105846787393343350063013231)
  ·
    refine ⟨158770181090015025094519847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105846787393343350063013231 158770181090015025094519847)
    ·
      refine ⟨238155271635022537641779771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158770181090015025094519847 238155271635022537641779771)
      ·
        refine ⟨357232907452533806462669657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238155271635022537641779771 357232907452533806462669657)
        ·
          refine ⟨267924680589400354847002243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357232907452533806462669657 267924680589400354847002243)
          ·
            refine ⟨401887020884100532270503365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267924680589400354847002243 401887020884100532270503365)
            ·
              refine ⟨75353816415768849800719381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 401887020884100532270503365 75353816415768849800719381)
              ·
                refine ⟨3532210144489164834408721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75353816415768849800719381 3532210144489164834408721)
                ·
                  refine ⟨2649157608366873625806541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3532210144489164834408721 2649157608366873625806541)
                  ·
                    refine ⟨993434103137577609677453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2649157608366873625806541 993434103137577609677453)
                    ·
                      rfl

theorem cell22_2902059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 3].length) (baseStart_2902059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902059 prefixEnd_2902059 := by exact prefixLift 2902059
  have htrace : WordTrace (prefixWord ++ tailWord_2902059) baseStart_2902059 baseEnd_2902059 := by
    simpa [prefixWord, tailWord_2902059, baseEnd_2902059] using wordTrace_append hprefix tailTrace_2902059
  have hstable : (prefixWord ++ tailWord_2902059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902059).length < 2 ^ (prefixWord ++ tailWord_2902059).sum := by decide
  have hdescent : baseEnd_2902059 < baseStart_2902059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902087 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 2, 7]
def baseStart_2902087 : Nat := 118140960795 + 2902087 * 2 ^ 59
def prefixEnd_2902087 : Nat := 4983230072969 + 3 ^ 40 * 2902087 * 2
def baseEnd_2902087 : Nat := 993443688109794869977367

theorem tailTrace_2902087 : CollatzResearch.WordTrace tailWord_2902087 prefixEnd_2902087 993443688109794869977367 := by
  unfold tailWord_2902087
  simp only [CollatzResearch.WordTrace]
  refine ⟨105847808637241910845032515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70565205758161273896688343 105847808637241910845032515)
  ·
    refine ⟨158771712955862866267548773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105847808637241910845032515 158771712955862866267548773)
    ·
      refine ⟨29769696179224287425165395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158771712955862866267548773 29769696179224287425165395)
      ·
        refine ⟨44654544268836431137748093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29769696179224287425165395 44654544268836431137748093)
        ·
          refine ⟨16745454100813661676655535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44654544268836431137748093 16745454100813661676655535)
          ·
            refine ⟨25118181151220492514983303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16745454100813661676655535 25118181151220492514983303)
            ·
              refine ⟨37677271726830738772474955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25118181151220492514983303 37677271726830738772474955)
              ·
                refine ⟨56515907590246108158712433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37677271726830738772474955 56515907590246108158712433)
                ·
                  refine ⟨42386930692684581119034325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56515907590246108158712433 42386930692684581119034325)
                  ·
                    refine ⟨993443688109794869977367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42386930692684581119034325 993443688109794869977367)
                    ·
                      rfl

theorem cell22_2902087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_2902087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902087 prefixEnd_2902087 := by exact prefixLift 2902087
  have htrace : WordTrace (prefixWord ++ tailWord_2902087) baseStart_2902087 baseEnd_2902087 := by
    simpa [prefixWord, tailWord_2902087, baseEnd_2902087] using wordTrace_append hprefix tailTrace_2902087
  have hstable : (prefixWord ++ tailWord_2902087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902087).length < 2 ^ (prefixWord ++ tailWord_2902087).sum := by decide
  have hdescent : baseEnd_2902087 < baseStart_2902087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902230 : List Nat := [5, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_2902230 : Nat := 118140960795 + 2902230 * 2 ^ 59
def prefixEnd_2902230 : Nat := 4983230072969 + 3 ^ 40 * 2902230 * 2
def baseEnd_2902230 : Nat := 331164213310730054550643

theorem tailTrace_2902230 : CollatzResearch.WordTrace tailWord_2902230 prefixEnd_2902230 331164213310730054550643 := by
  unfold tailWord_2902230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6615814017232740391718009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70568682850482564178325429 6615814017232740391718009)
  ·
    refine ⟨4961860512924555293788507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6615814017232740391718009 4961860512924555293788507)
    ·
      refine ⟨7442790769386832940682761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4961860512924555293788507 7442790769386832940682761)
      ·
        refine ⟨5582093077040124705512071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7442790769386832940682761 5582093077040124705512071)
        ·
          refine ⟨8373139615560187058268107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5582093077040124705512071 8373139615560187058268107)
          ·
            refine ⟨12559709423340280587402161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8373139615560187058268107 12559709423340280587402161)
            ·
              refine ⟨9419782067505210440551621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12559709423340280587402161 9419782067505210440551621)
              ·
                refine ⟨1766209137657226957603429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9419782067505210440551621 1766209137657226957603429)
                ·
                  refine ⟨331164213310730054550643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1766209137657226957603429 331164213310730054550643)
                  ·
                    rfl

theorem cell22_2902230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_2902230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902230 prefixEnd_2902230 := by exact prefixLift 2902230
  have htrace : WordTrace (prefixWord ++ tailWord_2902230) baseStart_2902230 baseEnd_2902230 := by
    simpa [prefixWord, tailWord_2902230, baseEnd_2902230] using wordTrace_append hprefix tailTrace_2902230
  have hstable : (prefixWord ++ tailWord_2902230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902230).length < 2 ^ (prefixWord ++ tailWord_2902230).sum := by decide
  have hdescent : baseEnd_2902230 < baseStart_2902230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902245 : List Nat := [1, 3, 1, 4, 2, 2, 3, 1, 2, 3]
def baseStart_2902245 : Nat := 118140960795 + 2902245 * 2 ^ 59
def prefixEnd_2902245 : Nat := 4983230072969 + 3 ^ 40 * 2902245 * 2
def baseEnd_2902245 : Nat := 993497774738735124526883

theorem tailTrace_2902245 : CollatzResearch.WordTrace tailWord_2902245 prefixEnd_2902245 993497774738735124526883 := by
  unfold tailWord_2902245
  simp only [CollatzResearch.WordTrace]
  refine ⟨105853571370669503829284189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70569047580446335886189459 105853571370669503829284189)
  ·
    refine ⟨39695089264001063935981571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105853571370669503829284189 39695089264001063935981571)
    ·
      refine ⟨59542633896001595903972357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39695089264001063935981571 59542633896001595903972357)
      ·
        refine ⟨11164243855500299231994817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59542633896001595903972357 11164243855500299231994817)
        ·
          refine ⟨8373182891625224423996113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11164243855500299231994817 8373182891625224423996113)
          ·
            refine ⟨6279887168718918317997085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8373182891625224423996113 6279887168718918317997085)
            ·
              refine ⟨2354957688269594369248907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6279887168718918317997085 2354957688269594369248907)
              ·
                refine ⟨3532436532404391553873361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354957688269594369248907 3532436532404391553873361)
                ·
                  refine ⟨2649327399303293665405021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3532436532404391553873361 2649327399303293665405021)
                  ·
                    refine ⟨993497774738735124526883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2649327399303293665405021 993497774738735124526883)
                    ·
                      rfl

theorem cell22_2902245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_2902245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902245 prefixEnd_2902245 := by exact prefixLift 2902245
  have htrace : WordTrace (prefixWord ++ tailWord_2902245) baseStart_2902245 baseEnd_2902245 := by
    simpa [prefixWord, tailWord_2902245, baseEnd_2902245] using wordTrace_append hprefix tailTrace_2902245
  have hstable : (prefixWord ++ tailWord_2902245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902245).length < 2 ^ (prefixWord ++ tailWord_2902245).sum := by decide
  have hdescent : baseEnd_2902245 < baseStart_2902245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902258 : List Nat := [3, 2, 1, 3, 2, 3, 2, 6]
def baseStart_2902258 : Nat := 118140960795 + 2902258 * 2 ^ 59
def prefixEnd_2902258 : Nat := 4983230072969 + 3 ^ 40 * 2902258 * 2
def baseEnd_2902258 : Nat := 110389136100489713772427

theorem tailTrace_2902258 : CollatzResearch.WordTrace tailWord_2902258 prefixEnd_2902258 110389136100489713772427 := by
  unfold tailWord_2902258
  simp only [CollatzResearch.WordTrace]
  refine ⟨26463511379905601762376857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70569363679748271366338285 26463511379905601762376857)
  ·
    refine ⟨19847633534929201321782643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26463511379905601762376857 19847633534929201321782643)
    ·
      refine ⟨29771450302393801982673965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19847633534929201321782643 29771450302393801982673965)
      ·
        refine ⟨11164293863397675743502737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29771450302393801982673965 11164293863397675743502737)
        ·
          refine ⟨8373220397548256807627053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11164293863397675743502737 8373220397548256807627053)
          ·
            refine ⟨3139957649080596302860145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8373220397548256807627053 3139957649080596302860145)
            ·
              refine ⟨2354968236810447227145109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3139957649080596302860145 2354968236810447227145109)
              ·
                refine ⟨110389136100489713772427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2354968236810447227145109 110389136100489713772427)
                ·
                  rfl

theorem cell22_2902258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_2902258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902258 prefixEnd_2902258 := by exact prefixLift 2902258
  have htrace : WordTrace (prefixWord ++ tailWord_2902258) baseStart_2902258 baseEnd_2902258 := by
    simpa [prefixWord, tailWord_2902258, baseEnd_2902258] using wordTrace_append hprefix tailTrace_2902258
  have hstable : (prefixWord ++ tailWord_2902258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902258).length < 2 ^ (prefixWord ++ tailWord_2902258).sum := by decide
  have hdescent : baseEnd_2902258 < baseStart_2902258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902286 : List Nat := [4, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_2902286 : Nat := 118140960795 + 2902286 * 2 ^ 59
def prefixEnd_2902286 : Nat := 4983230072969 + 3 ^ 40 * 2902286 * 2
def baseEnd_2902286 : Nat := 331170603292208228083919

theorem tailTrace_2902286 : CollatzResearch.WordTrace tailWord_2902286 prefixEnd_2902286 331170603292208228083919 := by
  unfold tailWord_2902286
  simp only [CollatzResearch.WordTrace]
  refine ⟨13231883345440120978940839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70570044509013978554351141 13231883345440120978940839)
  ·
    refine ⟨19847825018160181468411259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13231883345440120978940839 19847825018160181468411259)
    ·
      refine ⟨29771737527240272202616889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19847825018160181468411259 29771737527240272202616889)
      ·
        refine ⟨22328803145430204151962667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29771737527240272202616889 22328803145430204151962667)
        ·
          refine ⟨33493204718145306227944001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22328803145430204151962667 33493204718145306227944001)
          ·
            refine ⟨25119903538608979670958001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33493204718145306227944001 25119903538608979670958001)
            ·
              refine ⟨18839927653956734753218501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25119903538608979670958001 18839927653956734753218501)
              ·
                refine ⟨3532486435116887766228469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18839927653956734753218501 3532486435116887766228469)
                ·
                  refine ⟨331170603292208228083919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3532486435116887766228469 331170603292208228083919)
                  ·
                    rfl

theorem cell22_2902286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_2902286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902286 prefixEnd_2902286 := by exact prefixLift 2902286
  have htrace : WordTrace (prefixWord ++ tailWord_2902286) baseStart_2902286 baseEnd_2902286 := by
    simpa [prefixWord, tailWord_2902286, baseEnd_2902286] using wordTrace_append hprefix tailTrace_2902286
  have hstable : (prefixWord ++ tailWord_2902286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902286).length < 2 ^ (prefixWord ++ tailWord_2902286).sum := by decide
  have hdescent : baseEnd_2902286 < baseStart_2902286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902303 : List Nat := [1, 1, 2, 4, 3, 1, 4, 1, 5]
def baseStart_2902303 : Nat := 118140960795 + 2902303 * 2 ^ 59
def prefixEnd_2902303 : Nat := 4983230072969 + 3 ^ 40 * 2902303 * 2
def baseEnd_2902303 : Nat := 331172543108014102192235

theorem tailTrace_2902303 : CollatzResearch.WordTrace tailWord_2902303 prefixEnd_2902303 331172543108014102192235 := by
  unfold tailWord_2902303
  simp only [CollatzResearch.WordTrace]
  refine ⟨105855686804459379734895563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70570457869639586489930375 105855686804459379734895563)
  ·
    refine ⟨158783530206689069602343345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105855686804459379734895563 158783530206689069602343345)
    ·
      refine ⟨119087647655016802201757509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158783530206689069602343345 119087647655016802201757509)
      ·
        refine ⟨22328933935315650412829533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119087647655016802201757509 22328933935315650412829533)
        ·
          refine ⟨8373350225743368904811075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22328933935315650412829533 8373350225743368904811075)
          ·
            refine ⟨12560025338615053357216613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8373350225743368904811075 12560025338615053357216613)
            ·
              refine ⟨2355004750990322504478115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12560025338615053357216613 2355004750990322504478115)
              ·
                refine ⟨3532507126485483756717173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2355004750990322504478115 3532507126485483756717173)
                ·
                  refine ⟨331172543108014102192235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3532507126485483756717173 331172543108014102192235)
                  ·
                    rfl

theorem cell22_2902303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 5].length) (baseStart_2902303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902303 prefixEnd_2902303 := by exact prefixLift 2902303
  have htrace : WordTrace (prefixWord ++ tailWord_2902303) baseStart_2902303 baseEnd_2902303 := by
    simpa [prefixWord, tailWord_2902303, baseEnd_2902303] using wordTrace_append hprefix tailTrace_2902303
  have hstable : (prefixWord ++ tailWord_2902303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902303).length < 2 ^ (prefixWord ++ tailWord_2902303).sum := by decide
  have hdescent : baseEnd_2902303 < baseStart_2902303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902348 : List Nat := [2, 2, 1, 3, 2, 1, 3, 4, 4]
def baseStart_2902348 : Nat := 118140960795 + 2902348 * 2 ^ 59
def prefixEnd_2902348 : Nat := 4983230072969 + 3 ^ 40 * 2902348 * 2
def baseEnd_2902348 : Nat := 331177677914559063067189

theorem tailTrace_2902348 : CollatzResearch.WordTrace tailWord_2902348 prefixEnd_2902348 331177677914559063067189 := by
  unfold tailWord_2902348
  simp only [CollatzResearch.WordTrace]
  refine ⟨52928664044648176210141849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70571552059530901613522465 52928664044648176210141849)
  ·
    refine ⟨39696498033486132157606387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52928664044648176210141849 39696498033486132157606387)
    ·
      refine ⟨59544747050229198236409581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39696498033486132157606387 59544747050229198236409581)
      ·
        refine ⟨22329280143835949338653593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59544747050229198236409581 22329280143835949338653593)
        ·
          refine ⟨16746960107876962003990195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22329280143835949338653593 16746960107876962003990195)
          ·
            refine ⟨25120440161815443005985293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16746960107876962003990195 25120440161815443005985293)
            ·
              refine ⟨9420165060680791127244485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25120440161815443005985293 9420165060680791127244485)
              ·
                refine ⟨1766280948877648336358341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9420165060680791127244485 1766280948877648336358341)
                ·
                  refine ⟨331177677914559063067189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1766280948877648336358341 331177677914559063067189)
                  ·
                    rfl

theorem cell22_2902348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_2902348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902348 prefixEnd_2902348 := by exact prefixLift 2902348
  have htrace : WordTrace (prefixWord ++ tailWord_2902348) baseStart_2902348 baseEnd_2902348 := by
    simpa [prefixWord, tailWord_2902348, baseEnd_2902348] using wordTrace_append hprefix tailTrace_2902348
  have hstable : (prefixWord ++ tailWord_2902348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902348).length < 2 ^ (prefixWord ++ tailWord_2902348).sum := by decide
  have hdescent : baseEnd_2902348 < baseStart_2902348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902378 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_2902378 : Nat := 118140960795 + 2902378 * 2 ^ 59
def prefixEnd_2902378 : Nat := 4983230072969 + 3 ^ 40 * 2902378 * 2
def baseEnd_2902378 : Nat := 993543303356767110951475

theorem tailTrace_2902378 : CollatzResearch.WordTrace tailWord_2902378 prefixEnd_2902378 993543303356767110951475 := by
  unfold tailWord_2902378
  simp only [CollatzResearch.WordTrace]
  refine ⟨26464605569796916885968947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70572281519458445029250525 26464605569796916885968947)
  ·
    refine ⟨39696908354695375328953421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26464605569796916885968947 39696908354695375328953421)
    ·
      refine ⟨14886340633010765748357533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39696908354695375328953421 14886340633010765748357533)
      ·
        refine ⟨5582377737379037155634075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14886340633010765748357533 5582377737379037155634075)
        ·
          refine ⟨8373566606068555733451113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5582377737379037155634075 8373566606068555733451113)
          ·
            refine ⟨6280174954551416800088335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8373566606068555733451113 6280174954551416800088335)
            ·
              refine ⟨9420262431827125200132503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6280174954551416800088335 9420262431827125200132503)
              ·
                refine ⟨14130393647740687800198755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9420262431827125200132503 14130393647740687800198755)
                ·
                  refine ⟨21195590471611031700298133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14130393647740687800198755 21195590471611031700298133)
                  ·
                    refine ⟨993543303356767110951475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21195590471611031700298133 993543303356767110951475)
                    ·
                      rfl

theorem cell22_2902378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_2902378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902378 prefixEnd_2902378 := by exact prefixLift 2902378
  have htrace : WordTrace (prefixWord ++ tailWord_2902378) baseStart_2902378 baseEnd_2902378 := by
    simpa [prefixWord, tailWord_2902378, baseEnd_2902378] using wordTrace_append hprefix tailTrace_2902378
  have hstable : (prefixWord ++ tailWord_2902378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902378).length < 2 ^ (prefixWord ++ tailWord_2902378).sum := by decide
  have hdescent : baseEnd_2902378 < baseStart_2902378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902436 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_2902436 : Nat := 118140960795 + 2902436 * 2 ^ 59
def prefixEnd_2902436 : Nat := 4983230072969 + 3 ^ 40 * 2902436 * 2
def baseEnd_2902436 : Nat := 993563157942074293001297

theorem tailTrace_2902436 : CollatzResearch.WordTrace tailWord_2902436 prefixEnd_2902436 993563157942074293001297 := by
  unfold tailWord_2902436
  simp only [CollatzResearch.WordTrace]
  refine ⟨52930268856488771724743581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70573691808651695632991441 52930268856488771724743581)
  ·
    refine ⟨19848850821183289396778843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52930268856488771724743581 19848850821183289396778843)
    ·
      refine ⟨29773276231774934095168265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19848850821183289396778843 29773276231774934095168265)
      ·
        refine ⟨22329957173831200571376199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29773276231774934095168265 22329957173831200571376199)
        ·
          refine ⟨33494935760746800857064299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22329957173831200571376199 33494935760746800857064299)
          ·
            refine ⟨50242403641120201285596449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33494935760746800857064299 50242403641120201285596449)
            ·
              refine ⟨37681802730840150964197337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50242403641120201285596449 37681802730840150964197337)
              ·
                refine ⟨28261352048130113223148003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37681802730840150964197337 28261352048130113223148003)
                ·
                  refine ⟨42392028072195169834722005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28261352048130113223148003 42392028072195169834722005)
                  ·
                    refine ⟨993563157942074293001297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42392028072195169834722005 993563157942074293001297)
                    ·
                      rfl

theorem cell22_2902436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_2902436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902436 prefixEnd_2902436 := by exact prefixLift 2902436
  have htrace : WordTrace (prefixWord ++ tailWord_2902436) baseStart_2902436 baseEnd_2902436 := by
    simpa [prefixWord, tailWord_2902436, baseEnd_2902436] using wordTrace_append hprefix tailTrace_2902436
  have hstable : (prefixWord ++ tailWord_2902436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902436).length < 2 ^ (prefixWord ++ tailWord_2902436).sum := by decide
  have hdescent : baseEnd_2902436 < baseStart_2902436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902451 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 7, 4]
def baseStart_2902451 : Nat := 118140960795 + 2902451 * 2 ^ 59
def prefixEnd_2902451 : Nat := 4983230072969 + 3 ^ 40 * 2902451 * 2
def baseEnd_2902451 : Nat := 993568292748619253876251

theorem tailTrace_2902451 : CollatzResearch.WordTrace tailWord_2902451 prefixEnd_2902451 993568292748619253876251 := by
  unfold tailWord_2902451
  simp only [CollatzResearch.WordTrace]
  refine ⟨105861084807923201011283207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70574056538615467340855471 105861084807923201011283207)
  ·
    refine ⟨158791627211884801516924811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105861084807923201011283207 158791627211884801516924811)
    ·
      refine ⟨238187440817827202275387217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158791627211884801516924811 238187440817827202275387217)
      ·
        refine ⟨178640580613370401706540413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238187440817827202275387217 178640580613370401706540413)
        ·
          refine ⟨66990217730013900639952655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178640580613370401706540413 66990217730013900639952655)
          ·
            refine ⟨100485326595020850959928983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66990217730013900639952655 100485326595020850959928983)
            ·
              refine ⟨150727989892531276439893475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100485326595020850959928983 150727989892531276439893475)
              ·
                refine ⟨226091984838796914659840213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150727989892531276439893475 226091984838796914659840213)
                ·
                  refine ⟨5299030894659302687340005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 226091984838796914659840213 5299030894659302687340005)
                  ·
                    refine ⟨993568292748619253876251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5299030894659302687340005 993568292748619253876251)
                    ·
                      rfl

theorem cell22_2902451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 4].length) (baseStart_2902451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902451 prefixEnd_2902451 := by exact prefixLift 2902451
  have htrace : WordTrace (prefixWord ++ tailWord_2902451) baseStart_2902451 baseEnd_2902451 := by
    simpa [prefixWord, tailWord_2902451, baseEnd_2902451] using wordTrace_append hprefix tailTrace_2902451
  have hstable : (prefixWord ++ tailWord_2902451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902451).length < 2 ^ (prefixWord ++ tailWord_2902451).sum := by decide
  have hdescent : baseEnd_2902451 < baseStart_2902451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902481 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 5, 5]
def baseStart_2902481 : Nat := 118140960795 + 2902481 * 2 ^ 59
def prefixEnd_2902481 : Nat := 4983230072969 + 3 ^ 40 * 2902481 * 2
def baseEnd_2902481 : Nat := 993578562361709175626159

theorem tailTrace_2902481 : CollatzResearch.WordTrace tailWord_2902481 prefixEnd_2902481 993578562361709175626159 := by
  unfold tailWord_2902481
  simp only [CollatzResearch.WordTrace]
  refine ⟨105862178997814516134875297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70574785998543010756583531 105862178997814516134875297)
  ·
    refine ⟨79396634248360887101156473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105862178997814516134875297 79396634248360887101156473)
    ·
      refine ⟨59547475686270665325867355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79396634248360887101156473 59547475686270665325867355)
      ·
        refine ⟨89321213529405997988801033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59547475686270665325867355 89321213529405997988801033)
        ·
          refine ⟨66990910147054498491600775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89321213529405997988801033 66990910147054498491600775)
          ·
            refine ⟨100486365220581747737401163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66990910147054498491600775 100486365220581747737401163)
            ·
              refine ⟨150729547830872621606101745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100486365220581747737401163 150729547830872621606101745)
              ·
                refine ⟨113047160873154466204576309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150729547830872621606101745 113047160873154466204576309)
                ·
                  refine ⟨10598171331858231206679029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113047160873154466204576309 10598171331858231206679029)
                  ·
                    refine ⟨993578562361709175626159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10598171331858231206679029 993578562361709175626159)
                    ·
                      rfl

theorem cell22_2902481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_2902481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902481 prefixEnd_2902481 := by exact prefixLift 2902481
  have htrace : WordTrace (prefixWord ++ tailWord_2902481) baseStart_2902481 baseEnd_2902481 := by
    simpa [prefixWord, tailWord_2902481, baseEnd_2902481] using wordTrace_append hprefix tailTrace_2902481
  have hstable : (prefixWord ++ tailWord_2902481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902481).length < 2 ^ (prefixWord ++ tailWord_2902481).sum := by decide
  have hdescent : baseEnd_2902481 < baseStart_2902481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902485 : List Nat := [1, 3, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_2902485 : Nat := 118140960795 + 2902485 * 2 ^ 59
def prefixEnd_2902485 : Nat := 4983230072969 + 3 ^ 40 * 2902485 * 2
def baseEnd_2902485 : Nat := 993579931643454498526147

theorem tailTrace_2902485 : CollatzResearch.WordTrace tailWord_2902485 prefixEnd_2902485 993579931643454498526147 := by
  unfold tailWord_2902485
  simp only [CollatzResearch.WordTrace]
  refine ⟨105862324889800024818020909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70574883259866683212013939 105862324889800024818020909)
  ·
    refine ⟨39698371833675009306757841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105862324889800024818020909 39698371833675009306757841)
    ·
      refine ⟨29773778875256256980068381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39698371833675009306757841 29773778875256256980068381)
      ·
        refine ⟨11165167078221096367525643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29773778875256256980068381 11165167078221096367525643)
        ·
          refine ⟨16747750617331644551288465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11165167078221096367525643 16747750617331644551288465)
          ·
            refine ⟨12560812962998733413466349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16747750617331644551288465 12560812962998733413466349)
            ·
              refine ⟨4710304861124525030049881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12560812962998733413466349 4710304861124525030049881)
              ·
                refine ⟨3532728645843393772537411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4710304861124525030049881 3532728645843393772537411)
                ·
                  refine ⟨5299092968765090658806117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3532728645843393772537411 5299092968765090658806117)
                  ·
                    refine ⟨993579931643454498526147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5299092968765090658806117 993579931643454498526147)
                    ·
                      rfl

theorem cell22_2902485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_2902485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902485 prefixEnd_2902485 := by exact prefixLift 2902485
  have htrace : WordTrace (prefixWord ++ tailWord_2902485) baseStart_2902485 baseEnd_2902485 := by
    simpa [prefixWord, tailWord_2902485, baseEnd_2902485] using wordTrace_append hprefix tailTrace_2902485
  have hstable : (prefixWord ++ tailWord_2902485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902485).length < 2 ^ (prefixWord ++ tailWord_2902485).sum := by decide
  have hdescent : baseEnd_2902485 < baseStart_2902485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902513 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 2, 4]
def baseStart_2902513 : Nat := 118140960795 + 2902513 * 2 ^ 59
def prefixEnd_2902513 : Nat := 4983230072969 + 3 ^ 40 * 2902513 * 2
def baseEnd_2902513 : Nat := 993589516615671758826061

theorem tailTrace_2902513 : CollatzResearch.WordTrace tailWord_2902513 prefixEnd_2902513 993589516615671758826061 := by
  unfold tailWord_2902513
  simp only [CollatzResearch.WordTrace]
  refine ⟨105863346133698585600040193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70575564089132390400026795 105863346133698585600040193)
  ·
    refine ⟨79397509600273939200030145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105863346133698585600040193 79397509600273939200030145)
    ·
      refine ⟨59548132200205454400022609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79397509600273939200030145 59548132200205454400022609)
      ·
        refine ⟨44661099150154090800016957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59548132200205454400022609 44661099150154090800016957)
        ·
          refine ⟨16747912181307784050006359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44661099150154090800016957 16747912181307784050006359)
          ·
            refine ⟨25121868271961676075009539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16747912181307784050006359 25121868271961676075009539)
            ·
              refine ⟨37682802407942514112514309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25121868271961676075009539 37682802407942514112514309)
              ·
                refine ⟨7065525451489221396096433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37682802407942514112514309 7065525451489221396096433)
                ·
                  refine ⟨5299144088616916047072325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7065525451489221396096433 5299144088616916047072325)
                  ·
                    refine ⟨993589516615671758826061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5299144088616916047072325 993589516615671758826061)
                    ·
                      rfl

theorem cell22_2902513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_2902513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902513 prefixEnd_2902513 := by exact prefixLift 2902513
  have htrace : WordTrace (prefixWord ++ tailWord_2902513) baseStart_2902513 baseEnd_2902513 := by
    simpa [prefixWord, tailWord_2902513, baseEnd_2902513] using wordTrace_append hprefix tailTrace_2902513
  have hstable : (prefixWord ++ tailWord_2902513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902513).length < 2 ^ (prefixWord ++ tailWord_2902513).sum := by decide
  have hdescent : baseEnd_2902513 < baseStart_2902513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902515 : List Nat := [1, 1, 1, 2, 2, 2, 6, 2, 2, 3]
def baseStart_2902515 : Nat := 118140960795 + 2902515 * 2 ^ 59
def prefixEnd_2902515 : Nat := 4983230072969 + 3 ^ 40 * 2902515 * 2
def baseEnd_2902515 : Nat := 993590201256544420276055

theorem tailTrace_2902515 : CollatzResearch.WordTrace tailWord_2902515 prefixEnd_2902515 993590201256544420276055 := by
  unfold tailWord_2902515
  simp only [CollatzResearch.WordTrace]
  refine ⟨105863419079691339941612999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70575612719794226627741999 105863419079691339941612999)
  ·
    refine ⟨158795128619537009912419499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105863419079691339941612999 158795128619537009912419499)
    ·
      refine ⟨238192692929305514868629249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158795128619537009912419499 238192692929305514868629249)
      ·
        refine ⟨178644519696979136151471937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238192692929305514868629249 178644519696979136151471937)
        ·
          refine ⟨133983389772734352113603953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178644519696979136151471937 133983389772734352113603953)
          ·
            refine ⟨100487542329550764085202965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133983389772734352113603953 100487542329550764085202965)
            ·
              refine ⟨4710353546697692066493889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100487542329550764085202965 4710353546697692066493889)
              ·
                refine ⟨3532765160023269049870417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4710353546697692066493889 3532765160023269049870417)
                ·
                  refine ⟨2649573870017451787402813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3532765160023269049870417 2649573870017451787402813)
                  ·
                    refine ⟨993590201256544420276055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2649573870017451787402813 993590201256544420276055)
                    ·
                      rfl

theorem cell22_2902515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 3].length) (baseStart_2902515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902515 prefixEnd_2902515 := by exact prefixLift 2902515
  have htrace : WordTrace (prefixWord ++ tailWord_2902515) baseStart_2902515 baseEnd_2902515 := by
    simpa [prefixWord, tailWord_2902515, baseEnd_2902515] using wordTrace_append hprefix tailTrace_2902515
  have hstable : (prefixWord ++ tailWord_2902515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902515).length < 2 ^ (prefixWord ++ tailWord_2902515).sum := by decide
  have hdescent : baseEnd_2902515 < baseStart_2902515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902532 : List Nat := [2, 3, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_2902532 : Nat := 118140960795 + 2902532 * 2 ^ 59
def prefixEnd_2902532 : Nat := 4983230072969 + 3 ^ 40 * 2902532 * 2
def baseEnd_2902532 : Nat := 993596020703962042601003

theorem tailTrace_2902532 : CollatzResearch.WordTrace tailWord_2902532 prefixEnd_2902532 993596020703962042601003 := by
  unfold tailWord_2902532
  simp only [CollatzResearch.WordTrace]
  refine ⟨52932019560314875922490925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70576026080419834563321233 52932019560314875922490925)
  ·
    refine ⟨19849507335118078470934097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52932019560314875922490925 19849507335118078470934097)
    ·
      refine ⟨14887130501338558853200573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19849507335118078470934097 14887130501338558853200573)
      ·
        refine ⟨5582673938001959569950215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14887130501338558853200573 5582673938001959569950215)
        ·
          refine ⟨8374010907002939354925323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5582673938001959569950215 8374010907002939354925323)
          ·
            refine ⟨12561016360504409032387985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8374010907002939354925323 12561016360504409032387985)
            ·
              refine ⟨9420762270378306774290989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12561016360504409032387985 9420762270378306774290989)
              ·
                refine ⟨3532785851391865040359121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9420762270378306774290989 3532785851391865040359121)
                ·
                  refine ⟨2649589388543898780269341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3532785851391865040359121 2649589388543898780269341)
                  ·
                    refine ⟨993596020703962042601003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2649589388543898780269341 993596020703962042601003)
                    ·
                      rfl

theorem cell22_2902532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_2902532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902532 prefixEnd_2902532 := by exact prefixLift 2902532
  have htrace : WordTrace (prefixWord ++ tailWord_2902532) baseStart_2902532 baseEnd_2902532 := by
    simpa [prefixWord, tailWord_2902532, baseEnd_2902532] using wordTrace_append hprefix tailTrace_2902532
  have hstable : (prefixWord ++ tailWord_2902532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902532).length < 2 ^ (prefixWord ++ tailWord_2902532).sum := by decide
  have hdescent : baseEnd_2902532 < baseStart_2902532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902534 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2902534 : Nat := 118140960795 + 2902534 * 2 ^ 59
def prefixEnd_2902534 : Nat := 4983230072969 + 3 ^ 40 * 2902534 * 2
def baseEnd_2902534 : Nat := 331198901781611568016999

theorem tailTrace_2902534 : CollatzResearch.WordTrace tailWord_2902534 prefixEnd_2902534 331198901781611568016999 := by
  unfold tailWord_2902534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3308253502081953318329833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70576074711081670791036437 3308253502081953318329833)
  ·
    refine ⟨2481190126561464988747375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3308253502081953318329833 2481190126561464988747375)
    ·
      refine ⟨3721785189842197483121063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2481190126561464988747375 3721785189842197483121063)
      ·
        refine ⟨5582677784763296224681595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3721785189842197483121063 5582677784763296224681595)
        ·
          refine ⟨8374016677144944337022393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5582677784763296224681595 8374016677144944337022393)
          ·
            refine ⟨6280512507858708252766795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8374016677144944337022393 6280512507858708252766795)
            ·
              refine ⟨9420768761788062379150193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6280512507858708252766795 9420768761788062379150193)
              ·
                refine ⟨7065576571341046784362645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9420768761788062379150193 7065576571341046784362645)
                ·
                  refine ⟨331198901781611568016999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7065576571341046784362645 331198901781611568016999)
                  ·
                    rfl

theorem cell22_2902534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2902534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902534 prefixEnd_2902534 := by exact prefixLift 2902534
  have htrace : WordTrace (prefixWord ++ tailWord_2902534) baseStart_2902534 baseEnd_2902534 := by
    simpa [prefixWord, tailWord_2902534, baseEnd_2902534] using wordTrace_append hprefix tailTrace_2902534
  have hstable : (prefixWord ++ tailWord_2902534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902534).length < 2 ^ (prefixWord ++ tailWord_2902534).sum := by decide
  have hdescent : baseEnd_2902534 < baseStart_2902534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902543 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 5, 3]
def baseStart_2902543 : Nat := 118140960795 + 2902543 * 2 ^ 59
def prefixEnd_2902543 : Nat := 4983230072969 + 3 ^ 40 * 2902543 * 2
def baseEnd_2902543 : Nat := 993599786228761680575969

theorem tailTrace_2902543 : CollatzResearch.WordTrace tailWord_2902543 prefixEnd_2902543 993599786228761680575969 := by
  unfold tailWord_2902543
  simp only [CollatzResearch.WordTrace]
  refine ⟨105864440323589900723632283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70576293549059933815754855 105864440323589900723632283)
  ·
    refine ⟨158796660485384851085448425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105864440323589900723632283 158796660485384851085448425)
    ·
      refine ⟨119097495364038638314086319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158796660485384851085448425 119097495364038638314086319)
      ·
        refine ⟨178646243046057957471129479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119097495364038638314086319 178646243046057957471129479)
        ·
          refine ⟨267969364569086936206694219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178646243046057957471129479 267969364569086936206694219)
          ·
            refine ⟨401954046853630404310041329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267969364569086936206694219 401954046853630404310041329)
            ·
              refine ⟨301465535140222803232530997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401954046853630404310041329 301465535140222803232530997)
              ·
                refine ⟨28262393919395887803049781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 301465535140222803232530997 28262393919395887803049781)
                ·
                  refine ⟨2649599429943364481535917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28262393919395887803049781 2649599429943364481535917)
                  ·
                    refine ⟨993599786228761680575969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2649599429943364481535917 993599786228761680575969)
                    ·
                      rfl

theorem cell22_2902543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 3].length) (baseStart_2902543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902543 prefixEnd_2902543 := by exact prefixLift 2902543
  have htrace : WordTrace (prefixWord ++ tailWord_2902543) baseStart_2902543 baseEnd_2902543 := by
    simpa [prefixWord, tailWord_2902543, baseEnd_2902543] using wordTrace_append hprefix tailTrace_2902543
  have hstable : (prefixWord ++ tailWord_2902543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902543).length < 2 ^ (prefixWord ++ tailWord_2902543).sum := by decide
  have hdescent : baseEnd_2902543 < baseStart_2902543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902577 : List Nat := [1, 2, 2, 3, 1, 1, 4, 4, 1, 3]
def baseStart_2902577 : Nat := 118140960795 + 2902577 * 2 ^ 59
def prefixEnd_2902577 : Nat := 4983230072969 + 3 ^ 40 * 2902577 * 2
def baseEnd_2902577 : Nat := 993611425123596925225865

theorem tailTrace_2902577 : CollatzResearch.WordTrace tailWord_2902577 prefixEnd_2902577 993611425123596925225865 := by
  unfold tailWord_2902577
  simp only [CollatzResearch.WordTrace]
  refine ⟨105865680405466724530369985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70577120270311149686913323 105865680405466724530369985)
  ·
    refine ⟨79399260304100043397777489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105865680405466724530369985 79399260304100043397777489)
    ·
      refine ⟨59549445228075032548333117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79399260304100043397777489 59549445228075032548333117)
      ·
        refine ⟨22331041960528137205624919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59549445228075032548333117 22331041960528137205624919)
        ·
          refine ⟨33496562940792205808437379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22331041960528137205624919 33496562940792205808437379)
          ·
            refine ⟨50244844411188308712656069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33496562940792205808437379 50244844411188308712656069)
            ·
              refine ⟨9420908327097807883623013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50244844411188308712656069 9420908327097807883623013)
              ·
                refine ⟨1766420311330838978179315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9420908327097807883623013 1766420311330838978179315)
                ·
                  refine ⟨2649630466996258467268973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1766420311330838978179315 2649630466996258467268973)
                  ·
                    refine ⟨993611425123596925225865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2649630466996258467268973 993611425123596925225865)
                    ·
                      rfl

theorem cell22_2902577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_2902577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902577 prefixEnd_2902577 := by exact prefixLift 2902577
  have htrace : WordTrace (prefixWord ++ tailWord_2902577) baseStart_2902577 baseEnd_2902577 := by
    simpa [prefixWord, tailWord_2902577, baseEnd_2902577] using wordTrace_append hprefix tailTrace_2902577
  have hstable : (prefixWord ++ tailWord_2902577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902577).length < 2 ^ (prefixWord ++ tailWord_2902577).sum := by decide
  have hdescent : baseEnd_2902577 < baseStart_2902577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902596 : List Nat := [2, 3, 5, 1, 1, 2, 2, 6]
def baseStart_2902596 : Nat := 118140960795 + 2902596 * 2 ^ 59
def prefixEnd_2902596 : Nat := 4983230072969 + 3 ^ 40 * 2902596 * 2
def baseEnd_2902596 : Nat := 110401992134654134333423

theorem tailTrace_2902596 : CollatzResearch.WordTrace tailWord_2902596 prefixEnd_2902596 110401992134654134333423 := by
  unfold tailWord_2902596
  simp only [CollatzResearch.WordTrace]
  refine ⟨52933186696198945387655821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70577582261598593850207761 52933186696198945387655821)
  ·
    refine ⟨19849945011074604520370933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52933186696198945387655821 19849945011074604520370933)
    ·
      refine ⟨1860932344788244173784775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19849945011074604520370933 1860932344788244173784775)
      ·
        refine ⟨2791398517182366260677163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1860932344788244173784775 2791398517182366260677163)
        ·
          refine ⟨4187097775773549391015745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2791398517182366260677163 4187097775773549391015745)
          ·
            refine ⟨3140323331830162043261809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4187097775773549391015745 3140323331830162043261809)
            ·
              refine ⟨2355242498872621532446357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3140323331830162043261809 2355242498872621532446357)
              ·
                refine ⟨110401992134654134333423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2355242498872621532446357 110401992134654134333423)
                ·
                  rfl

theorem cell22_2902596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 6].length) (baseStart_2902596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902596 prefixEnd_2902596 := by exact prefixLift 2902596
  have htrace : WordTrace (prefixWord ++ tailWord_2902596) baseStart_2902596 baseEnd_2902596 := by
    simpa [prefixWord, tailWord_2902596, baseEnd_2902596] using wordTrace_append hprefix tailTrace_2902596
  have hstable : (prefixWord ++ tailWord_2902596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902596).length < 2 ^ (prefixWord ++ tailWord_2902596).sum := by decide
  have hdescent : baseEnd_2902596 < baseStart_2902596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902603 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 3, 4]
def baseStart_2902603 : Nat := 118140960795 + 2902603 * 2 ^ 59
def prefixEnd_2902603 : Nat := 4983230072969 + 3 ^ 40 * 2902603 * 2
def baseEnd_2902603 : Nat := 993620325454941524075785

theorem tailTrace_2902603 : CollatzResearch.WordTrace tailWord_2902603 prefixEnd_2902603 993620325454941524075785 := by
  unfold tailWord_2902603
  simp only [CollatzResearch.WordTrace]
  refine ⟨105866628703372530970816463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70577752468915020647210975 105866628703372530970816463)
  ·
    refine ⟨158799943055058796456224695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105866628703372530970816463 158799943055058796456224695)
    ·
      refine ⟨238199914582588194684337043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158799943055058796456224695 238199914582588194684337043)
      ·
        refine ⟨357299871873882292026505565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238199914582588194684337043 357299871873882292026505565)
        ·
          refine ⟨133987451952705859509939587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357299871873882292026505565 133987451952705859509939587)
          ·
            refine ⟨200981177929058789264909381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133987451952705859509939587 200981177929058789264909381)
            ·
              refine ⟨37683970861698522987170509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200981177929058789264909381 37683970861698522987170509)
              ·
                refine ⟨14131489073136946120188941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37683970861698522987170509 14131489073136946120188941)
                ·
                  refine ⟨5299308402426354795070853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14131489073136946120188941 5299308402426354795070853)
                  ·
                    refine ⟨993620325454941524075785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5299308402426354795070853 993620325454941524075785)
                    ·
                      rfl

theorem cell22_2902603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 4].length) (baseStart_2902603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902603 prefixEnd_2902603 := by exact prefixLift 2902603
  have htrace : WordTrace (prefixWord ++ tailWord_2902603) baseStart_2902603 baseEnd_2902603 := by
    simpa [prefixWord, tailWord_2902603, baseEnd_2902603] using wordTrace_append hprefix tailTrace_2902603
  have hstable : (prefixWord ++ tailWord_2902603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902603).length < 2 ^ (prefixWord ++ tailWord_2902603).sum := by decide
  have hdescent : baseEnd_2902603 < baseStart_2902603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902663 : List Nat := [1, 1, 4, 2, 1, 2, 1, 10]
def baseStart_2902663 : Nat := 118140960795 + 2902663 * 2 ^ 59
def prefixEnd_2902663 : Nat := 4983230072969 + 3 ^ 40 * 2902663 * 2
def baseEnd_2902663 : Nat := 110404540520124596397289

theorem tailTrace_2902663 : CollatzResearch.WordTrace tailWord_2902663 prefixEnd_2902663 110404540520124596397289 := by
  unfold tailWord_2902663
  simp only [CollatzResearch.WordTrace]
  refine ⟨105868817083155161218000643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70579211388770107478667095 105868817083155161218000643)
  ·
    refine ⟨158803225624732741827000965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105868817083155161218000643 158803225624732741827000965)
    ·
      refine ⟨29775604804637389092562681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158803225624732741827000965 29775604804637389092562681)
      ·
        refine ⟨22331703603478041819422011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29775604804637389092562681 22331703603478041819422011)
        ·
          refine ⟨33497555405217062729133017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22331703603478041819422011 33497555405217062729133017)
          ·
            refine ⟨25123166553912797046849763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33497555405217062729133017 25123166553912797046849763)
            ·
              refine ⟨37684749830869195570274645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25123166553912797046849763 37684749830869195570274645)
              ·
                refine ⟨110404540520124596397289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37684749830869195570274645 110404540520124596397289)
                ·
                  rfl

theorem cell22_2902663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 10].length) (baseStart_2902663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902663 prefixEnd_2902663 := by exact prefixLift 2902663
  have htrace : WordTrace (prefixWord ++ tailWord_2902663) baseStart_2902663 baseEnd_2902663 := by
    simpa [prefixWord, tailWord_2902663, baseEnd_2902663] using wordTrace_append hprefix tailTrace_2902663
  have hstable : (prefixWord ++ tailWord_2902663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902663).length < 2 ^ (prefixWord ++ tailWord_2902663).sum := by decide
  have hdescent : baseEnd_2902663 < baseStart_2902663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902684 : List Nat := [2, 2, 3, 2, 2, 2, 2, 2, 2, 3]
def baseStart_2902684 : Nat := 118140960795 + 2902684 * 2 ^ 59
def prefixEnd_2902684 : Nat := 4983230072969 + 3 ^ 40 * 2902684 * 2
def baseEnd_2902684 : Nat := 993648053410284312800537

theorem tailTrace_2902684 : CollatzResearch.WordTrace tailWord_2902684 prefixEnd_2902684 993648053410284312800537 := by
  unfold tailWord_2902684
  simp only [CollatzResearch.WordTrace]
  refine ⟨52934791508039540902257553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70579722010719387869676737 52934791508039540902257553)
  ·
    refine ⟨39701093631029655676693165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52934791508039540902257553 39701093631029655676693165)
    ·
      refine ⟨14887910111636120878759937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39701093631029655676693165 14887910111636120878759937)
      ·
        refine ⟨11165932583727090659069953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14887910111636120878759937 11165932583727090659069953)
        ·
          refine ⟨8374449437795317994302465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11165932583727090659069953 8374449437795317994302465)
          ·
            refine ⟨6280837078346488495726849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8374449437795317994302465 6280837078346488495726849)
            ·
              refine ⟨4710627808759866371795137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6280837078346488495726849 4710627808759866371795137)
              ·
                refine ⟨3532970856569899778846353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4710627808759866371795137 3532970856569899778846353)
                ·
                  refine ⟨2649728142427424834134765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3532970856569899778846353 2649728142427424834134765)
                  ·
                    refine ⟨993648053410284312800537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2649728142427424834134765 993648053410284312800537)
                    ·
                      rfl

theorem cell22_2902684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_2902684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902684 prefixEnd_2902684 := by exact prefixLift 2902684
  have htrace : WordTrace (prefixWord ++ tailWord_2902684) baseStart_2902684 baseEnd_2902684 := by
    simpa [prefixWord, tailWord_2902684, baseEnd_2902684] using wordTrace_append hprefix tailTrace_2902684
  have hstable : (prefixWord ++ tailWord_2902684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902684).length < 2 ^ (prefixWord ++ tailWord_2902684).sum := by decide
  have hdescent : baseEnd_2902684 < baseStart_2902684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902785 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2902785 : Nat := 118140960795 + 2902785 * 2 ^ 59
def prefixEnd_2902785 : Nat := 4983230072969 + 3 ^ 40 * 2902785 * 2
def baseEnd_2902785 : Nat := 993682627774353716025227

theorem tailTrace_2902785 : CollatzResearch.WordTrace tailWord_2902785 prefixEnd_2902785 993682627774353716025227 := by
  unfold tailWord_2902785
  simp only [CollatzResearch.WordTrace]
  refine ⟨105873266788713176053941809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70582177859142117369294539 105873266788713176053941809)
  ·
    refine ⟨79404950091534882040456357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105873266788713176053941809 79404950091534882040456357)
    ·
      refine ⟨14888428142162790382585567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79404950091534882040456357 14888428142162790382585567)
      ·
        refine ⟨22332642213244185573878351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14888428142162790382585567 22332642213244185573878351)
        ·
          refine ⟨33498963319866278360817527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22332642213244185573878351 33498963319866278360817527)
          ·
            refine ⟨50248444979799417541226291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33498963319866278360817527 50248444979799417541226291)
            ·
              refine ⟨75372667469699126311839437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50248444979799417541226291 75372667469699126311839437)
              ·
                refine ⟨28264750301137172366939789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75372667469699126311839437 28264750301137172366939789)
                ·
                  refine ⟨10599281362926439637602421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28264750301137172366939789 10599281362926439637602421)
                  ·
                    refine ⟨993682627774353716025227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10599281362926439637602421 993682627774353716025227)
                    ·
                      rfl

theorem cell22_2902785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2902785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902785 prefixEnd_2902785 := by exact prefixLift 2902785
  have htrace : WordTrace (prefixWord ++ tailWord_2902785) baseStart_2902785 baseEnd_2902785 := by
    simpa [prefixWord, tailWord_2902785, baseEnd_2902785] using wordTrace_append hprefix tailTrace_2902785
  have hstable : (prefixWord ++ tailWord_2902785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902785).length < 2 ^ (prefixWord ++ tailWord_2902785).sum := by decide
  have hdescent : baseEnd_2902785 < baseStart_2902785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902815 : List Nat := [1, 1, 2, 4, 2, 2, 1, 9]
def baseStart_2902815 : Nat := 118140960795 + 2902815 * 2 ^ 59
def prefixEnd_2902815 : Nat := 4983230072969 + 3 ^ 40 * 2902815 * 2
def baseEnd_2902815 : Nat := 110410321931938181975015

theorem tailTrace_2902815 : CollatzResearch.WordTrace tailWord_2902815 prefixEnd_2902815 110410321931938181975015 := by
  unfold tailWord_2902815
  simp only [CollatzResearch.WordTrace]
  refine ⟨105874360978604491177533899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70582907319069660785022599 105874360978604491177533899)
  ·
    refine ⟨158811541467906736766300849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105874360978604491177533899 158811541467906736766300849)
    ·
      refine ⟨119108656100930052574725637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158811541467906736766300849 119108656100930052574725637)
      ·
        refine ⟨22332873018924384857761057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119108656100930052574725637 22332873018924384857761057)
        ·
          refine ⟨16749654764193288643320793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22332873018924384857761057 16749654764193288643320793)
          ·
            refine ⟨12562241073144966482490595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16749654764193288643320793 12562241073144966482490595)
            ·
              refine ⟨18843361609717449723735893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12562241073144966482490595 18843361609717449723735893)
              ·
                refine ⟨110410321931938181975015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18843361609717449723735893 110410321931938181975015)
                ·
                  rfl

theorem cell22_2902815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 9].length) (baseStart_2902815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902815 prefixEnd_2902815 := by exact prefixLift 2902815
  have htrace : WordTrace (prefixWord ++ tailWord_2902815) baseStart_2902815 baseEnd_2902815 := by
    simpa [prefixWord, tailWord_2902815, baseEnd_2902815] using wordTrace_append hprefix tailTrace_2902815
  have hstable : (prefixWord ++ tailWord_2902815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902815).length < 2 ^ (prefixWord ++ tailWord_2902815).sum := by decide
  have hdescent : baseEnd_2902815 < baseStart_2902815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902849 : List Nat := [1, 2, 5, 3, 2, 9]
def baseStart_2902849 : Nat := 118140960795 + 2902849 * 2 ^ 59
def prefixEnd_2902849 : Nat := 4983230072969 + 3 ^ 40 * 2902849 * 2
def baseEnd_2902849 : Nat := 12267957238052825708951

theorem tailTrace_2902849 : CollatzResearch.WordTrace tailWord_2902849 prefixEnd_2902849 12267957238052825708951 := by
  unfold tailWord_2902849
  simp only [CollatzResearch.WordTrace]
  refine ⟨105875601060481314984271601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70583734040320876656181067 105875601060481314984271601)
  ·
    refine ⟨79406700795360986238203701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105875601060481314984271601 79406700795360986238203701)
    ·
      refine ⟨7444378199565092459831597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79406700795360986238203701 7444378199565092459831597)
      ·
        refine ⟨2791641824836909672436849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7444378199565092459831597 2791641824836909672436849)
        ·
          refine ⟨2093731368627682254327637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2791641824836909672436849 2093731368627682254327637)
          ·
            refine ⟨12267957238052825708951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2093731368627682254327637 12267957238052825708951)
            ·
              rfl

theorem cell22_2902849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 9].length) (baseStart_2902849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902849 prefixEnd_2902849 := by exact prefixLift 2902849
  have htrace : WordTrace (prefixWord ++ tailWord_2902849) baseStart_2902849 baseEnd_2902849 := by
    simpa [prefixWord, tailWord_2902849, baseEnd_2902849] using wordTrace_append hprefix tailTrace_2902849
  have hstable : (prefixWord ++ tailWord_2902849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902849).length < 2 ^ (prefixWord ++ tailWord_2902849).sum := by decide
  have hdescent : baseEnd_2902849 < baseStart_2902849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902969 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 2, 4]
def baseStart_2902969 : Nat := 118140960795 + 2902969 * 2 ^ 59
def prefixEnd_2902969 : Nat := 4983230072969 + 3 ^ 40 * 2902969 * 2
def baseEnd_2902969 : Nat := 993745614734638569424663

theorem tailTrace_2902969 : CollatzResearch.WordTrace tailWord_2902969 prefixEnd_2902969 993745614734638569424663 := by
  unfold tailWord_2902969
  simp only [CollatzResearch.WordTrace]
  refine ⟨105879977820046575478639961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70586651880031050319093307 105879977820046575478639961)
  ·
    refine ⟨79409983365034931608979971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105879977820046575478639961 79409983365034931608979971)
    ·
      refine ⟨119114975047552397413469957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79409983365034931608979971 119114975047552397413469957)
      ·
        refine ⟨22334057821416074515025617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119114975047552397413469957 22334057821416074515025617)
        ·
          refine ⟨16750543366062055886269213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22334057821416074515025617 16750543366062055886269213)
          ·
            refine ⟨6281453762273270957350955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16750543366062055886269213 6281453762273270957350955)
            ·
              refine ⟨9422180643409906436026433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281453762273270957350955 9422180643409906436026433)
              ·
                refine ⟨7066635482557429827019825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9422180643409906436026433 7066635482557429827019825)
                ·
                  refine ⟨5299976611918072370264869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7066635482557429827019825 5299976611918072370264869)
                  ·
                    refine ⟨993745614734638569424663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5299976611918072370264869 993745614734638569424663)
                    ·
                      rfl

theorem cell22_2902969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_2902969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902969 prefixEnd_2902969 := by exact prefixLift 2902969
  have htrace : WordTrace (prefixWord ++ tailWord_2902969) baseStart_2902969 baseEnd_2902969 := by
    simpa [prefixWord, tailWord_2902969, baseEnd_2902969] using wordTrace_append hprefix tailTrace_2902969
  have hstable : (prefixWord ++ tailWord_2902969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902969).length < 2 ^ (prefixWord ++ tailWord_2902969).sum := by decide
  have hdescent : baseEnd_2902969 < baseStart_2902969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902973 : List Nat := [1, 4, 1, 2, 4, 1, 3, 2, 4]
def baseStart_2902973 : Nat := 118140960795 + 2902973 * 2 ^ 59
def prefixEnd_2902973 : Nat := 4983230072969 + 3 ^ 40 * 2902973 * 2
def baseEnd_2902973 : Nat := 331248994672127964108217

theorem tailTrace_2902973 : CollatzResearch.WordTrace tailWord_2902973 prefixEnd_2902973 331248994672127964108217 := by
  unfold tailWord_2902973
  simp only [CollatzResearch.WordTrace]
  refine ⟨105880123712032084161785573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70586749141354722774523715 105880123712032084161785573)
  ·
    refine ⟨19852523196006015780334795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105880123712032084161785573 19852523196006015780334795)
    ·
      refine ⟨29778784794009023670502193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19852523196006015780334795 29778784794009023670502193)
      ·
        refine ⟨22334088595506767752876645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29778784794009023670502193 22334088595506767752876645)
        ·
          refine ⟨4187641611657518953664371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22334088595506767752876645 4187641611657518953664371)
          ·
            refine ⟨6281462417486278430496557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4187641611657518953664371 6281462417486278430496557)
            ·
              refine ⟨2355548406557354411436209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6281462417486278430496557 2355548406557354411436209)
              ·
                refine ⟨1766661304918015808577157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2355548406557354411436209 1766661304918015808577157)
                ·
                  refine ⟨331248994672127964108217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1766661304918015808577157 331248994672127964108217)
                  ·
                    rfl

theorem cell22_2902973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_2902973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902973 prefixEnd_2902973 := by exact prefixLift 2902973
  have htrace : WordTrace (prefixWord ++ tailWord_2902973) baseStart_2902973 baseEnd_2902973 := by
    simpa [prefixWord, tailWord_2902973, baseEnd_2902973] using wordTrace_append hprefix tailTrace_2902973
  have hstable : (prefixWord ++ tailWord_2902973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902973).length < 2 ^ (prefixWord ++ tailWord_2902973).sum := by decide
  have hdescent : baseEnd_2902973 < baseStart_2902973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902984 : List Nat := [2, 1, 3, 1, 5, 1, 2, 7]
def baseStart_2902984 : Nat := 118140960795 + 2902984 * 2 ^ 59
def prefixEnd_2902984 : Nat := 4983230072969 + 3 ^ 40 * 2902984 * 2
def baseEnd_2902984 : Nat := 110416749949020392255513

theorem tailTrace_2902984 : CollatzResearch.WordTrace tailWord_2902984 prefixEnd_2902984 110416749949020392255513 := by
  unfold tailWord_2902984
  simp only [CollatzResearch.WordTrace]
  refine ⟨52940262457496116520218003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70587016609994822026957337 52940262457496116520218003)
  ·
    refine ⟨79410393686244174780327005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52940262457496116520218003 79410393686244174780327005)
    ·
      refine ⟨29778897632341565542622627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79410393686244174780327005 29778897632341565542622627)
      ·
        refine ⟨44668346448512348313933941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29778897632341565542622627 44668346448512348313933941)
        ·
          refine ⟨4187657479548032654431307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44668346448512348313933941 4187657479548032654431307)
          ·
            refine ⟨6281486219322048981646961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4187657479548032654431307 6281486219322048981646961)
            ·
              refine ⟨4711114664491536736235221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6281486219322048981646961 4711114664491536736235221)
              ·
                refine ⟨110416749949020392255513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4711114664491536736235221 110416749949020392255513)
                ·
                  rfl

theorem cell22_2902984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 7].length) (baseStart_2902984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2902984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2902984 prefixEnd_2902984 := by exact prefixLift 2902984
  have htrace : WordTrace (prefixWord ++ tailWord_2902984) baseStart_2902984 baseEnd_2902984 := by
    simpa [prefixWord, tailWord_2902984, baseEnd_2902984] using wordTrace_append hprefix tailTrace_2902984
  have hstable : (prefixWord ++ tailWord_2902984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902984).length < 2 ^ (prefixWord ++ tailWord_2902984).sum := by decide
  have hdescent : baseEnd_2902984 < baseStart_2902984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903012 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 7]
def baseStart_2903012 : Nat := 118140960795 + 2903012 * 2 ^ 59
def prefixEnd_2903012 : Nat := 4983230072969 + 3 ^ 40 * 2903012 * 2
def baseEnd_2903012 : Nat := 331253444837800263533177

theorem tailTrace_2903012 : CollatzResearch.WordTrace tailWord_2903012 prefixEnd_2903012 331253444837800263533177 := by
  unfold tailWord_2903012
  simp only [CollatzResearch.WordTrace]
  refine ⟨52940773079445396911227645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70587697439260529214970193 52940773079445396911227645)
  ·
    refine ⟨19852789904792023841710367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52940773079445396911227645 19852789904792023841710367)
    ·
      refine ⟨29779184857188035762565551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19852789904792023841710367 29779184857188035762565551)
      ·
        refine ⟨44668777285782053643848327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29779184857188035762565551 44668777285782053643848327)
        ·
          refine ⟨67003165928673080465772491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44668777285782053643848327 67003165928673080465772491)
          ·
            refine ⟨100504748893009620698658737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67003165928673080465772491 100504748893009620698658737)
            ·
              refine ⟨75378561669757215523994053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100504748893009620698658737 75378561669757215523994053)
              ·
                refine ⟨14133480313079477910748885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75378561669757215523994053 14133480313079477910748885)
                ·
                  refine ⟨331253444837800263533177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14133480313079477910748885 331253444837800263533177)
                  ·
                    rfl

theorem cell22_2903012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_2903012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903012 prefixEnd_2903012 := by exact prefixLift 2903012
  have htrace : WordTrace (prefixWord ++ tailWord_2903012) baseStart_2903012 baseEnd_2903012 := by
    simpa [prefixWord, tailWord_2903012, baseEnd_2903012] using wordTrace_append hprefix tailTrace_2903012
  have hstable : (prefixWord ++ tailWord_2903012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903012).length < 2 ^ (prefixWord ++ tailWord_2903012).sum := by decide
  have hdescent : baseEnd_2903012 < baseStart_2903012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903059 : List Nat := [1, 1, 1, 2, 1, 4, 1, 6, 1, 4]
def baseStart_2903059 : Nat := 118140960795 + 2903059 * 2 ^ 59
def prefixEnd_2903059 : Nat := 4983230072969 + 3 ^ 40 * 2903059 * 2
def baseEnd_2903059 : Nat := 993776423573908334674387

theorem tailTrace_2903059 : CollatzResearch.WordTrace tailWord_2903059 prefixEnd_2903059 993776423573908334674387 := by
  unfold tailWord_2903059
  simp only [CollatzResearch.WordTrace]
  refine ⟨105883260389720520849416231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70588840259813680566277487 105883260389720520849416231)
  ·
    refine ⟨158824890584580781274124347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105883260389720520849416231 158824890584580781274124347)
    ·
      refine ⟨238237335876871171911186521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158824890584580781274124347 238237335876871171911186521)
      ·
        refine ⟨178678001907653378933389891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238237335876871171911186521 178678001907653378933389891)
        ·
          refine ⟨268017002861480068400084837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178678001907653378933389891 268017002861480068400084837)
          ·
            refine ⟨50253188036527512825015907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268017002861480068400084837 50253188036527512825015907)
            ·
              refine ⟨75379782054791269237523861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50253188036527512825015907 75379782054791269237523861)
              ·
                refine ⟨3533427283818340745508931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75379782054791269237523861 3533427283818340745508931)
                ·
                  refine ⟨5300140925727511118263397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533427283818340745508931 5300140925727511118263397)
                  ·
                    refine ⟨993776423573908334674387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5300140925727511118263397 993776423573908334674387)
                    ·
                      rfl

theorem cell22_2903059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 4].length) (baseStart_2903059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903059 prefixEnd_2903059 := by exact prefixLift 2903059
  have htrace : WordTrace (prefixWord ++ tailWord_2903059) baseStart_2903059 baseEnd_2903059 := by
    simpa [prefixWord, tailWord_2903059, baseEnd_2903059] using wordTrace_append hprefix tailTrace_2903059
  have hstable : (prefixWord ++ tailWord_2903059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903059).length < 2 ^ (prefixWord ++ tailWord_2903059).sum := by decide
  have hdescent : baseEnd_2903059 < baseStart_2903059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903110 : List Nat := [6, 1, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_2903110 : Nat := 118140960795 + 2903110 * 2 ^ 59
def prefixEnd_2903110 : Nat := 4983230072969 + 3 ^ 40 * 2903110 * 2
def baseEnd_2903110 : Nat := 993793881916161201649231

theorem tailTrace_2903110 : CollatzResearch.WordTrace tailWord_2903110 prefixEnd_2903110 993793881916161201649231 := by
  unfold tailWord_2903110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3308910016016742392485087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70590080341690504373015189 3308910016016742392485087)
  ·
    refine ⟨4963365024025113588727631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3308910016016742392485087 4963365024025113588727631)
    ·
      refine ⟨7445047536037670383091447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4963365024025113588727631 7445047536037670383091447)
      ·
        refine ⟨11167571304056505574637171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7445047536037670383091447 11167571304056505574637171)
        ·
          refine ⟨16751356956084758361955757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11167571304056505574637171 16751356956084758361955757)
          ·
            refine ⟨6281758858531784385733409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16751356956084758361955757 6281758858531784385733409)
            ·
              refine ⟨4711319143898838289300057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6281758858531784385733409 4711319143898838289300057)
              ·
                refine ⟨3533489357924128716975043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4711319143898838289300057 3533489357924128716975043)
                ·
                  refine ⟨5300234036886193075462565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533489357924128716975043 5300234036886193075462565)
                  ·
                    refine ⟨993793881916161201649231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5300234036886193075462565 993793881916161201649231)
                    ·
                      rfl

theorem cell22_2903110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_2903110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903110 prefixEnd_2903110 := by exact prefixLift 2903110
  have htrace : WordTrace (prefixWord ++ tailWord_2903110) baseStart_2903110 baseEnd_2903110 := by
    simpa [prefixWord, tailWord_2903110, baseEnd_2903110] using wordTrace_append hprefix tailTrace_2903110
  have hstable : (prefixWord ++ tailWord_2903110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903110).length < 2 ^ (prefixWord ++ tailWord_2903110).sum := by decide
  have hdescent : baseEnd_2903110 < baseStart_2903110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903138 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2903138 : Nat := 118140960795 + 2903138 * 2 ^ 59
def prefixEnd_2903138 : Nat := 4983230072969 + 3 ^ 40 * 2903138 * 2
def baseEnd_2903138 : Nat := 993803466888378461949145

theorem tailTrace_2903138 : CollatzResearch.WordTrace tailWord_2903138 prefixEnd_2903138 993803466888378461949145 := by
  unfold tailWord_2903138
  simp only [CollatzResearch.WordTrace]
  refine ⟨26471535439108579335385517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70590761170956211561028045 26471535439108579335385517)
  ·
    refine ⟨9926825789665717250769569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26471535439108579335385517 9926825789665717250769569)
    ·
      refine ⟨7445119342249287938077177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9926825789665717250769569 7445119342249287938077177)
      ·
        refine ⟨5583839506686965953557883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7445119342249287938077177 5583839506686965953557883)
        ·
          refine ⟨8375759260030448930336825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5583839506686965953557883 8375759260030448930336825)
          ·
            refine ⟨6281819445022836697752619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8375759260030448930336825 6281819445022836697752619)
            ·
              refine ⟨9422729167534255046628929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281819445022836697752619 9422729167534255046628929)
              ·
                refine ⟨7067046875650691284971697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9422729167534255046628929 7067046875650691284971697)
                ·
                  refine ⟨5300285156738018463728773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7067046875650691284971697 5300285156738018463728773)
                  ·
                    refine ⟨993803466888378461949145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5300285156738018463728773 993803466888378461949145)
                    ·
                      rfl

theorem cell22_2903138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2903138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903138 prefixEnd_2903138 := by exact prefixLift 2903138
  have htrace : WordTrace (prefixWord ++ tailWord_2903138) baseStart_2903138 baseEnd_2903138 := by
    simpa [prefixWord, tailWord_2903138, baseEnd_2903138] using wordTrace_append hprefix tailTrace_2903138
  have hstable : (prefixWord ++ tailWord_2903138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903138).length < 2 ^ (prefixWord ++ tailWord_2903138).sum := by decide
  have hdescent : baseEnd_2903138 < baseStart_2903138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903198 : List Nat := [4, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_2903198 : Nat := 118140960795 + 2903198 * 2 ^ 59
def prefixEnd_2903198 : Nat := 4983230072969 + 3 ^ 40 * 2903198 * 2
def baseEnd_2903198 : Nat := 331274668704852768482987

theorem tailTrace_2903198 : CollatzResearch.WordTrace tailWord_2903198 prefixEnd_2903198 331274668704852768482987 := by
  unfold tailWord_2903198
  simp only [CollatzResearch.WordTrace]
  refine ⟨13236041267027118448590781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70592220090811298392484165 13236041267027118448590781)
  ·
    refine ⟨4963515475135169418221543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13236041267027118448590781 4963515475135169418221543)
    ·
      refine ⟨7445273212702754127332315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4963515475135169418221543 7445273212702754127332315)
      ·
        refine ⟨11167909819054131190998473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7445273212702754127332315 11167909819054131190998473)
        ·
          refine ⟨8375932364290598393248855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11167909819054131190998473 8375932364290598393248855)
          ·
            refine ⟨12563898546435897589873283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8375932364290598393248855 12563898546435897589873283)
            ·
              refine ⟨18845847819653846384809925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12563898546435897589873283 18845847819653846384809925)
              ·
                refine ⟨3533596466185096197151861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18845847819653846384809925 3533596466185096197151861)
                ·
                  refine ⟨331274668704852768482987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3533596466185096197151861 331274668704852768482987)
                  ·
                    rfl

theorem cell22_2903198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_2903198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903198 prefixEnd_2903198 := by exact prefixLift 2903198
  have htrace : WordTrace (prefixWord ++ tailWord_2903198) baseStart_2903198 baseEnd_2903198 := by
    simpa [prefixWord, tailWord_2903198, baseEnd_2903198] using wordTrace_append hprefix tailTrace_2903198
  have hstable : (prefixWord ++ tailWord_2903198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903198).length < 2 ^ (prefixWord ++ tailWord_2903198).sum := by decide
  have hdescent : baseEnd_2903198 < baseStart_2903198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903202 : List Nat := [3, 3, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_2903202 : Nat := 118140960795 + 2903202 * 2 ^ 59
def prefixEnd_2903202 : Nat := 4983230072969 + 3 ^ 40 * 2903202 * 2
def baseEnd_2903202 : Nat := 993825375396303628348949

theorem tailTrace_2903202 : CollatzResearch.WordTrace tailWord_2903202 prefixEnd_2903202 993825375396303628348949 := by
  unfold tailWord_2903202
  simp only [CollatzResearch.WordTrace]
  refine ⟨26472119007050614067967965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70592317352134970847914573 26472119007050614067967965)
  ·
    refine ⟨9927044627643980275487987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26472119007050614067967965 9927044627643980275487987)
    ·
      refine ⟨14890566941465970413231981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9927044627643980275487987 14890566941465970413231981)
      ·
        refine ⟨5583962603049738904961993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14890566941465970413231981 5583962603049738904961993)
        ·
          refine ⟨4187971952287304178721495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5583962603049738904961993 4187971952287304178721495)
          ·
            refine ⟨6281957928430956268082243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4187971952287304178721495 6281957928430956268082243)
            ·
              refine ⟨9422936892646434402123365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281957928430956268082243 9422936892646434402123365)
              ·
                refine ⟨1766800667371206450398131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9422936892646434402123365 1766800667371206450398131)
                ·
                  refine ⟨2650201001056809675597197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1766800667371206450398131 2650201001056809675597197)
                  ·
                    refine ⟨993825375396303628348949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2650201001056809675597197 993825375396303628348949)
                    ·
                      rfl

theorem cell22_2903202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_2903202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903202 prefixEnd_2903202 := by exact prefixLift 2903202
  have htrace : WordTrace (prefixWord ++ tailWord_2903202) baseStart_2903202 baseEnd_2903202 := by
    simpa [prefixWord, tailWord_2903202, baseEnd_2903202] using wordTrace_append hprefix tailTrace_2903202
  have hstable : (prefixWord ++ tailWord_2903202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903202).length < 2 ^ (prefixWord ++ tailWord_2903202).sum := by decide
  have hdescent : baseEnd_2903202 < baseStart_2903202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903213 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_2903213 : Nat := 118140960795 + 2903213 * 2 ^ 59
def prefixEnd_2903213 : Nat := 4983230072969 + 3 ^ 40 * 2903213 * 2
def baseEnd_2903213 : Nat := 993829140921103266323915

theorem tailTrace_2903213 : CollatzResearch.WordTrace tailWord_2903213 prefixEnd_2903213 993829140921103266323915 := by
  unfold tailWord_2903213
  simp only [CollatzResearch.WordTrace]
  refine ⟨105888877231162605150522293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70592584820775070100348195 105888877231162605150522293)
  ·
    refine ⟨9927082240421494232861465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105888877231162605150522293 9927082240421494232861465)
    ·
      refine ⟨7445311680316120674646099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9927082240421494232861465 7445311680316120674646099)
      ·
        refine ⟨11167967520474181011969149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7445311680316120674646099 11167967520474181011969149)
        ·
          refine ⟨4187987820177817879488431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11167967520474181011969149 4187987820177817879488431)
          ·
            refine ⟨6281981730266726819232647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4187987820177817879488431 6281981730266726819232647)
            ·
              refine ⟨9422972595400090228848971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281981730266726819232647 9422972595400090228848971)
              ·
                refine ⟨14134458893100135343273457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9422972595400090228848971 14134458893100135343273457)
                ·
                  refine ⟨10600844169825101507455093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14134458893100135343273457 10600844169825101507455093)
                  ·
                    refine ⟨993829140921103266323915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10600844169825101507455093 993829140921103266323915)
                    ·
                      rfl

theorem cell22_2903213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_2903213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903213 prefixEnd_2903213 := by exact prefixLift 2903213
  have htrace : WordTrace (prefixWord ++ tailWord_2903213) baseStart_2903213 baseEnd_2903213 := by
    simpa [prefixWord, tailWord_2903213, baseEnd_2903213] using wordTrace_append hprefix tailTrace_2903213
  have hstable : (prefixWord ++ tailWord_2903213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903213).length < 2 ^ (prefixWord ++ tailWord_2903213).sum := by decide
  have hdescent : baseEnd_2903213 < baseStart_2903213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903275 : List Nat := [1, 1, 1, 1, 2, 7, 3, 1, 2, 3]
def baseStart_2903275 : Nat := 118140960795 + 2903275 * 2 ^ 59
def prefixEnd_2903275 : Nat := 4983230072969 + 3 ^ 40 * 2903275 * 2
def baseEnd_2903275 : Nat := 993850364788155771273725

theorem tailTrace_2903275 : CollatzResearch.WordTrace tailWord_2903275 prefixEnd_2903275 993850364788155771273725 := by
  unfold tailWord_2903275
  simp only [CollatzResearch.WordTrace]
  refine ⟨105891138556937989739279279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70594092371291993159519519 105891138556937989739279279)
  ·
    refine ⟨158836707835406984608918919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105891138556937989739279279 158836707835406984608918919)
    ·
      refine ⟨238255061753110476913378379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158836707835406984608918919 238255061753110476913378379)
      ·
        refine ⟨357382592629665715370067569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238255061753110476913378379 357382592629665715370067569)
        ·
          refine ⟨268036944472249286527550677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357382592629665715370067569 268036944472249286527550677)
          ·
            refine ⟨6282115886068342652989469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 268036944472249286527550677 6282115886068342652989469)
            ·
              refine ⟨2355793457275628494871051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6282115886068342652989469 2355793457275628494871051)
              ·
                refine ⟨3533690185913442742306577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2355793457275628494871051 3533690185913442742306577)
                ·
                  refine ⟨2650267639435082056729933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3533690185913442742306577 2650267639435082056729933)
                  ·
                    refine ⟨993850364788155771273725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2650267639435082056729933 993850364788155771273725)
                    ·
                      rfl

theorem cell22_2903275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 2, 3].length) (baseStart_2903275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903275 prefixEnd_2903275 := by exact prefixLift 2903275
  have htrace : WordTrace (prefixWord ++ tailWord_2903275) baseStart_2903275 baseEnd_2903275 := by
    simpa [prefixWord, tailWord_2903275, baseEnd_2903275] using wordTrace_append hprefix tailTrace_2903275
  have hstable : (prefixWord ++ tailWord_2903275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903275).length < 2 ^ (prefixWord ++ tailWord_2903275).sum := by decide
  have hdescent : baseEnd_2903275 < baseStart_2903275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903286 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_2903286 : Nat := 118140960795 + 2903286 * 2 ^ 59
def prefixEnd_2903286 : Nat := 4983230072969 + 3 ^ 40 * 2903286 * 2
def baseEnd_2903286 : Nat := 993854130312955409248691

theorem tailTrace_2903286 : CollatzResearch.WordTrace tailWord_2903286 prefixEnd_2903286 993854130312955409248691 := by
  unfold tailWord_2903286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6618221234993633663620607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70594359839932092411953141 6618221234993633663620607)
  ·
    refine ⟨9927331852490450495430911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6618221234993633663620607 9927331852490450495430911)
    ·
      refine ⟨14890997778735675743146367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9927331852490450495430911 14890997778735675743146367)
      ·
        refine ⟨22336496668103513614719551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14890997778735675743146367 22336496668103513614719551)
        ·
          refine ⟨33504745002155270422079327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22336496668103513614719551 33504745002155270422079327)
          ·
            refine ⟨50257117503232905633118991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33504745002155270422079327 50257117503232905633118991)
            ·
              refine ⟨75385676254849358449678487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50257117503232905633118991 75385676254849358449678487)
              ·
                refine ⟨113078514382274037674517731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75385676254849358449678487 113078514382274037674517731)
                ·
                  refine ⟨169617771573411056511776597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113078514382274037674517731 169617771573411056511776597)
                  ·
                    refine ⟨993854130312955409248691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 169617771573411056511776597 993854130312955409248691)
                    ·
                      rfl

theorem cell22_2903286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_2903286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903286 prefixEnd_2903286 := by exact prefixLift 2903286
  have htrace : WordTrace (prefixWord ++ tailWord_2903286) baseStart_2903286 baseEnd_2903286 := by
    simpa [prefixWord, tailWord_2903286, baseEnd_2903286] using wordTrace_append hprefix tailTrace_2903286
  have hstable : (prefixWord ++ tailWord_2903286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903286).length < 2 ^ (prefixWord ++ tailWord_2903286).sum := by decide
  have hdescent : baseEnd_2903286 < baseStart_2903286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903320 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 3, 3]
def baseStart_2903320 : Nat := 118140960795 + 2903320 * 2 ^ 59
def prefixEnd_2903320 : Nat := 4983230072969 + 3 ^ 40 * 2903320 * 2
def baseEnd_2903320 : Nat := 993865769207790653898587

theorem tailTrace_2903320 : CollatzResearch.WordTrace tailWord_2903320 prefixEnd_2903320 993865769207790653898587 := by
  unfold tailWord_2903320
  simp only [CollatzResearch.WordTrace]
  refine ⟨52946389920887481212333707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70595186561183308283111609 52946389920887481212333707)
  ·
    refine ⟨79419584881331221818500561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52946389920887481212333707 79419584881331221818500561)
    ·
      refine ⟨59564688660998416363875421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79419584881331221818500561 59564688660998416363875421)
      ·
        refine ⟨22336758247874406136453283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59564688660998416363875421 22336758247874406136453283)
        ·
          refine ⟨33505137371811609204679925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22336758247874406136453283 33505137371811609204679925)
          ·
            refine ⟨3141106628607338362938743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33505137371811609204679925 3141106628607338362938743)
            ·
              refine ⟨4711659942911007544408115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141106628607338362938743 4711659942911007544408115)
              ·
                refine ⟨7067489914366511316612173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711659942911007544408115 7067489914366511316612173)
                ·
                  refine ⟨2650308717887441743729565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7067489914366511316612173 2650308717887441743729565)
                  ·
                    refine ⟨993865769207790653898587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2650308717887441743729565 993865769207790653898587)
                    ·
                      rfl

theorem cell22_2903320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_2903320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903320 prefixEnd_2903320 := by exact prefixLift 2903320
  have htrace : WordTrace (prefixWord ++ tailWord_2903320) baseStart_2903320 baseEnd_2903320 := by
    simpa [prefixWord, tailWord_2903320, baseEnd_2903320] using wordTrace_append hprefix tailTrace_2903320
  have hstable : (prefixWord ++ tailWord_2903320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903320).length < 2 ^ (prefixWord ++ tailWord_2903320).sum := by decide
  have hdescent : baseEnd_2903320 < baseStart_2903320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903326 : List Nat := [4, 3, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2903326 : Nat := 118140960795 + 2903326 * 2 ^ 59
def prefixEnd_2903326 : Nat := 4983230072969 + 3 ^ 40 * 2903326 * 2
def baseEnd_2903326 : Nat := 993867823130408638248569

theorem tailTrace_2903326 : CollatzResearch.WordTrace tailWord_2903326 prefixEnd_2903326 993867823130408638248569 := by
  unfold tailWord_2903326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13236624834969153181173229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70595332453168816966257221 13236624834969153181173229)
  ·
    refine ⟨4963734313113432442939961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13236624834969153181173229 4963734313113432442939961)
    ·
      refine ⟨3722800734835074332204971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4963734313113432442939961 3722800734835074332204971)
      ·
        refine ⟨5584201102252611498307457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3722800734835074332204971 5584201102252611498307457)
        ·
          refine ⟨4188150826689458623730593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5584201102252611498307457 4188150826689458623730593)
          ·
            refine ⟨3141113120017093967797945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4188150826689458623730593 3141113120017093967797945)
            ·
              refine ⟨2355834840012820475848459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3141113120017093967797945 2355834840012820475848459)
              ·
                refine ⟨3533752260019230713772689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2355834840012820475848459 3533752260019230713772689)
                ·
                  refine ⟨2650314195014423035329517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3533752260019230713772689 2650314195014423035329517)
                  ·
                    refine ⟨993867823130408638248569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2650314195014423035329517 993867823130408638248569)
                    ·
                      rfl

theorem cell22_2903326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2903326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903326 prefixEnd_2903326 := by exact prefixLift 2903326
  have htrace : WordTrace (prefixWord ++ tailWord_2903326) baseStart_2903326 baseEnd_2903326 := by
    simpa [prefixWord, tailWord_2903326, baseEnd_2903326] using wordTrace_append hprefix tailTrace_2903326
  have hstable : (prefixWord ++ tailWord_2903326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903326).length < 2 ^ (prefixWord ++ tailWord_2903326).sum := by decide
  have hdescent : baseEnd_2903326 < baseStart_2903326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903333 : List Nat := [1, 3, 1, 2, 4, 2, 1, 3, 5]
def baseStart_2903333 : Nat := 118140960795 + 2903333 * 2 ^ 59
def prefixEnd_2903333 : Nat := 4983230072969 + 3 ^ 40 * 2903333 * 2
def baseEnd_2903333 : Nat := 331290073124487651107849

theorem tailTrace_2903333 : CollatzResearch.WordTrace tailWord_2903333 prefixEnd_2903333 331290073124487651107849 := by
  unfold tailWord_2903333
  simp only [CollatzResearch.WordTrace]
  refine ⟨105893253990727865644890653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70595502660485243763260435 105893253990727865644890653)
  ·
    refine ⟨39709970246522949616833995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105893253990727865644890653 39709970246522949616833995)
    ·
      refine ⟨59564955369784424425250993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39709970246522949616833995 59564955369784424425250993)
      ·
        refine ⟨44673716527338318318938245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59564955369784424425250993 44673716527338318318938245)
        ·
          refine ⟨8376321848875934684800921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44673716527338318318938245 8376321848875934684800921)
          ·
            refine ⟨6282241386656951013600691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8376321848875934684800921 6282241386656951013600691)
            ·
              refine ⟨9423362079985426520401037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6282241386656951013600691 9423362079985426520401037)
              ·
                refine ⟨3533760779994534945150389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9423362079985426520401037 3533760779994534945150389)
                ·
                  refine ⟨331290073124487651107849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3533760779994534945150389 331290073124487651107849)
                  ·
                    rfl

theorem cell22_2903333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_2903333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903333 prefixEnd_2903333 := by exact prefixLift 2903333
  have htrace : WordTrace (prefixWord ++ tailWord_2903333) baseStart_2903333 baseEnd_2903333 := by
    simpa [prefixWord, tailWord_2903333, baseEnd_2903333] using wordTrace_append hprefix tailTrace_2903333
  have hstable : (prefixWord ++ tailWord_2903333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903333).length < 2 ^ (prefixWord ++ tailWord_2903333).sum := by decide
  have hdescent : baseEnd_2903333 < baseStart_2903333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903376 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 3, 5]
def baseStart_2903376 : Nat := 118140960795 + 2903376 * 2 ^ 59
def prefixEnd_2903376 : Nat := 4983230072969 + 3 ^ 40 * 2903376 * 2
def baseEnd_2903376 : Nat := 993884939152225174498415

theorem tailTrace_2903376 : CollatzResearch.WordTrace tailWord_2903376 prefixEnd_2903376 993884939152225174498415 := by
  unfold tailWord_2903376
  simp only [CollatzResearch.WordTrace]
  refine ⟨52947411164786041994352991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70596548219714722659137321 52947411164786041994352991)
  ·
    refine ⟨79421116747179062991529487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52947411164786041994352991 79421116747179062991529487)
    ·
      refine ⟨119131675120768594487294231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79421116747179062991529487 119131675120768594487294231)
      ·
        refine ⟨178697512681152891730941347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119131675120768594487294231 178697512681152891730941347)
        ·
          refine ⟨268046269021729337596412021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178697512681152891730941347 268046269021729337596412021)
          ·
            refine ⟨25129337720787125399663627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 268046269021729337596412021 25129337720787125399663627)
            ·
              refine ⟨37694006581180688099495441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25129337720787125399663627 37694006581180688099495441)
              ·
                refine ⟨28270504935885516074621581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37694006581180688099495441 28270504935885516074621581)
                ·
                  refine ⟨10601439350957068527983093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28270504935885516074621581 10601439350957068527983093)
                  ·
                    refine ⟨993884939152225174498415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10601439350957068527983093 993884939152225174498415)
                    ·
                      rfl

theorem cell22_2903376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_2903376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903376 prefixEnd_2903376 := by exact prefixLift 2903376
  have htrace : WordTrace (prefixWord ++ tailWord_2903376) baseStart_2903376 baseEnd_2903376 := by
    simpa [prefixWord, tailWord_2903376, baseEnd_2903376] using wordTrace_append hprefix tailTrace_2903376
  have hstable : (prefixWord ++ tailWord_2903376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903376).length < 2 ^ (prefixWord ++ tailWord_2903376).sum := by decide
  have hdescent : baseEnd_2903376 < baseStart_2903376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903391 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 1, 6]
def baseStart_2903391 : Nat := 118140960795 + 2903391 * 2 ^ 59
def prefixEnd_2903391 : Nat := 4983230072969 + 3 ^ 40 * 2903391 * 2
def baseEnd_2903391 : Nat := 993890073958770135373369

theorem tailTrace_2903391 : CollatzResearch.WordTrace tailWord_2903391 prefixEnd_2903391 993890073958770135373369 := by
  unfold tailWord_2903391
  simp only [CollatzResearch.WordTrace]
  refine ⟨105895369424517741550502027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70596912949678494367001351 105895369424517741550502027)
  ·
    refine ⟨158843054136776612325753041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105895369424517741550502027 158843054136776612325753041)
    ·
      refine ⟨119132290602582459244314781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158843054136776612325753041 119132290602582459244314781)
      ·
        refine ⟨44674608975968422216618043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119132290602582459244314781 44674608975968422216618043)
        ·
          refine ⟨67011913463952633324927065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44674608975968422216618043 67011913463952633324927065)
          ·
            refine ⟨50258935097964474993695299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67011913463952633324927065 50258935097964474993695299)
            ·
              refine ⟨75388402646946712490542949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50258935097964474993695299 75388402646946712490542949)
              ·
                refine ⟨14135325496302508591976803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75388402646946712490542949 14135325496302508591976803)
                ·
                  refine ⟨21202988244453762887965205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14135325496302508591976803 21202988244453762887965205)
                  ·
                    refine ⟨993890073958770135373369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21202988244453762887965205 993890073958770135373369)
                    ·
                      rfl

theorem cell22_2903391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_2903391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903391 prefixEnd_2903391 := by exact prefixLift 2903391
  have htrace : WordTrace (prefixWord ++ tailWord_2903391) baseStart_2903391 baseEnd_2903391 := by
    simpa [prefixWord, tailWord_2903391, baseEnd_2903391] using wordTrace_append hprefix tailTrace_2903391
  have hstable : (prefixWord ++ tailWord_2903391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903391).length < 2 ^ (prefixWord ++ tailWord_2903391).sum := by decide
  have hdescent : baseEnd_2903391 < baseStart_2903391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903427 : List Nat := [1, 1, 1, 3, 5, 3, 1, 2, 2, 3]
def baseStart_2903427 : Nat := 118140960795 + 2903427 * 2 ^ 59
def prefixEnd_2903427 : Nat := 4983230072969 + 3 ^ 40 * 2903427 * 2
def baseEnd_2903427 : Nat := 993902397494478041473259

theorem tailTrace_2903427 : CollatzResearch.WordTrace tailWord_2903427 prefixEnd_2903427 993902397494478041473259 := by
  unfold tailWord_2903427
  simp only [CollatzResearch.WordTrace]
  refine ⟨105896682452387319698812535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70597788301591546465875023 105896682452387319698812535)
  ·
    refine ⟨158845023678580979548218803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105896682452387319698812535 158845023678580979548218803)
    ·
      refine ⟨238267535517871469322328205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158845023678580979548218803 238267535517871469322328205)
      ·
        refine ⟨89350325819201800995873077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238267535517871469322328205 89350325819201800995873077)
        ·
          refine ⟨8376593045550168843363101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89350325819201800995873077 8376593045550168843363101)
          ·
            refine ⟨3141222392081313316261163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8376593045550168843363101 3141222392081313316261163)
            ·
              refine ⟨4711833588121969974391745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141222392081313316261163 4711833588121969974391745)
              ·
                refine ⟨3533875191091477480793809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4711833588121969974391745 3533875191091477480793809)
                ·
                  refine ⟨2650406393318608110595357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3533875191091477480793809 2650406393318608110595357)
                  ·
                    refine ⟨993902397494478041473259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2650406393318608110595357 993902397494478041473259)
                    ·
                      rfl

theorem cell22_2903427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 3].length) (baseStart_2903427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903427 prefixEnd_2903427 := by exact prefixLift 2903427
  have htrace : WordTrace (prefixWord ++ tailWord_2903427) baseStart_2903427 baseEnd_2903427 := by
    simpa [prefixWord, tailWord_2903427, baseEnd_2903427] using wordTrace_append hprefix tailTrace_2903427
  have hstable : (prefixWord ++ tailWord_2903427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903427).length < 2 ^ (prefixWord ++ tailWord_2903427).sum := by decide
  have hdescent : baseEnd_2903427 < baseStart_2903427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903444 : List Nat := [2, 4, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_2903444 : Nat := 118140960795 + 2903444 * 2 ^ 59
def prefixEnd_2903444 : Nat := 4983230072969 + 3 ^ 40 * 2903444 * 2
def baseEnd_2903444 : Nat := 993908216941895663798207

theorem tailTrace_2903444 : CollatzResearch.WordTrace tailWord_2903444 prefixEnd_2903444 993908216941895663798207 := by
  unfold tailWord_2903444
  simp only [CollatzResearch.WordTrace]
  refine ⟨52948651246662865801090693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70598201662217154401454257 52948651246662865801090693)
  ·
    refine ⟨9927872108749287337704505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52948651246662865801090693 9927872108749287337704505)
    ·
      refine ⟨7445904081561965503278379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9927872108749287337704505 7445904081561965503278379)
      ·
        refine ⟨11168856122342948254917569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7445904081561965503278379 11168856122342948254917569)
        ·
          refine ⟨8376642091757211191188177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11168856122342948254917569 8376642091757211191188177)
          ·
            refine ⟨6282481568817908393391133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8376642091757211191188177 6282481568817908393391133)
            ·
              refine ⟨2355930588306715647521675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6282481568817908393391133 2355930588306715647521675)
              ·
                refine ⟨3533895882460073471282513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2355930588306715647521675 3533895882460073471282513)
                ·
                  refine ⟨2650421911845055103461885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3533895882460073471282513 2650421911845055103461885)
                  ·
                    refine ⟨993908216941895663798207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2650421911845055103461885 993908216941895663798207)
                    ·
                      rfl

theorem cell22_2903444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_2903444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903444 prefixEnd_2903444 := by exact prefixLift 2903444
  have htrace : WordTrace (prefixWord ++ tailWord_2903444) baseStart_2903444 baseEnd_2903444 := by
    simpa [prefixWord, tailWord_2903444, baseEnd_2903444] using wordTrace_append hprefix tailTrace_2903444
  have hstable : (prefixWord ++ tailWord_2903444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903444).length < 2 ^ (prefixWord ++ tailWord_2903444).sum := by decide
  have hdescent : baseEnd_2903444 < baseStart_2903444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903455 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 3, 3]
def baseStart_2903455 : Nat := 118140960795 + 2903455 * 2 ^ 59
def prefixEnd_2903455 : Nat := 4983230072969 + 3 ^ 40 * 2903455 * 2
def baseEnd_2903455 : Nat := 993911982466695301773173

theorem tailTrace_2903455 : CollatzResearch.WordTrace tailWord_2903455 prefixEnd_2903455 993911982466695301773173 := by
  unfold tailWord_2903455
  simp only [CollatzResearch.WordTrace]
  refine ⟨105897703696285880480831819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70598469130857253653887879 105897703696285880480831819)
  ·
    refine ⟨158846555544428820721247729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105897703696285880480831819 158846555544428820721247729)
    ·
      refine ⟨119134916658321615540935797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158846555544428820721247729 119134916658321615540935797)
      ·
        refine ⟨11168898436717651456962731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119134916658321615540935797 11168898436717651456962731)
        ·
          refine ⟨16753347655076477185444097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11168898436717651456962731 16753347655076477185444097)
          ·
            refine ⟨12565010741307357889083073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16753347655076477185444097 12565010741307357889083073)
            ·
              refine ⟨9423758055980518416812305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12565010741307357889083073 9423758055980518416812305)
              ·
                refine ⟨7067818541985388812609229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9423758055980518416812305 7067818541985388812609229)
                ·
                  refine ⟨2650431953244520804728461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7067818541985388812609229 2650431953244520804728461)
                  ·
                    refine ⟨993911982466695301773173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2650431953244520804728461 993911982466695301773173)
                    ·
                      rfl

theorem cell22_2903455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 3].length) (baseStart_2903455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903455 prefixEnd_2903455 := by exact prefixLift 2903455
  have htrace : WordTrace (prefixWord ++ tailWord_2903455) baseStart_2903455 baseEnd_2903455 := by
    simpa [prefixWord, tailWord_2903455, baseEnd_2903455] using wordTrace_append hprefix tailTrace_2903455
  have hstable : (prefixWord ++ tailWord_2903455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903455).length < 2 ^ (prefixWord ++ tailWord_2903455).sum := by decide
  have hdescent : baseEnd_2903455 < baseStart_2903455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903543 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 4, 4]
def baseStart_2903543 : Nat := 118140960795 + 2903543 * 2 ^ 59
def prefixEnd_2903543 : Nat := 4983230072969 + 3 ^ 40 * 2903543 * 2
def baseEnd_2903543 : Nat := 993942106665092405572903

theorem tailTrace_2903543 : CollatzResearch.WordTrace tailWord_2903543 prefixEnd_2903543 993942106665092405572903 := by
  unfold tailWord_2903543
  simp only [CollatzResearch.WordTrace]
  refine ⟨105900913319967071510035283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70600608879978047673356855 105900913319967071510035283)
  ·
    refine ⟨158851369979950607265052925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105900913319967071510035283 158851369979950607265052925)
    ·
      refine ⟨59569263742481477724394847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158851369979950607265052925 59569263742481477724394847)
      ·
        refine ⟨89353895613722216586592271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59569263742481477724394847 89353895613722216586592271)
        ·
          refine ⟨134030843420583324879888407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89353895613722216586592271 134030843420583324879888407)
          ·
            refine ⟨201046265130874987319832611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134030843420583324879888407 201046265130874987319832611)
            ·
              refine ⟨301569397696312480979748917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201046265130874987319832611 301569397696312480979748917)
              ·
                refine ⟨28272131034029295091851461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 301569397696312480979748917 28272131034029295091851461)
                ·
                  refine ⟨5301024568880492829722149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28272131034029295091851461 5301024568880492829722149)
                  ·
                    refine ⟨993942106665092405572903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5301024568880492829722149 993942106665092405572903)
                    ·
                      rfl

theorem cell22_2903543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_2903543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903543 prefixEnd_2903543 := by exact prefixLift 2903543
  have htrace : WordTrace (prefixWord ++ tailWord_2903543) baseStart_2903543 baseEnd_2903543 := by
    simpa [prefixWord, tailWord_2903543, baseEnd_2903543] using wordTrace_append hprefix tailTrace_2903543
  have hstable : (prefixWord ++ tailWord_2903543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903543).length < 2 ^ (prefixWord ++ tailWord_2903543).sum := by decide
  have hdescent : baseEnd_2903543 < baseStart_2903543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903562 : List Nat := [3, 1, 2, 2, 2, 2, 2, 3, 2, 3]
def baseStart_2903562 : Nat := 118140960795 + 2903562 * 2 ^ 59
def prefixEnd_2903562 : Nat := 4983230072969 + 3 ^ 40 * 2903562 * 2
def baseEnd_2903562 : Nat := 993948610753382689347845

theorem tailTrace_2903562 : CollatzResearch.WordTrace tailWord_2903562 prefixEnd_2903562 993948610753382689347845 := by
  unfold tailWord_2903562
  simp only [CollatzResearch.WordTrace]
  refine ⟨26475401576724559438744235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70601070871265491836651293 26475401576724559438744235)
  ·
    refine ⟨39713102365086839158116353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26475401576724559438744235 39713102365086839158116353)
    ·
      refine ⟨29784826773815129368587265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39713102365086839158116353 29784826773815129368587265)
      ·
        refine ⟨22338620080361347026440449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29784826773815129368587265 22338620080361347026440449)
        ·
          refine ⟨16753965060271010269830337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22338620080361347026440449 16753965060271010269830337)
          ·
            refine ⟨12565473795203257702372753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16753965060271010269830337 12565473795203257702372753)
            ·
              refine ⟨9424105346402443276779565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12565473795203257702372753 9424105346402443276779565)
              ·
                refine ⟨3534039504900916228792337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9424105346402443276779565 3534039504900916228792337)
                ·
                  refine ⟨2650529628675687171594253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3534039504900916228792337 2650529628675687171594253)
                  ·
                    refine ⟨993948610753382689347845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2650529628675687171594253 993948610753382689347845)
                    ·
                      rfl

theorem cell22_2903562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_2903562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903562 prefixEnd_2903562 := by exact prefixLift 2903562
  have htrace : WordTrace (prefixWord ++ tailWord_2903562) baseStart_2903562 baseEnd_2903562 := by
    simpa [prefixWord, tailWord_2903562, baseEnd_2903562] using wordTrace_append hprefix tailTrace_2903562
  have hstable : (prefixWord ++ tailWord_2903562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903562).length < 2 ^ (prefixWord ++ tailWord_2903562).sum := by decide
  have hdescent : baseEnd_2903562 < baseStart_2903562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903607 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 3, 3]
def baseStart_2903607 : Nat := 118140960795 + 2903607 * 2 ^ 59
def prefixEnd_2903607 : Nat := 4983230072969 + 3 ^ 40 * 2903607 * 2
def baseEnd_2903607 : Nat := 993964015173017571972707

theorem tailTrace_2903607 : CollatzResearch.WordTrace tailWord_2903607 prefixEnd_2903607 993964015173017571972707 := by
  unfold tailWord_2903607
  simp only [CollatzResearch.WordTrace]
  refine ⟨105903247591735210440365075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70602165061156806960243383 105903247591735210440365075)
  ·
    refine ⟨158854871387602815660547613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105903247591735210440365075 158854871387602815660547613)
    ·
      refine ⟨59570576770351055872705355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158854871387602815660547613 59570576770351055872705355)
      ·
        refine ⟨89355865155526583809058033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59570576770351055872705355 89355865155526583809058033)
        ·
          refine ⟨67016898866644937856793525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89355865155526583809058033 67016898866644937856793525)
          ·
            refine ⟨6282834268747962924074393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67016898866644937856793525 6282834268747962924074393)
            ·
              refine ⟨4712125701560972193055795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6282834268747962924074393 4712125701560972193055795)
              ·
                refine ⟨7068188552341458289583693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4712125701560972193055795 7068188552341458289583693)
                ·
                  refine ⟨2650570707128046858593885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7068188552341458289583693 2650570707128046858593885)
                  ·
                    refine ⟨993964015173017571972707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2650570707128046858593885 993964015173017571972707)
                    ·
                      rfl

theorem cell22_2903607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_2903607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903607 prefixEnd_2903607 := by exact prefixLift 2903607
  have htrace : WordTrace (prefixWord ++ tailWord_2903607) baseStart_2903607 baseEnd_2903607 := by
    simpa [prefixWord, tailWord_2903607, baseEnd_2903607] using wordTrace_append hprefix tailTrace_2903607
  have hstable : (prefixWord ++ tailWord_2903607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903607).length < 2 ^ (prefixWord ++ tailWord_2903607).sum := by decide
  have hdescent : baseEnd_2903607 < baseStart_2903607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903680 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 1, 5]
def baseStart_2903680 : Nat := 118140960795 + 2903680 * 2 ^ 59
def prefixEnd_2903680 : Nat := 4983230072969 + 3 ^ 40 * 2903680 * 2
def baseEnd_2903680 : Nat := 993989004564869714897483

theorem tailTrace_2903680 : CollatzResearch.WordTrace tailWord_2903680 prefixEnd_2903680 993989004564869714897483 := by
  unfold tailWord_2903680
  simp only [CollatzResearch.WordTrace]
  refine ⟨52952955060235371953886247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70603940080313829271848329 52952955060235371953886247)
  ·
    refine ⟨79429432590353057930829371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52952955060235371953886247 79429432590353057930829371)
    ·
      refine ⟨119144148885529586896244057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79429432590353057930829371 119144148885529586896244057)
      ·
        refine ⟨89358111664147190172183043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119144148885529586896244057 89358111664147190172183043)
        ·
          refine ⟨134037167496220785258274565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89358111664147190172183043 134037167496220785258274565)
          ·
            refine ⟨25131968905541397235926481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134037167496220785258274565 25131968905541397235926481)
            ·
              refine ⟨18848976679156047926944861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25131968905541397235926481 18848976679156047926944861)
              ·
                refine ⟨7068366254683517972604323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18848976679156047926944861 7068366254683517972604323)
                ·
                  refine ⟨10602549382025276958906485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7068366254683517972604323 10602549382025276958906485)
                  ·
                    refine ⟨993989004564869714897483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10602549382025276958906485 993989004564869714897483)
                    ·
                      rfl

theorem cell22_2903680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_2903680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903680 prefixEnd_2903680 := by exact prefixLift 2903680
  have htrace : WordTrace (prefixWord ++ tailWord_2903680) baseStart_2903680 baseEnd_2903680 := by
    simpa [prefixWord, tailWord_2903680, baseEnd_2903680] using wordTrace_append hprefix tailTrace_2903680
  have hstable : (prefixWord ++ tailWord_2903680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903680).length < 2 ^ (prefixWord ++ tailWord_2903680).sum := by decide
  have hdescent : baseEnd_2903680 < baseStart_2903680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903712 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 2, 4]
def baseStart_2903712 : Nat := 118140960795 + 2903712 * 2 ^ 59
def prefixEnd_2903712 : Nat := 4983230072969 + 3 ^ 40 * 2903712 * 2
def baseEnd_2903712 : Nat := 993999958818832298097385

theorem tailTrace_2903712 : CollatzResearch.WordTrace tailWord_2903712 prefixEnd_2903712 993999958818832298097385 := by
  unfold tailWord_2903712
  simp only [CollatzResearch.WordTrace]
  refine ⟨52953538628177406686468695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70604718170903208915291593 52953538628177406686468695)
  ·
    refine ⟨79430307942266110029703043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52953538628177406686468695 79430307942266110029703043)
    ·
      refine ⟨119145461913399165044554565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79430307942266110029703043 119145461913399165044554565)
      ·
        refine ⟨22339774108762343445853981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119145461913399165044554565 22339774108762343445853981)
        ·
          refine ⟨8377415290785878792195243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22339774108762343445853981 8377415290785878792195243)
          ·
            refine ⟨12566122936178818188292865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8377415290785878792195243 12566122936178818188292865)
            ·
              refine ⟨9424592202134113641219649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12566122936178818188292865 9424592202134113641219649)
              ·
                refine ⟨7068444151600585230914737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9424592202134113641219649 7068444151600585230914737)
                ·
                  refine ⟨5301333113700438923186053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7068444151600585230914737 5301333113700438923186053)
                  ·
                    refine ⟨993999958818832298097385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5301333113700438923186053 993999958818832298097385)
                    ·
                      rfl

theorem cell22_2903712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_2903712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903712 prefixEnd_2903712 := by exact prefixLift 2903712
  have htrace : WordTrace (prefixWord ++ tailWord_2903712) baseStart_2903712 baseEnd_2903712 := by
    simpa [prefixWord, tailWord_2903712, baseEnd_2903712] using wordTrace_append hprefix tailTrace_2903712
  have hstable : (prefixWord ++ tailWord_2903712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903712).length < 2 ^ (prefixWord ++ tailWord_2903712).sum := by decide
  have hdescent : baseEnd_2903712 < baseStart_2903712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903716 : List Nat := [2, 3, 1, 2, 2, 4, 2, 2, 4]
def baseStart_2903716 : Nat := 118140960795 + 2903716 * 2 ^ 59
def prefixEnd_2903716 : Nat := 4983230072969 + 3 ^ 40 * 2903716 * 2
def baseEnd_2903716 : Nat := 331333776033525873665791

theorem tailTrace_2903716 : CollatzResearch.WordTrace tailWord_2903716 prefixEnd_2903716 331333776033525873665791 := by
  unfold tailWord_2903716
  simp only [CollatzResearch.WordTrace]
  refine ⟨52953611574170161028041501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70604815432226881370722001 52953611574170161028041501)
  ·
    refine ⟨19857604340313810385515563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52953611574170161028041501 19857604340313810385515563)
    ·
      refine ⟨29786406510470715578273345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19857604340313810385515563 29786406510470715578273345)
      ·
        refine ⟨22339804882853036683705009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29786406510470715578273345 22339804882853036683705009)
        ·
          refine ⟨16754853662139777512778757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22339804882853036683705009 16754853662139777512778757)
          ·
            refine ⟨3141535061651208283646017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16754853662139777512778757 3141535061651208283646017)
            ·
              refine ⟨2356151296238406212734513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3141535061651208283646017 2356151296238406212734513)
              ·
                refine ⟨1767113472178804659550885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2356151296238406212734513 1767113472178804659550885)
                ·
                  refine ⟨331333776033525873665791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1767113472178804659550885 331333776033525873665791)
                  ·
                    rfl

theorem cell22_2903716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_2903716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903716 prefixEnd_2903716 := by exact prefixLift 2903716
  have htrace : WordTrace (prefixWord ++ tailWord_2903716) baseStart_2903716 baseEnd_2903716 := by
    simpa [prefixWord, tailWord_2903716, baseEnd_2903716] using wordTrace_append hprefix tailTrace_2903716
  have hstable : (prefixWord ++ tailWord_2903716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903716).length < 2 ^ (prefixWord ++ tailWord_2903716).sum := by decide
  have hdescent : baseEnd_2903716 < baseStart_2903716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903800 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 8]
def baseStart_2903800 : Nat := 118140960795 + 2903800 * 2 ^ 59
def prefixEnd_2903800 : Nat := 4983230072969 + 3 ^ 40 * 2903800 * 2
def baseEnd_2903800 : Nat := 331343361005743133965705

theorem tailTrace_2903800 : CollatzResearch.WordTrace tailWord_2903800 prefixEnd_2903800 331343361005743133965705 := by
  unfold tailWord_2903800
  simp only [CollatzResearch.WordTrace]
  refine ⟨52955143440018002201070427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70606857920024002934760569 52955143440018002201070427)
  ·
    refine ⟨79432715160027003301605641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52955143440018002201070427 79432715160027003301605641)
    ·
      refine ⟨59574536370020252476204231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79432715160027003301605641 59574536370020252476204231)
      ·
        refine ⟨89361804555030378714306347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59574536370020252476204231 89361804555030378714306347)
        ·
          refine ⟨134042706832545568071459521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89361804555030378714306347 134042706832545568071459521)
          ·
            refine ⟨100532030124409176053594641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134042706832545568071459521 100532030124409176053594641)
            ·
              refine ⟨75399022593306882040195981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100532030124409176053594641 75399022593306882040195981)
              ·
                refine ⟨28274633472490080765073493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75399022593306882040195981 28274633472490080765073493)
                ·
                  refine ⟨331343361005743133965705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28274633472490080765073493 331343361005743133965705)
                  ·
                    rfl

theorem cell22_2903800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_2903800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903800 prefixEnd_2903800 := by exact prefixLift 2903800
  have htrace : WordTrace (prefixWord ++ tailWord_2903800) baseStart_2903800 baseEnd_2903800 := by
    simpa [prefixWord, tailWord_2903800, baseEnd_2903800] using wordTrace_append hprefix tailTrace_2903800
  have hstable : (prefixWord ++ tailWord_2903800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903800).length < 2 ^ (prefixWord ++ tailWord_2903800).sum := by decide
  have hdescent : baseEnd_2903800 < baseStart_2903800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903834 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 6]
def baseStart_2903834 : Nat := 118140960795 + 2903834 * 2 ^ 59
def prefixEnd_2903834 : Nat := 4983230072969 + 3 ^ 40 * 2903834 * 2
def baseEnd_2903834 : Nat := 331347240637354882182337

theorem tailTrace_2903834 : CollatzResearch.WordTrace tailWord_2903834 prefixEnd_2903834 331347240637354882182337 := by
  unfold tailWord_2903834
  simp only [CollatzResearch.WordTrace]
  refine ⟨26477881740478207052219639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70607684641275218805919037 26477881740478207052219639)
  ·
    refine ⟨39716822610717310578329459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26477881740478207052219639 39716822610717310578329459)
    ·
      refine ⟨59575233916075965867494189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39716822610717310578329459 59575233916075965867494189)
      ·
        refine ⟨22340712718528487200310321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59575233916075965867494189 22340712718528487200310321)
        ·
          refine ⟨16755534538896365400232741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22340712718528487200310321 16755534538896365400232741)
          ·
            refine ⟨3141662726043068512543639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16755534538896365400232741 3141662726043068512543639)
            ·
              refine ⟨4712494089064602768815459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141662726043068512543639 4712494089064602768815459)
              ·
                refine ⟨7068741133596904153223189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4712494089064602768815459 7068741133596904153223189)
                ·
                  refine ⟨331347240637354882182337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7068741133596904153223189 331347240637354882182337)
                  ·
                    rfl

theorem cell22_2903834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_2903834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903834 prefixEnd_2903834 := by exact prefixLift 2903834
  have htrace : WordTrace (prefixWord ++ tailWord_2903834) baseStart_2903834 baseEnd_2903834 := by
    simpa [prefixWord, tailWord_2903834, baseEnd_2903834] using wordTrace_append hprefix tailTrace_2903834
  have hstable : (prefixWord ++ tailWord_2903834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903834).length < 2 ^ (prefixWord ++ tailWord_2903834).sum := by decide
  have hdescent : baseEnd_2903834 < baseStart_2903834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903864 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 2, 4]
def baseStart_2903864 : Nat := 118140960795 + 2903864 * 2 ^ 59
def prefixEnd_2903864 : Nat := 4983230072969 + 3 ^ 40 * 2903864 * 2
def baseEnd_2903864 : Nat := 994051991525154568296919

theorem tailTrace_2903864 : CollatzResearch.WordTrace tailWord_2903864 prefixEnd_2903864 994051991525154568296919 := by
  unfold tailWord_2903864
  simp only [CollatzResearch.WordTrace]
  refine ⟨52956310575902071666235323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70608414101202762221647097 52956310575902071666235323)
  ·
    refine ⟨79434465863853107499352985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52956310575902071666235323 79434465863853107499352985)
    ·
      refine ⟨59575849397889830624514739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79434465863853107499352985 59575849397889830624514739)
      ·
        refine ⟨89363774096834745936772109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59575849397889830624514739 89363774096834745936772109)
        ·
          refine ⟨33511415286313029726289541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89363774096834745936772109 33511415286313029726289541)
          ·
            refine ⟨6283390366183693073679289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33511415286313029726289541 6283390366183693073679289)
            ·
              refine ⟨4712542774637769805259467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6283390366183693073679289 4712542774637769805259467)
              ·
                refine ⟨7068814161956654707889201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4712542774637769805259467 7068814161956654707889201)
                ·
                  refine ⟨5301610621467491030916901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7068814161956654707889201 5301610621467491030916901)
                  ·
                    refine ⟨994051991525154568296919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5301610621467491030916901 994051991525154568296919)
                    ·
                      rfl

theorem cell22_2903864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_2903864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903864 prefixEnd_2903864 := by exact prefixLift 2903864
  have htrace : WordTrace (prefixWord ++ tailWord_2903864) baseStart_2903864 baseEnd_2903864 := by
    simpa [prefixWord, tailWord_2903864, baseEnd_2903864] using wordTrace_append hprefix tailTrace_2903864
  have hstable : (prefixWord ++ tailWord_2903864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903864).length < 2 ^ (prefixWord ++ tailWord_2903864).sum := by decide
  have hdescent : baseEnd_2903864 < baseStart_2903864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903885 : List Nat := [1, 6, 1, 2, 1, 3, 2, 2, 4]
def baseStart_2903885 : Nat := 118140960795 + 2903885 * 2 ^ 59
def prefixEnd_2903885 : Nat := 4983230072969 + 3 ^ 40 * 2903885 * 2
def baseEnd_2903885 : Nat := 331353060084772504507285

theorem tailTrace_2903885 : CollatzResearch.WordTrace tailWord_2903885 prefixEnd_2903885 331353060084772504507285 := by
  unfold tailWord_2903885
  simp only [CollatzResearch.WordTrace]
  refine ⟨105913387084728063918985109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70608924723152042612656739 105913387084728063918985109)
  ·
    refine ⟨4964690019596627996202427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105913387084728063918985109 4964690019596627996202427)
    ·
      refine ⟨7447035029394941994303641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4964690019596627996202427 7447035029394941994303641)
      ·
        refine ⟨5585276272046206495727731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7447035029394941994303641 5585276272046206495727731)
        ·
          refine ⟨8377914408069309743591597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5585276272046206495727731 8377914408069309743591597)
          ·
            refine ⟨3141717903025991153846849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8377914408069309743591597 3141717903025991153846849)
            ·
              refine ⟨2356288427269493365385137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3141717903025991153846849 2356288427269493365385137)
              ·
                refine ⟨1767216320452120024038853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2356288427269493365385137 1767216320452120024038853)
                ·
                  refine ⟨331353060084772504507285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1767216320452120024038853 331353060084772504507285)
                  ·
                    rfl

theorem cell22_2903885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_2903885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903885 prefixEnd_2903885 := by exact prefixLift 2903885
  have htrace : WordTrace (prefixWord ++ tailWord_2903885) baseStart_2903885 baseEnd_2903885 := by
    simpa [prefixWord, tailWord_2903885, baseEnd_2903885] using wordTrace_append hprefix tailTrace_2903885
  have hstable : (prefixWord ++ tailWord_2903885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903885).length < 2 ^ (prefixWord ++ tailWord_2903885).sum := by decide
  have hdescent : baseEnd_2903885 < baseStart_2903885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903922 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_2903922 : Nat := 118140960795 + 2903922 * 2 ^ 59
def prefixEnd_2903922 : Nat := 4983230072969 + 3 ^ 40 * 2903922 * 2
def baseEnd_2903922 : Nat := 994071846110461750346741

theorem tailTrace_2903922 : CollatzResearch.WordTrace tailWord_2903922 prefixEnd_2903922 994071846110461750346741 := by
  unfold tailWord_2903922
  simp only [CollatzResearch.WordTrace]
  refine ⟨26478684146398504809520505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70609824390396012825388013 26478684146398504809520505)
  ·
    refine ⟨19859013109798878607140379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26478684146398504809520505 19859013109798878607140379)
    ·
      refine ⟨29788519664698317910710569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19859013109798878607140379 29788519664698317910710569)
      ·
        refine ⟨22341389748523738433032927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29788519664698317910710569 22341389748523738433032927)
        ·
          refine ⟨33512084622785607649549391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22341389748523738433032927 33512084622785607649549391)
          ·
            refine ⟨50268126934178411474324087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33512084622785607649549391 50268126934178411474324087)
            ·
              refine ⟨75402190401267617211486131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50268126934178411474324087 75402190401267617211486131)
              ·
                refine ⟨113103285601901425817229197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75402190401267617211486131 113103285601901425817229197)
                ·
                  refine ⟨42413732100713034681460949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113103285601901425817229197 42413732100713034681460949)
                  ·
                    refine ⟨994071846110461750346741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42413732100713034681460949 994071846110461750346741)
                    ·
                      rfl

theorem cell22_2903922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_2903922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903922 prefixEnd_2903922 := by exact prefixLift 2903922
  have htrace : WordTrace (prefixWord ++ tailWord_2903922) baseStart_2903922 baseEnd_2903922 := by
    simpa [prefixWord, tailWord_2903922, baseEnd_2903922] using wordTrace_append hprefix tailTrace_2903922
  have hstable : (prefixWord ++ tailWord_2903922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903922).length < 2 ^ (prefixWord ++ tailWord_2903922).sum := by decide
  have hdescent : baseEnd_2903922 < baseStart_2903922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903952 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 6]
def baseStart_2903952 : Nat := 118140960795 + 2903952 * 2 ^ 59
def prefixEnd_2903952 : Nat := 4983230072969 + 3 ^ 40 * 2903952 * 2
def baseEnd_2903952 : Nat := 331360705241183890698883

theorem tailTrace_2903952 : CollatzResearch.WordTrace tailWord_2903952 prefixEnd_2903952 331360705241183890698883 := by
  unfold tailWord_2903952
  simp only [CollatzResearch.WordTrace]
  refine ⟨52957915387742667180837055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70610553850323556241116073 52957915387742667180837055)
  ·
    refine ⟨79436873081614000771255583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52957915387742667180837055 79436873081614000771255583)
    ·
      refine ⟨119155309622421001156883375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79436873081614000771255583 119155309622421001156883375)
      ·
        refine ⟨178732964433631501735325063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119155309622421001156883375 178732964433631501735325063)
        ·
          refine ⟨268099446650447252602987595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178732964433631501735325063 268099446650447252602987595)
          ·
            refine ⟨402149169975670878904481393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268099446650447252602987595 402149169975670878904481393)
            ·
              refine ⟨301611877481753159178361045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402149169975670878904481393 301611877481753159178361045)
              ·
                refine ⟨7069028378478589668242837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 301611877481753159178361045 7069028378478589668242837)
                ·
                  refine ⟨331360705241183890698883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7069028378478589668242837 331360705241183890698883)
                  ·
                    rfl

theorem cell22_2903952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_2903952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903952 prefixEnd_2903952 := by exact prefixLift 2903952
  have htrace : WordTrace (prefixWord ++ tailWord_2903952) baseStart_2903952 baseEnd_2903952 := by
    simpa [prefixWord, tailWord_2903952, baseEnd_2903952] using wordTrace_append hprefix tailTrace_2903952
  have hstable : (prefixWord ++ tailWord_2903952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903952).length < 2 ^ (prefixWord ++ tailWord_2903952).sum := by decide
  have hdescent : baseEnd_2903952 < baseStart_2903952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903999 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 2, 4]
def baseStart_2903999 : Nat := 118140960795 + 2903999 * 2 ^ 59
def prefixEnd_2903999 : Nat := 4983230072969 + 3 ^ 40 * 2903999 * 2
def baseEnd_2903999 : Nat := 994098204784059216171505

theorem tailTrace_2903999 : CollatzResearch.WordTrace tailWord_2903999 prefixEnd_2903999 994098204784059216171505 := by
  unfold tailWord_2903999
  simp only [CollatzResearch.WordTrace]
  refine ⟨105917545006315061388635051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70611696670876707592423367 105917545006315061388635051)
  ·
    refine ⟨158876317509472592082952577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105917545006315061388635051 158876317509472592082952577)
    ·
      refine ⟨119157238132104444062214433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158876317509472592082952577 119157238132104444062214433)
      ·
        refine ⟨89367928599078333046660825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119157238132104444062214433 89367928599078333046660825)
        ·
          refine ⟨67025946449308749784995619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89367928599078333046660825 67025946449308749784995619)
          ·
            refine ⟨100538919673963124677493429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67025946449308749784995619 100538919673963124677493429)
            ·
              refine ⟨9425523719434042938515009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100538919673963124677493429 9425523719434042938515009)
              ·
                refine ⟨7069142789575532203886257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9425523719434042938515009 7069142789575532203886257)
                ·
                  refine ⟨5301857092181649152914693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7069142789575532203886257 5301857092181649152914693)
                  ·
                    refine ⟨994098204784059216171505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5301857092181649152914693 994098204784059216171505)
                    ·
                      rfl

theorem cell22_2903999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_2903999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2903999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2903999 prefixEnd_2903999 := by exact prefixLift 2903999
  have htrace : WordTrace (prefixWord ++ tailWord_2903999) baseStart_2903999 baseEnd_2903999 := by
    simpa [prefixWord, tailWord_2903999, baseEnd_2903999] using wordTrace_append hprefix tailTrace_2903999
  have hstable : (prefixWord ++ tailWord_2903999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903999).length < 2 ^ (prefixWord ++ tailWord_2903999).sum := by decide
  have hdescent : baseEnd_2903999 < baseStart_2903999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904014 : List Nat := [4, 1, 1, 1, 2, 2, 4, 7]
def baseStart_2904014 : Nat := 118140960795 + 2904014 * 2 ^ 59
def prefixEnd_2904014 : Nat := 4983230072969 + 3 ^ 40 * 2904014 * 2
def baseEnd_2904014 : Nat := 110455926621178241894051

theorem tailTrace_2904014 : CollatzResearch.WordTrace tailWord_2904014 prefixEnd_2904014 110455926621178241894051 := by
  unfold tailWord_2904014
  simp only [CollatzResearch.WordTrace]
  refine ⟨13239761512657589868803887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70612061400840479300287397 13239761512657589868803887)
  ·
    refine ⟨19859642268986384803205831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13239761512657589868803887 19859642268986384803205831)
    ·
      refine ⟨29789463403479577204808747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19859642268986384803205831 29789463403479577204808747)
      ·
        refine ⟨44684195105219365807213121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29789463403479577204808747 44684195105219365807213121)
        ·
          refine ⟨33513146328914524355409841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44684195105219365807213121 33513146328914524355409841)
          ·
            refine ⟨25134859746685893266557381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33513146328914524355409841 25134859746685893266557381)
            ·
              refine ⟨4712786202503604987479509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25134859746685893266557381 4712786202503604987479509)
              ·
                refine ⟨110455926621178241894051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4712786202503604987479509 110455926621178241894051)
                ·
                  rfl

theorem cell22_2904014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_2904014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904014 prefixEnd_2904014 := by exact prefixLift 2904014
  have htrace : WordTrace (prefixWord ++ tailWord_2904014) baseStart_2904014 baseEnd_2904014 := by
    simpa [prefixWord, tailWord_2904014, baseEnd_2904014] using wordTrace_append hprefix tailTrace_2904014
  have hstable : (prefixWord ++ tailWord_2904014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904014).length < 2 ^ (prefixWord ++ tailWord_2904014).sum := by decide
  have hdescent : baseEnd_2904014 < baseStart_2904014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904022 : List Nat := [5, 2, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_2904022 : Nat := 118140960795 + 2904022 * 2 ^ 59
def prefixEnd_2904022 : Nat := 4983230072969 + 3 ^ 40 * 2904022 * 2
def baseEnd_2904022 : Nat := 994106078154094822846435

theorem tailTrace_2904022 : CollatzResearch.WordTrace tailWord_2904022 prefixEnd_2904022 994106078154094822846435 := by
  unfold tailWord_2904022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6619898992826983519795145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70612255923487824211148213 6619898992826983519795145)
  ·
    refine ⟨4964924244620237639846359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6619898992826983519795145 4964924244620237639846359)
    ·
      refine ⟨7447386366930356459769539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4964924244620237639846359 7447386366930356459769539)
      ·
        refine ⟨11171079550395534689654309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7447386366930356459769539 11171079550395534689654309)
        ·
          refine ⟨2094577415699162754310183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11171079550395534689654309 2094577415699162754310183)
          ·
            refine ⟨3141866123548744131465275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2094577415699162754310183 3141866123548744131465275)
            ·
              refine ⟨4712799185323116197197913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141866123548744131465275 4712799185323116197197913)
              ·
                refine ⟨3534599388992337147898435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4712799185323116197197913 3534599388992337147898435)
                ·
                  refine ⟨5301899083488505721847653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3534599388992337147898435 5301899083488505721847653)
                  ·
                    refine ⟨994106078154094822846435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5301899083488505721847653 994106078154094822846435)
                    ·
                      rfl

theorem cell22_2904022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_2904022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904022 prefixEnd_2904022 := by exact prefixLift 2904022
  have htrace : WordTrace (prefixWord ++ tailWord_2904022) baseStart_2904022 baseEnd_2904022 := by
    simpa [prefixWord, tailWord_2904022, baseEnd_2904022] using wordTrace_append hprefix tailTrace_2904022
  have hstable : (prefixWord ++ tailWord_2904022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904022).length < 2 ^ (prefixWord ++ tailWord_2904022).sum := by decide
  have hdescent : baseEnd_2904022 < baseStart_2904022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904059 : List Nat := [1, 1, 1, 1, 1, 3, 5, 4, 5]
def baseStart_2904059 : Nat := 118140960795 + 2904059 * 2 ^ 59
def prefixEnd_2904059 : Nat := 4983230072969 + 3 ^ 40 * 2904059 * 2
def baseEnd_2904059 : Nat := 331372914670079686557107

theorem tailTrace_2904059 : CollatzResearch.WordTrace tailWord_2904059 prefixEnd_2904059 331372914670079686557107 := by
  unfold tailWord_2904059
  simp only [CollatzResearch.WordTrace]
  refine ⟨105919733386097691635819231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70613155590731794423879487 105919733386097691635819231)
  ·
    refine ⟨158879600079146537453728847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105919733386097691635819231 158879600079146537453728847)
    ·
      refine ⟨238319400118719806180593271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158879600079146537453728847 238319400118719806180593271)
      ·
        refine ⟨357479100178079709270889907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238319400118719806180593271 357479100178079709270889907)
        ·
          refine ⟨536218650267119563906334861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357479100178079709270889907 536218650267119563906334861)
          ·
            refine ⟨201081993850169836464875573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 536218650267119563906334861 201081993850169836464875573)
            ·
              refine ⟨18851436923453422168582085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201081993850169836464875573 18851436923453422168582085)
              ·
                refine ⟨3534644423147516656609141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18851436923453422168582085 3534644423147516656609141)
                ·
                  refine ⟨331372914670079686557107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3534644423147516656609141 331372914670079686557107)
                  ·
                    rfl

theorem cell22_2904059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 5].length) (baseStart_2904059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904059 prefixEnd_2904059 := by exact prefixLift 2904059
  have htrace : WordTrace (prefixWord ++ tailWord_2904059) baseStart_2904059 baseEnd_2904059 := by
    simpa [prefixWord, tailWord_2904059, baseEnd_2904059] using wordTrace_append hprefix tailTrace_2904059
  have hstable : (prefixWord ++ tailWord_2904059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904059).length < 2 ^ (prefixWord ++ tailWord_2904059).sum := by decide
  have hdescent : baseEnd_2904059 < baseStart_2904059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904119 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 3, 5]
def baseStart_2904119 : Nat := 118140960795 + 2904119 * 2 ^ 59
def prefixEnd_2904119 : Nat := 4983230072969 + 3 ^ 40 * 2904119 * 2
def baseEnd_2904119 : Nat := 994139283236418903171137

theorem tailTrace_2904119 : CollatzResearch.WordTrace tailWord_2904119 prefixEnd_2904119 994139283236418903171137 := by
  unfold tailWord_2904119
  simp only [CollatzResearch.WordTrace]
  refine ⟨105921921765880321883003411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70614614510586881255335607 105921921765880321883003411)
  ·
    refine ⟨158882882648820482824505117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105921921765880321883003411 158882882648820482824505117)
    ·
      refine ⟨59581080993307681059189419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158882882648820482824505117 59581080993307681059189419)
      ·
        refine ⟨89371621489961521588784129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59581080993307681059189419 89371621489961521588784129)
        ·
          refine ⟨67028716117471141191588097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89371621489961521588784129 67028716117471141191588097)
          ·
            refine ⟨50271537088103355893691073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67028716117471141191588097 50271537088103355893691073)
            ·
              refine ⟨37703652816077516920268305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50271537088103355893691073 37703652816077516920268305)
              ·
                refine ⟨28277739612058137690201229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37703652816077516920268305 28277739612058137690201229)
                ·
                  refine ⟨10604152354521801633825461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28277739612058137690201229 10604152354521801633825461)
                  ·
                    refine ⟨994139283236418903171137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10604152354521801633825461 994139283236418903171137)
                    ·
                      rfl

theorem cell22_2904119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_2904119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904119 prefixEnd_2904119 := by exact prefixLift 2904119
  have htrace : WordTrace (prefixWord ++ tailWord_2904119) baseStart_2904119 baseEnd_2904119 := by
    simpa [prefixWord, tailWord_2904119, baseEnd_2904119] using wordTrace_append hprefix tailTrace_2904119
  have hstable : (prefixWord ++ tailWord_2904119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904119).length < 2 ^ (prefixWord ++ tailWord_2904119).sum := by decide
  have hdescent : baseEnd_2904119 < baseStart_2904119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904256 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 8]
def baseStart_2904256 : Nat := 118140960795 + 2904256 * 2 ^ 59
def prefixEnd_2904256 : Nat := 4983230072969 + 3 ^ 40 * 2904256 * 2
def baseEnd_2904256 : Nat := 331395393712065404165239

theorem tailTrace_2904256 : CollatzResearch.WordTrace tailWord_2904256 prefixEnd_2904256 331395393712065404165239 := by
  unfold tailWord_2904256
  simp only [CollatzResearch.WordTrace]
  refine ⟨52963459283191997140370311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70617945710922662853827081 52963459283191997140370311)
  ·
    refine ⟨79445188924787995710555467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52963459283191997140370311 79445188924787995710555467)
    ·
      refine ⟨119167783387181993565833201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79445188924787995710555467 119167783387181993565833201)
      ·
        refine ⟨89375837540386495174374901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119167783387181993565833201 89375837540386495174374901)
        ·
          refine ⟨8378984769411233922597647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89375837540386495174374901 8378984769411233922597647)
          ·
            refine ⟨12568477154116850883896471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8378984769411233922597647 12568477154116850883896471)
            ·
              refine ⟨18852715731175276325844707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12568477154116850883896471 18852715731175276325844707)
              ·
                refine ⟨28279073596762914488767061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18852715731175276325844707 28279073596762914488767061)
                ·
                  refine ⟨331395393712065404165239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28279073596762914488767061 331395393712065404165239)
                  ·
                    rfl

theorem cell22_2904256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_2904256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904256 prefixEnd_2904256 := by exact prefixLift 2904256
  have htrace : WordTrace (prefixWord ++ tailWord_2904256) baseStart_2904256 baseEnd_2904256 := by
    simpa [prefixWord, tailWord_2904256, baseEnd_2904256] using wordTrace_append hprefix tailTrace_2904256
  have hstable : (prefixWord ++ tailWord_2904256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904256).length < 2 ^ (prefixWord ++ tailWord_2904256).sum := by decide
  have hdescent : baseEnd_2904256 < baseStart_2904256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904271 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 1, 5]
def baseStart_2904271 : Nat := 118140960795 + 2904271 * 2 ^ 59
def prefixEnd_2904271 : Nat := 4983230072969 + 3 ^ 40 * 2904271 * 2
def baseEnd_2904271 : Nat := 994191315942741173370671

theorem tailTrace_2904271 : CollatzResearch.WordTrace tailWord_2904271 prefixEnd_2904271 994191315942741173370671 := by
  unfold tailWord_2904271
  simp only [CollatzResearch.WordTrace]
  refine ⟨105927465661329651842536667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70618310440886434561691111 105927465661329651842536667)
  ·
    refine ⟨158891198491994477763805001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105927465661329651842536667 158891198491994477763805001)
    ·
      refine ⟨119168398868995858322853751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158891198491994477763805001 119168398868995858322853751)
      ·
        refine ⟨178752598303493787484280627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119168398868995858322853751 178752598303493787484280627)
        ·
          refine ⟨268128897455240681226420941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178752598303493787484280627 268128897455240681226420941)
          ·
            refine ⟨100548336545715255459907853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268128897455240681226420941 100548336545715255459907853)
            ·
              refine ⟨37705626204643220797465445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100548336545715255459907853 37705626204643220797465445)
              ·
                refine ⟨7069804913370603899524771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37705626204643220797465445 7069804913370603899524771)
                ·
                  refine ⟨10604707370055905849287157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7069804913370603899524771 10604707370055905849287157)
                  ·
                    refine ⟨994191315942741173370671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10604707370055905849287157 994191315942741173370671)
                    ·
                      rfl

theorem cell22_2904271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_2904271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904271 prefixEnd_2904271 := by exact prefixLift 2904271
  have htrace : WordTrace (prefixWord ++ tailWord_2904271) baseStart_2904271 baseEnd_2904271 := by
    simpa [prefixWord, tailWord_2904271, baseEnd_2904271] using wordTrace_append hprefix tailTrace_2904271
  have hstable : (prefixWord ++ tailWord_2904271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904271).length < 2 ^ (prefixWord ++ tailWord_2904271).sum := by decide
  have hdescent : baseEnd_2904271 < baseStart_2904271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904273 : List Nat := [1, 2, 2, 1, 2, 2, 3, 5, 4]
def baseStart_2904273 : Nat := 118140960795 + 2904273 * 2 ^ 59
def prefixEnd_2904273 : Nat := 4983230072969 + 3 ^ 40 * 2904273 * 2
def baseEnd_2904273 : Nat := 331397333527871278273555

theorem tailTrace_2904273 : CollatzResearch.WordTrace tailWord_2904273 prefixEnd_2904273 331397333527871278273555 := by
  unfold tailWord_2904273
  simp only [CollatzResearch.WordTrace]
  refine ⟨105927538607322406184109473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70618359071548270789406315 105927538607322406184109473)
  ·
    refine ⟨79445653955491804638082105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105927538607322406184109473 79445653955491804638082105)
    ·
      refine ⟨59584240466618853478561579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79445653955491804638082105 59584240466618853478561579)
      ·
        refine ⟨89376360699928280217842369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59584240466618853478561579 89376360699928280217842369)
        ·
          refine ⟨67032270524946210163381777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89376360699928280217842369 67032270524946210163381777)
          ·
            refine ⟨50274202893709657622536333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67032270524946210163381777 50274202893709657622536333)
            ·
              refine ⟨18852826085141121608451125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50274202893709657622536333 18852826085141121608451125)
              ·
                refine ⟨1767452445481980150792293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18852826085141121608451125 1767452445481980150792293)
                ·
                  refine ⟨331397333527871278273555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1767452445481980150792293 331397333527871278273555)
                  ·
                    rfl

theorem cell22_2904273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 4].length) (baseStart_2904273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904273 prefixEnd_2904273 := by exact prefixLift 2904273
  have htrace : WordTrace (prefixWord ++ tailWord_2904273) baseStart_2904273 baseEnd_2904273 := by
    simpa [prefixWord, tailWord_2904273, baseEnd_2904273] using wordTrace_append hprefix tailTrace_2904273
  have hstable : (prefixWord ++ tailWord_2904273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904273).length < 2 ^ (prefixWord ++ tailWord_2904273).sum := by decide
  have hdescent : baseEnd_2904273 < baseStart_2904273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904288 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 4, 3]
def baseStart_2904288 : Nat := 118140960795 + 2904288 * 2 ^ 59
def prefixEnd_2904288 : Nat := 4983230072969 + 3 ^ 40 * 2904288 * 2
def baseEnd_2904288 : Nat := 994197135390158795695619

theorem tailTrace_2904288 : CollatzResearch.WordTrace tailWord_2904288 prefixEnd_2904288 994197135390158795695619 := by
  unfold tailWord_2904288
  simp only [CollatzResearch.WordTrace]
  refine ⟨52964042851134031872952759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70618723801512042497270345 52964042851134031872952759)
  ·
    refine ⟨79446064276701047809429139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52964042851134031872952759 79446064276701047809429139)
    ·
      refine ⟨119169096415051571714143709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79446064276701047809429139 119169096415051571714143709)
      ·
        refine ⟨44688411155644339392803891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119169096415051571714143709 44688411155644339392803891)
        ·
          refine ⟨67032616733466509089205837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44688411155644339392803891 67032616733466509089205837)
          ·
            refine ⟨25137231275049940908452189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67032616733466509089205837 25137231275049940908452189)
            ·
              refine ⟨9426461728143727840669571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25137231275049940908452189 9426461728143727840669571)
              ·
                refine ⟨14139692592215591761004357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9426461728143727840669571 14139692592215591761004357)
                ·
                  refine ⟨2651192361040423455188317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14139692592215591761004357 2651192361040423455188317)
                  ·
                    refine ⟨994197135390158795695619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2651192361040423455188317 994197135390158795695619)
                    ·
                      rfl

theorem cell22_2904288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 4, 3].length) (baseStart_2904288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904288 prefixEnd_2904288 := by exact prefixLift 2904288
  have htrace : WordTrace (prefixWord ++ tailWord_2904288) baseStart_2904288 baseEnd_2904288 := by
    simpa [prefixWord, tailWord_2904288, baseEnd_2904288] using wordTrace_append hprefix tailTrace_2904288
  have hstable : (prefixWord ++ tailWord_2904288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904288).length < 2 ^ (prefixWord ++ tailWord_2904288).sum := by decide
  have hdescent : baseEnd_2904288 < baseStart_2904288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904318 : List Nat := [4, 2, 2, 1, 1, 1, 3, 8]
def baseStart_2904318 : Nat := 118140960795 + 2904318 * 2 ^ 59
def prefixEnd_2904318 : Nat := 4983230072969 + 3 ^ 40 * 2904318 * 2
def baseEnd_2904318 : Nat := 110467489444805413049503

theorem tailTrace_2904318 : CollatzResearch.WordTrace tailWord_2904318 prefixEnd_2904318 110467489444805413049503 := by
  unfold tailWord_2904318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13241147486519922358687201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70619453261439585912998405 13241147486519922358687201)
  ·
    refine ⟨9930860614889941769015401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13241147486519922358687201 9930860614889941769015401)
    ·
      refine ⟨7448145461167456326761551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9930860614889941769015401 7448145461167456326761551)
      ·
        refine ⟨11172218191751184490142327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7448145461167456326761551 11172218191751184490142327)
        ·
          refine ⟨16758327287626776735213491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11172218191751184490142327 16758327287626776735213491)
          ·
            refine ⟨25137490931440165102820237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16758327287626776735213491 25137490931440165102820237)
            ·
              refine ⟨9426559099290061913557589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25137490931440165102820237 9426559099290061913557589)
              ·
                refine ⟨110467489444805413049503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9426559099290061913557589 110467489444805413049503)
                ·
                  rfl

theorem cell22_2904318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_2904318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904318 prefixEnd_2904318 := by exact prefixLift 2904318
  have htrace : WordTrace (prefixWord ++ tailWord_2904318) baseStart_2904318 baseEnd_2904318 := by
    simpa [prefixWord, tailWord_2904318, baseEnd_2904318] using wordTrace_append hprefix tailTrace_2904318
  have hstable : (prefixWord ++ tailWord_2904318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904318).length < 2 ^ (prefixWord ++ tailWord_2904318).sum := by decide
  have hdescent : baseEnd_2904318 < baseStart_2904318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904324 : List Nat := [2, 3, 2, 2, 4, 1, 1, 3, 4]
def baseStart_2904324 : Nat := 118140960795 + 2904324 * 2 ^ 59
def prefixEnd_2904324 : Nat := 4983230072969 + 3 ^ 40 * 2904324 * 2
def baseEnd_2904324 : Nat := 331403152975288900598503

theorem tailTrace_2904324 : CollatzResearch.WordTrace tailWord_2904324 prefixEnd_2904324 331403152975288900598503 := by
  unfold tailWord_2904324
  simp only [CollatzResearch.WordTrace]
  refine ⟨52964699365068820947108013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70619599153425094596144017 52964699365068820947108013)
  ·
    refine ⟨19861762261900807855165505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52964699365068820947108013 19861762261900807855165505)
    ·
      refine ⟨14896321696425605891374129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19861762261900807855165505 14896321696425605891374129)
      ·
        refine ⟨11172241272319204418530597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14896321696425605891374129 11172241272319204418530597)
        ·
          refine ⟨2094795238559850828474487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11172241272319204418530597 2094795238559850828474487)
          ·
            refine ⟨3142192857839776242711731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2094795238559850828474487 3142192857839776242711731)
            ·
              refine ⟨4713289286759664364067597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3142192857839776242711731 4713289286759664364067597)
              ·
                refine ⟨1767483482534874136525349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4713289286759664364067597 1767483482534874136525349)
                ·
                  refine ⟨331403152975288900598503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1767483482534874136525349 331403152975288900598503)
                  ·
                    rfl

theorem cell22_2904324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_2904324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904324 prefixEnd_2904324 := by exact prefixLift 2904324
  have htrace : WordTrace (prefixWord ++ tailWord_2904324) baseStart_2904324 baseEnd_2904324 := by
    simpa [prefixWord, tailWord_2904324, baseEnd_2904324] using wordTrace_append hprefix tailTrace_2904324
  have hstable : (prefixWord ++ tailWord_2904324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904324).length < 2 ^ (prefixWord ++ tailWord_2904324).sum := by decide
  have hdescent : baseEnd_2904324 < baseStart_2904324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904412 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 2, 5]
def baseStart_2904412 : Nat := 118140960795 + 2904412 * 2 ^ 59
def prefixEnd_2904412 : Nat := 4983230072969 + 3 ^ 40 * 2904412 * 2
def baseEnd_2904412 : Nat := 994239583124263805595239

theorem tailTrace_2904412 : CollatzResearch.WordTrace tailWord_2904412 prefixEnd_2904412 994239583124263805595239 := by
  unfold tailWord_2904412
  simp only [CollatzResearch.WordTrace]
  refine ⟨52966304176909416461709745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70621738902545888615612993 52966304176909416461709745)
  ·
    refine ⟨39724728132682062346282309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52966304176909416461709745 39724728132682062346282309)
    ·
      refine ⟨7448386524877886689927933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39724728132682062346282309 7448386524877886689927933)
      ·
        refine ⟨2793144946829207508722975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7448386524877886689927933 2793144946829207508722975)
        ·
          refine ⟨4189717420243811263084463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2793144946829207508722975 4189717420243811263084463)
          ·
            refine ⟨6284576130365716894626695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189717420243811263084463 6284576130365716894626695)
            ·
              refine ⟨9426864195548575341940043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6284576130365716894626695 9426864195548575341940043)
              ·
                refine ⟨14140296293322863012910065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9426864195548575341940043 14140296293322863012910065)
                ·
                  refine ⟨10605222219992147259682549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14140296293322863012910065 10605222219992147259682549)
                  ·
                    refine ⟨994239583124263805595239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10605222219992147259682549 994239583124263805595239)
                    ·
                      rfl

theorem cell22_2904412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_2904412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904412 prefixEnd_2904412 := by exact prefixLift 2904412
  have htrace : WordTrace (prefixWord ++ tailWord_2904412) baseStart_2904412 baseEnd_2904412 := by
    simpa [prefixWord, tailWord_2904412, baseEnd_2904412] using wordTrace_append hprefix tailTrace_2904412
  have hstable : (prefixWord ++ tailWord_2904412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904412).length < 2 ^ (prefixWord ++ tailWord_2904412).sum := by decide
  have hdescent : baseEnd_2904412 < baseStart_2904412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904457 : List Nat := [1, 2, 1, 1, 6, 1, 3, 2, 2, 3]
def baseStart_2904457 : Nat := 118140960795 + 2904457 * 2 ^ 59
def prefixEnd_2904457 : Nat := 4983230072969 + 3 ^ 40 * 2904457 * 2
def baseEnd_2904457 : Nat := 994254987543898688220101

theorem tailTrace_2904457 : CollatzResearch.WordTrace tailWord_2904457 prefixEnd_2904457 994254987543898688220101 := by
  unfold tailWord_2904457
  simp only [CollatzResearch.WordTrace]
  refine ⟨105934249638655805608807625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70622833092437203739205083 105934249638655805608807625)
  ·
    refine ⟨79450687228991854206605719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105934249638655805608807625 79450687228991854206605719)
    ·
      refine ⟨119176030843487781309908579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79450687228991854206605719 119176030843487781309908579)
      ·
        refine ⟨178764046265231671964862869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119176030843487781309908579 178764046265231671964862869)
        ·
          refine ⟨8379564668682734623352947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 178764046265231671964862869 8379564668682734623352947)
          ·
            refine ⟨12569347003024101935029421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8379564668682734623352947 12569347003024101935029421)
            ·
              refine ⟨4713505126134038225636033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12569347003024101935029421 4713505126134038225636033)
              ·
                refine ⟨3535128844600528669227025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4713505126134038225636033 3535128844600528669227025)
                ·
                  refine ⟨2651346633450396501920269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3535128844600528669227025 2651346633450396501920269)
                  ·
                    refine ⟨994254987543898688220101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2651346633450396501920269 994254987543898688220101)
                    ·
                      rfl

theorem cell22_2904457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 3].length) (baseStart_2904457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904457 prefixEnd_2904457 := by exact prefixLift 2904457
  have htrace : WordTrace (prefixWord ++ tailWord_2904457) baseStart_2904457 baseEnd_2904457 := by
    simpa [prefixWord, tailWord_2904457, baseEnd_2904457] using wordTrace_append hprefix tailTrace_2904457
  have hstable : (prefixWord ++ tailWord_2904457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904457).length < 2 ^ (prefixWord ++ tailWord_2904457).sum := by decide
  have hdescent : baseEnd_2904457 < baseStart_2904457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904474 : List Nat := [3, 1, 1, 4, 1, 3, 3, 1, 2, 3]
def baseStart_2904474 : Nat := 118140960795 + 2904474 * 2 ^ 59
def prefixEnd_2904474 : Nat := 4983230072969 + 3 ^ 40 * 2904474 * 2
def baseEnd_2904474 : Nat := 994260806991316310545049

theorem tailTrace_2904474 : CollatzResearch.WordTrace tailWord_2904474 prefixEnd_2904474 994260806991316310545049 := by
  unfold tailWord_2904474
  simp only [CollatzResearch.WordTrace]
  refine ⟨26483717419898554378044119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70623246453062811674784317 26483717419898554378044119)
  ·
    refine ⟨39725576129847831567066179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26483717419898554378044119 39725576129847831567066179)
    ·
      refine ⟨59588364194771747350599269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39725576129847831567066179 59588364194771747350599269)
      ·
        refine ⟨11172818286519702628237363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59588364194771747350599269 11172818286519702628237363)
        ·
          refine ⟨16759227429779553942356045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11172818286519702628237363 16759227429779553942356045)
          ·
            refine ⟨6284710286167332728383517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16759227429779553942356045 6284710286167332728383517)
            ·
              refine ⟨2356766357312749773143819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6284710286167332728383517 2356766357312749773143819)
              ·
                refine ⟨3535149535969124659715729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356766357312749773143819 3535149535969124659715729)
                ·
                  refine ⟨2651362151976843494786797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3535149535969124659715729 2651362151976843494786797)
                  ·
                    refine ⟨994260806991316310545049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2651362151976843494786797 994260806991316310545049)
                    ·
                      rfl

theorem cell22_2904474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_2904474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904474 prefixEnd_2904474 := by exact prefixLift 2904474
  have htrace : WordTrace (prefixWord ++ tailWord_2904474) baseStart_2904474 baseEnd_2904474 := by
    simpa [prefixWord, tailWord_2904474, baseEnd_2904474] using wordTrace_append hprefix tailTrace_2904474
  have hstable : (prefixWord ++ tailWord_2904474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904474).length < 2 ^ (prefixWord ++ tailWord_2904474).sum := by decide
  have hdescent : baseEnd_2904474 < baseStart_2904474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904485 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 3, 3]
def baseStart_2904485 : Nat := 118140960795 + 2904485 * 2 ^ 59
def prefixEnd_2904485 : Nat := 4983230072969 + 3 ^ 40 * 2904485 * 2
def baseEnd_2904485 : Nat := 994264572516115948520015

theorem tailTrace_2904485 : CollatzResearch.WordTrace tailWord_2904485 prefixEnd_2904485 994264572516115948520015 := by
  unfold tailWord_2904485
  simp only [CollatzResearch.WordTrace]
  refine ⟨105935270882554366390826909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70623513921702910927217939 105935270882554366390826909)
  ·
    refine ⟨39725726580957887396560091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105935270882554366390826909 39725726580957887396560091)
    ·
      refine ⟨59588589871436831094840137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39725726580957887396560091 59588589871436831094840137)
      ·
        refine ⟨44691442403577623321130103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59588589871436831094840137 44691442403577623321130103)
        ·
          refine ⟨67037163605366434981695155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44691442403577623321130103 67037163605366434981695155)
          ·
            refine ⟨100555745408049652472542733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67037163605366434981695155 100555745408049652472542733)
            ·
              refine ⟨37708404528018619677203525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100555745408049652472542733 37708404528018619677203525)
              ·
                refine ⟨7070325849003491189475661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37708404528018619677203525 7070325849003491189475661)
                ·
                  refine ⟨2651372193376309196053373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7070325849003491189475661 2651372193376309196053373)
                  ·
                    refine ⟨994264572516115948520015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2651372193376309196053373 994264572516115948520015)
                    ·
                      rfl

theorem cell22_2904485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_2904485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904485 prefixEnd_2904485 := by exact prefixLift 2904485
  have htrace : WordTrace (prefixWord ++ tailWord_2904485) baseStart_2904485 baseEnd_2904485 := by
    simpa [prefixWord, tailWord_2904485, baseEnd_2904485] using wordTrace_append hprefix tailTrace_2904485
  have hstable : (prefixWord ++ tailWord_2904485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904485).length < 2 ^ (prefixWord ++ tailWord_2904485).sum := by decide
  have hdescent : baseEnd_2904485 < baseStart_2904485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904487 : List Nat := [1, 1, 6, 1, 1, 4, 2, 6]
def baseStart_2904487 : Nat := 118140960795 + 2904487 * 2 ^ 59
def prefixEnd_2904487 : Nat := 4983230072969 + 3 ^ 40 * 2904487 * 2
def baseEnd_2904487 : Nat := 110473917461887623330001

theorem tailTrace_2904487 : CollatzResearch.WordTrace tailWord_2904487 prefixEnd_2904487 110473917461887623330001 := by
  unfold tailWord_2904487
  simp only [CollatzResearch.WordTrace]
  refine ⟨105935343828547120732399715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70623562552364747154933143 105935343828547120732399715)
  ·
    refine ⟨158903015742820681098599573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105935343828547120732399715 158903015742820681098599573)
    ·
      refine ⟨7448578862944719426496855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 158903015742820681098599573 7448578862944719426496855)
      ·
        refine ⟨11172868294417079139745283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7448578862944719426496855 11172868294417079139745283)
        ·
          refine ⟨16759302441625618709617925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11172868294417079139745283 16759302441625618709617925)
          ·
            refine ⟨3142369207804803508053361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16759302441625618709617925 3142369207804803508053361)
            ·
              refine ⟨2356776905853602631040021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3142369207804803508053361 2356776905853602631040021)
              ·
                refine ⟨110473917461887623330001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2356776905853602631040021 110473917461887623330001)
                ·
                  rfl

theorem cell22_2904487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 6].length) (baseStart_2904487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904487 prefixEnd_2904487 := by exact prefixLift 2904487
  have htrace : WordTrace (prefixWord ++ tailWord_2904487) baseStart_2904487 baseEnd_2904487 := by
    simpa [prefixWord, tailWord_2904487, baseEnd_2904487] using wordTrace_append hprefix tailTrace_2904487
  have hstable : (prefixWord ++ tailWord_2904487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904487).length < 2 ^ (prefixWord ++ tailWord_2904487).sum := by decide
  have hdescent : baseEnd_2904487 < baseStart_2904487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904498 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 9]
def baseStart_2904498 : Nat := 118140960795 + 2904498 * 2 ^ 59
def prefixEnd_2904498 : Nat := 4983230072969 + 3 ^ 40 * 2904498 * 2
def baseEnd_2904498 : Nat := 331423007560596082648325

theorem tailTrace_2904498 : CollatzResearch.WordTrace tailWord_2904498 prefixEnd_2904498 331423007560596082648325 := by
  unfold tailWord_2904498
  simp only [CollatzResearch.WordTrace]
  refine ⟨26483936257876817402762537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70623830021004846407366765 26483936257876817402762537)
  ·
    refine ⟨19862952193407613052071903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26483936257876817402762537 19862952193407613052071903)
    ·
      refine ⟨29794428290111419578107855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19862952193407613052071903 29794428290111419578107855)
      ·
        refine ⟨44691642435167129367161783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29794428290111419578107855 44691642435167129367161783)
        ·
          refine ⟨67037463652750694050742675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44691642435167129367161783 67037463652750694050742675)
          ·
            refine ⟨100556195479126041076114013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67037463652750694050742675 100556195479126041076114013)
            ·
              refine ⟨37708573304672265403542755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100556195479126041076114013 37708573304672265403542755)
              ·
                refine ⟨56562859957008398105314133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37708573304672265403542755 56562859957008398105314133)
                ·
                  refine ⟨331423007560596082648325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56562859957008398105314133 331423007560596082648325)
                  ·
                    rfl

theorem cell22_2904498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_2904498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904498 prefixEnd_2904498 := by exact prefixLift 2904498
  have htrace : WordTrace (prefixWord ++ tailWord_2904498) baseStart_2904498 baseEnd_2904498 := by
    simpa [prefixWord, tailWord_2904498, baseEnd_2904498] using wordTrace_append hprefix tailTrace_2904498
  have hstable : (prefixWord ++ tailWord_2904498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904498).length < 2 ^ (prefixWord ++ tailWord_2904498).sum := by decide
  have hdescent : baseEnd_2904498 < baseStart_2904498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904532 : List Nat := [2, 4, 1, 2, 2, 2, 1, 3, 5]
def baseStart_2904532 : Nat := 118140960795 + 2904532 * 2 ^ 59
def prefixEnd_2904532 : Nat := 4983230072969 + 3 ^ 40 * 2904532 * 2
def baseEnd_2904532 : Nat := 331426887192207830864957

theorem tailTrace_2904532 : CollatzResearch.WordTrace tailWord_2904532 prefixEnd_2904532 331426887192207830864957 := by
  unfold tailWord_2904532
  simp only [CollatzResearch.WordTrace]
  refine ⟨52968492556692046708893925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70624656742256062278525233 52968492556692046708893925)
  ·
    refine ⟨9931592354379758757917611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52968492556692046708893925 9931592354379758757917611)
    ·
      refine ⟨14897388531569638136876417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9931592354379758757917611 14897388531569638136876417)
      ·
        refine ⟨11173041398677228602657313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14897388531569638136876417 11173041398677228602657313)
        ·
          refine ⟨8379781049007921451992985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11173041398677228602657313 8379781049007921451992985)
          ·
            refine ⟨6284835786755941088994739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8379781049007921451992985 6284835786755941088994739)
            ·
              refine ⟨9427253680133911633492109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6284835786755941088994739 9427253680133911633492109)
              ·
                refine ⟨3535220130050216862559541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9427253680133911633492109 3535220130050216862559541)
                ·
                  refine ⟨331426887192207830864957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3535220130050216862559541 331426887192207830864957)
                  ·
                    rfl

theorem cell22_2904532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_2904532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904532 prefixEnd_2904532 := by exact prefixLift 2904532
  have htrace : WordTrace (prefixWord ++ tailWord_2904532) baseStart_2904532 baseEnd_2904532 := by
    simpa [prefixWord, tailWord_2904532, baseEnd_2904532] using wordTrace_append hprefix tailTrace_2904532
  have hstable : (prefixWord ++ tailWord_2904532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904532).length < 2 ^ (prefixWord ++ tailWord_2904532).sum := by decide
  have hdescent : baseEnd_2904532 < baseStart_2904532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904545 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 3, 4]
def baseStart_2904545 : Nat := 118140960795 + 2904545 * 2 ^ 59
def prefixEnd_2904545 : Nat := 4983230072969 + 3 ^ 40 * 2904545 * 2
def baseEnd_2904545 : Nat := 994285111742295792019831

theorem tailTrace_2904545 : CollatzResearch.WordTrace tailWord_2904545 prefixEnd_2904545 994285111742295792019831 := by
  unfold tailWord_2904545
  simp only [CollatzResearch.WordTrace]
  refine ⟨105937459262336996638011089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70624972841557997758674059 105937459262336996638011089)
  ·
    refine ⟨79453094446752747478508317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105937459262336996638011089 79453094446752747478508317)
    ·
      refine ⟨29794910417532280304440619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79453094446752747478508317 29794910417532280304440619)
      ·
        refine ⟨44692365626298420456660929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29794910417532280304440619 44692365626298420456660929)
        ·
          refine ⟨33519274219723815342495697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44692365626298420456660929 33519274219723815342495697)
          ·
            refine ⟨25139455664792861506871773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33519274219723815342495697 25139455664792861506871773)
            ·
              refine ⟨9427295874297323065076915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25139455664792861506871773 9427295874297323065076915)
              ·
                refine ⟨14140943811445984597615373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9427295874297323065076915 14140943811445984597615373)
                ·
                  refine ⟨5302853929292244224105765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14140943811445984597615373 5302853929292244224105765)
                  ·
                    refine ⟨994285111742295792019831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5302853929292244224105765 994285111742295792019831)
                    ·
                      rfl

theorem cell22_2904545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_2904545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904545 prefixEnd_2904545 := by exact prefixLift 2904545
  have htrace : WordTrace (prefixWord ++ tailWord_2904545) baseStart_2904545 baseEnd_2904545 := by
    simpa [prefixWord, tailWord_2904545, baseEnd_2904545] using wordTrace_append hprefix tailTrace_2904545
  have hstable : (prefixWord ++ tailWord_2904545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904545).length < 2 ^ (prefixWord ++ tailWord_2904545).sum := by decide
  have hdescent : baseEnd_2904545 < baseStart_2904545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904622 : List Nat := [4, 1, 3, 1, 3, 1, 9]
def baseStart_2904622 : Nat := 118140960795 + 2904622 * 2 ^ 59
def prefixEnd_2904622 : Nat := 4983230072969 + 3 ^ 40 * 2904622 * 2
def baseEnd_2904622 : Nat := 36826350756144194734985

theorem tailTrace_2904622 : CollatzResearch.WordTrace tailWord_2904622 prefixEnd_2904622 36826350756144194734985 := by
  unfold tailWord_2904622
  simp only [CollatzResearch.WordTrace]
  refine ⟨13242533460382254848570515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70626845122038692525709413 13242533460382254848570515)
  ·
    refine ⟨19863800190573382272855773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13242533460382254848570515 19863800190573382272855773)
    ·
      refine ⟨7448925071465018352320915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19863800190573382272855773 7448925071465018352320915)
      ·
        refine ⟨11173387607197527528481373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7448925071465018352320915 11173387607197527528481373)
        ·
          refine ⟨4190020352699072823180515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11173387607197527528481373 4190020352699072823180515)
          ·
            refine ⟨6285030529048609234770773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4190020352699072823180515 6285030529048609234770773)
            ·
              refine ⟨36826350756144194734985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6285030529048609234770773 36826350756144194734985)
              ·
                rfl

theorem cell22_2904622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 9].length) (baseStart_2904622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904622 prefixEnd_2904622 := by exact prefixLift 2904622
  have htrace : WordTrace (prefixWord ++ tailWord_2904622) baseStart_2904622 baseEnd_2904622 := by
    simpa [prefixWord, tailWord_2904622, baseEnd_2904622] using wordTrace_append hprefix tailTrace_2904622
  have hstable : (prefixWord ++ tailWord_2904622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904622).length < 2 ^ (prefixWord ++ tailWord_2904622).sum := by decide
  have hdescent : baseEnd_2904622 < baseStart_2904622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904688 : List Nat := [2, 1, 1, 1, 7, 1, 3, 2, 1, 3]
def baseStart_2904688 : Nat := 118140960795 + 2904688 * 2 ^ 59
def prefixEnd_2904688 : Nat := 4983230072969 + 3 ^ 40 * 2904688 * 2
def baseEnd_2904688 : Nat := 994334063564691085694393

theorem tailTrace_2904688 : CollatzResearch.WordTrace tailWord_2904688 prefixEnd_2904688 994334063564691085694393 := by
  unfold tailWord_2904688
  simp only [CollatzResearch.WordTrace]
  refine ⟨52971337450409466030233359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70628449933879288040311145 52971337450409466030233359)
  ·
    refine ⟨79457006175614199045350039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52971337450409466030233359 79457006175614199045350039)
    ·
      refine ⟨119185509263421298568025059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79457006175614199045350039 119185509263421298568025059)
      ·
        refine ⟨178778263895131947852037589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119185509263421298568025059 178778263895131947852037589)
        ·
          refine ⟨4190115560042155027782131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 178778263895131947852037589 4190115560042155027782131)
          ·
            refine ⟨6285173340063232541673197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4190115560042155027782131 6285173340063232541673197)
            ·
              refine ⟨2356940002523712203127449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6285173340063232541673197 2356940002523712203127449)
              ·
                refine ⟨1767705001892784152345587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2356940002523712203127449 1767705001892784152345587)
                ·
                  refine ⟨2651557502839176228518381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767705001892784152345587 2651557502839176228518381)
                  ·
                    refine ⟨994334063564691085694393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2651557502839176228518381 994334063564691085694393)
                    ·
                      rfl

theorem cell22_2904688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 1, 3].length) (baseStart_2904688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904688 prefixEnd_2904688 := by exact prefixLift 2904688
  have htrace : WordTrace (prefixWord ++ tailWord_2904688) baseStart_2904688 baseEnd_2904688 := by
    simpa [prefixWord, tailWord_2904688, baseEnd_2904688] using wordTrace_append hprefix tailTrace_2904688
  have hstable : (prefixWord ++ tailWord_2904688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904688).length < 2 ^ (prefixWord ++ tailWord_2904688).sum := by decide
  have hdescent : baseEnd_2904688 < baseStart_2904688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904701 : List Nat := [1, 4, 1, 1, 5, 2, 2, 1, 5]
def baseStart_2904701 : Nat := 118140960795 + 2904701 * 2 ^ 59
def prefixEnd_2904701 : Nat := 4983230072969 + 3 ^ 40 * 2904701 * 2
def baseEnd_2904701 : Nat := 331446171243454461706451

theorem tailTrace_2904701 : CollatzResearch.WordTrace tailWord_2904701 prefixEnd_2904701 331446171243454461706451 := by
  unfold tailWord_2904701
  simp only [CollatzResearch.WordTrace]
  refine ⟨105943149049771835280689957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70628766033181223520459971 105943149049771835280689957)
  ·
    refine ⟨19864340446832219115129367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105943149049771835280689957 19864340446832219115129367)
    ·
      refine ⟨29796510670248328672694051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19864340446832219115129367 29796510670248328672694051)
      ·
        refine ⟨44694766005372493009041077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29796510670248328672694051 44694766005372493009041077)
        ·
          refine ⟨4190134313003671219597601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44694766005372493009041077 4190134313003671219597601)
          ·
            refine ⟨3142600734752753414698201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4190134313003671219597601 3142600734752753414698201)
            ·
              refine ⟨2356950551064565061023651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3142600734752753414698201 2356950551064565061023651)
              ·
                refine ⟨3535425826596847591535477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356950551064565061023651 3535425826596847591535477)
                ·
                  refine ⟨331446171243454461706451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3535425826596847591535477 331446171243454461706451)
                  ·
                    rfl

theorem cell22_2904701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_2904701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904701 prefixEnd_2904701 := by exact prefixLift 2904701
  have htrace : WordTrace (prefixWord ++ tailWord_2904701) baseStart_2904701 baseEnd_2904701 := by
    simpa [prefixWord, tailWord_2904701, baseEnd_2904701] using wordTrace_append hprefix tailTrace_2904701
  have hstable : (prefixWord ++ tailWord_2904701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904701).length < 2 ^ (prefixWord ++ tailWord_2904701).sum := by decide
  have hdescent : baseEnd_2904701 < baseStart_2904701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904714 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_2904714 : Nat := 118140960795 + 2904714 * 2 ^ 59
def prefixEnd_2904714 : Nat := 4983230072969 + 3 ^ 40 * 2904714 * 2
def baseEnd_2904714 : Nat := 994342963896035684544313

theorem tailTrace_2904714 : CollatzResearch.WordTrace tailWord_2904714 prefixEnd_2904714 994342963896035684544313 := by
  unfold tailWord_2904714
  simp only [CollatzResearch.WordTrace]
  refine ⟨26485905799681184625228299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70629082132483159000608797 26485905799681184625228299)
  ·
    refine ⟨39728858699521776937842449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26485905799681184625228299 39728858699521776937842449)
    ·
      refine ⟨29796644024641332703381837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39728858699521776937842449 29796644024641332703381837)
      ·
        refine ⟨11173741509240499763768189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29796644024641332703381837 11173741509240499763768189)
        ·
          refine ⟨4190153065965187411413071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11173741509240499763768189 4190153065965187411413071)
          ·
            refine ⟨6285229598947781117119607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4190153065965187411413071 6285229598947781117119607)
            ·
              refine ⟨9427844398421671675679411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6285229598947781117119607 9427844398421671675679411)
              ·
                refine ⟨14141766597632507513519117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9427844398421671675679411 14141766597632507513519117)
                ·
                  refine ⟨5303162474112190317569669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14141766597632507513519117 5303162474112190317569669)
                  ·
                    refine ⟨994342963896035684544313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5303162474112190317569669 994342963896035684544313)
                    ·
                      rfl

theorem cell22_2904714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_2904714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904714 prefixEnd_2904714 := by exact prefixLift 2904714
  have htrace : WordTrace (prefixWord ++ tailWord_2904714) baseStart_2904714 baseEnd_2904714 := by
    simpa [prefixWord, tailWord_2904714, baseEnd_2904714] using wordTrace_append hprefix tailTrace_2904714
  have hstable : (prefixWord ++ tailWord_2904714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904714).length < 2 ^ (prefixWord ++ tailWord_2904714).sum := by decide
  have hdescent : baseEnd_2904714 < baseStart_2904714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904727 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 1, 5]
def baseStart_2904727 : Nat := 118140960795 + 2904727 * 2 ^ 59
def prefixEnd_2904727 : Nat := 4983230072969 + 3 ^ 40 * 2904727 * 2
def baseEnd_2904727 : Nat := 994347414061707983969273

theorem tailTrace_2904727 : CollatzResearch.WordTrace tailWord_2904727 prefixEnd_2904727 994347414061707983969273 := by
  unfold tailWord_2904727
  simp only [CollatzResearch.WordTrace]
  refine ⟨105944097347677641721136435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70629398231785094480757623 105944097347677641721136435)
  ·
    refine ⟨158916146021516462581704653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105944097347677641721136435 158916146021516462581704653)
    ·
      refine ⟨59593554758068673468139245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158916146021516462581704653 59593554758068673468139245)
      ·
        refine ⟨22347583034275752550552217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59593554758068673468139245 22347583034275752550552217)
        ·
          refine ⟨16760687275706814412914163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22347583034275752550552217 16760687275706814412914163)
          ·
            refine ⟨25141030913560221619371245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16760687275706814412914163 25141030913560221619371245)
            ·
              refine ⟨9427886592585083107264217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25141030913560221619371245 9427886592585083107264217)
              ·
                refine ⟨7070914944438812330448163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9427886592585083107264217 7070914944438812330448163)
                ·
                  refine ⟨10606372416658218495672245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7070914944438812330448163 10606372416658218495672245)
                  ·
                    refine ⟨994347414061707983969273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10606372416658218495672245 994347414061707983969273)
                    ·
                      rfl

theorem cell22_2904727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_2904727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904727 prefixEnd_2904727 := by exact prefixLift 2904727
  have htrace : WordTrace (prefixWord ++ tailWord_2904727) baseStart_2904727 baseEnd_2904727 := by
    simpa [prefixWord, tailWord_2904727, baseEnd_2904727] using wordTrace_append hprefix tailTrace_2904727
  have hstable : (prefixWord ++ tailWord_2904727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904727).length < 2 ^ (prefixWord ++ tailWord_2904727).sum := by decide
  have hdescent : baseEnd_2904727 < baseStart_2904727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904817 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 2, 5]
def baseStart_2904817 : Nat := 118140960795 + 2904817 * 2 ^ 59
def prefixEnd_2904817 : Nat := 4983230072969 + 3 ^ 40 * 2904817 * 2
def baseEnd_2904817 : Nat := 994378222900977749218997

theorem tailTrace_2904817 : CollatzResearch.WordTrace tailWord_2904817 prefixEnd_2904817 994378222900977749218997 := by
  unfold tailWord_2904817
  simp only [CollatzResearch.WordTrace]
  refine ⟨105947379917351587091912705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70631586611567724727941803 105947379917351587091912705)
  ·
    refine ⟨79460534938013690318934529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105947379917351587091912705 79460534938013690318934529)
    ·
      refine ⟨59595401203510267739200897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79460534938013690318934529 59595401203510267739200897)
      ·
        refine ⟨44696550902632700804400673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59595401203510267739200897 44696550902632700804400673)
        ·
          refine ⟨33522413176974525603300505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44696550902632700804400673 33522413176974525603300505)
          ·
            refine ⟨25141809882730894202475379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33522413176974525603300505 25141809882730894202475379)
            ·
              refine ⟨37712714824096341303713069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25141809882730894202475379 37712714824096341303713069)
              ·
                refine ⟨14142268059036127988892401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37712714824096341303713069 14142268059036127988892401)
                ·
                  refine ⟨10606701044277095991669301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14142268059036127988892401 10606701044277095991669301)
                  ·
                    refine ⟨994378222900977749218997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10606701044277095991669301 994378222900977749218997)
                    ·
                      rfl

theorem cell22_2904817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_2904817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904817 prefixEnd_2904817 := by exact prefixLift 2904817
  have htrace : WordTrace (prefixWord ++ tailWord_2904817) baseStart_2904817 baseEnd_2904817 := by
    simpa [prefixWord, tailWord_2904817, baseEnd_2904817] using wordTrace_append hprefix tailTrace_2904817
  have hstable : (prefixWord ++ tailWord_2904817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904817).length < 2 ^ (prefixWord ++ tailWord_2904817).sum := by decide
  have hdescent : baseEnd_2904817 < baseStart_2904817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904849 : List Nat := [1, 2, 2, 1, 1, 3, 4, 3, 1, 4]
def baseStart_2904849 : Nat := 118140960795 + 2904849 * 2 ^ 59
def prefixEnd_2904849 : Nat := 4983230072969 + 3 ^ 40 * 2904849 * 2
def baseEnd_2904849 : Nat := 994389177154940332418899

theorem tailTrace_2904849 : CollatzResearch.WordTrace tailWord_2904849 prefixEnd_2904849 994389177154940332418899 := by
  unfold tailWord_2904849
  simp only [CollatzResearch.WordTrace]
  refine ⟨105948547053235656557077601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70632364702157104371385067 105948547053235656557077601)
  ·
    refine ⟨79461410289926742417808201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105948547053235656557077601 79461410289926742417808201)
    ·
      refine ⟨59596057717445056813356151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79461410289926742417808201 59596057717445056813356151)
      ·
        refine ⟨89394086576167585220034227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59596057717445056813356151 89394086576167585220034227)
        ·
          refine ⟨134091129864251377830051341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89394086576167585220034227 134091129864251377830051341)
          ·
            refine ⟨50284173699094266686269253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134091129864251377830051341 50284173699094266686269253)
            ·
              refine ⟨9428282568580175003675485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50284173699094266686269253 9428282568580175003675485)
              ·
                refine ⟨3535605963217565626378307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9428282568580175003675485 3535605963217565626378307)
                ·
                  refine ⟨5303408944826348439567461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3535605963217565626378307 5303408944826348439567461)
                  ·
                    refine ⟨994389177154940332418899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5303408944826348439567461 994389177154940332418899)
                    ·
                      rfl

theorem cell22_2904849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_2904849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904849 prefixEnd_2904849 := by exact prefixLift 2904849
  have htrace : WordTrace (prefixWord ++ tailWord_2904849) baseStart_2904849 baseEnd_2904849 := by
    simpa [prefixWord, tailWord_2904849, baseEnd_2904849] using wordTrace_append hprefix tailTrace_2904849
  have hstable : (prefixWord ++ tailWord_2904849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904849).length < 2 ^ (prefixWord ++ tailWord_2904849).sum := by decide
  have hdescent : baseEnd_2904849 < baseStart_2904849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904864 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 6]
def baseStart_2904864 : Nat := 118140960795 + 2904864 * 2 ^ 59
def prefixEnd_2904864 : Nat := 4983230072969 + 3 ^ 40 * 2904864 * 2
def baseEnd_2904864 : Nat := 331464770653828431097951

theorem tailTrace_2904864 : CollatzResearch.WordTrace tailWord_2904864 prefixEnd_2904864 331464770653828431097951 := by
  unfold tailWord_2904864
  simp only [CollatzResearch.WordTrace]
  refine ⟨52974547074090657059436823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70632729432120876079249097 52974547074090657059436823)
  ·
    refine ⟨79461820611135985589155235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52974547074090657059436823 79461820611135985589155235)
    ·
      refine ⟨119192730916703978383732853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79461820611135985589155235 119192730916703978383732853)
      ·
        refine ⟨11174318523440997973474955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119192730916703978383732853 11174318523440997973474955)
        ·
          refine ⟨16761477785161496960212433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11174318523440997973474955 16761477785161496960212433)
          ·
            refine ⟨12571108338871122720159325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16761477785161496960212433 12571108338871122720159325)
            ·
              refine ⟨4714165627076671020059747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12571108338871122720159325 4714165627076671020059747)
              ·
                refine ⟨7071248440615006530089621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4714165627076671020059747 7071248440615006530089621)
                ·
                  refine ⟨331464770653828431097951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7071248440615006530089621 331464770653828431097951)
                  ·
                    rfl

theorem cell22_2904864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 6].length) (baseStart_2904864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904864 prefixEnd_2904864 := by exact prefixLift 2904864
  have htrace : WordTrace (prefixWord ++ tailWord_2904864) baseStart_2904864 baseEnd_2904864 := by
    simpa [prefixWord, tailWord_2904864, baseEnd_2904864] using wordTrace_append hprefix tailTrace_2904864
  have hstable : (prefixWord ++ tailWord_2904864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904864).length < 2 ^ (prefixWord ++ tailWord_2904864).sum := by decide
  have hdescent : baseEnd_2904864 < baseStart_2904864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904909 : List Nat := [1, 6, 1, 2, 12]
def baseStart_2904909 : Nat := 118140960795 + 2904909 * 2 ^ 59
def prefixEnd_2904909 : Nat := 4983230072969 + 3 ^ 40 * 2904909 * 2
def baseEnd_2904909 : Nat := 4092221055066338172505

theorem tailTrace_2904909 : CollatzResearch.WordTrace tailWord_2904909 prefixEnd_2904909 4092221055066338172505 := by
  unfold tailWord_2904909
  simp only [CollatzResearch.WordTrace]
  refine ⟨105950735433018286804261781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70633823622012191202841187 105950735433018286804261781)
  ·
    refine ⟨4966440723422732193949771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105950735433018286804261781 4966440723422732193949771)
    ·
      refine ⟨7449661085134098290924657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4966440723422732193949771 7449661085134098290924657)
      ·
        refine ⟨5587245813850573718193493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7449661085134098290924657 5587245813850573718193493)
        ·
          refine ⟨4092221055066338172505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5587245813850573718193493 4092221055066338172505)
          ·
            rfl

theorem cell22_2904909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 12].length) (baseStart_2904909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904909 prefixEnd_2904909 := by exact prefixLift 2904909
  have htrace : WordTrace (prefixWord ++ tailWord_2904909) baseStart_2904909 baseEnd_2904909 := by
    simpa [prefixWord, tailWord_2904909, baseEnd_2904909] using wordTrace_append hprefix tailTrace_2904909
  have hstable : (prefixWord ++ tailWord_2904909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904909).length < 2 ^ (prefixWord ++ tailWord_2904909).sum := by decide
  have hdescent : baseEnd_2904909 < baseStart_2904909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904913 : List Nat := [1, 2, 2, 1, 6, 1, 2, 2, 2, 3]
def baseStart_2904913 : Nat := 118140960795 + 2904913 * 2 ^ 59
def prefixEnd_2904913 : Nat := 4983230072969 + 3 ^ 40 * 2904913 * 2
def baseEnd_2904913 : Nat := 994411085662865498818703

theorem tailTrace_2904913 : CollatzResearch.WordTrace tailWord_2904913 prefixEnd_2904913 994411085662865498818703 := by
  unfold tailWord_2904913
  simp only [CollatzResearch.WordTrace]
  refine ⟨105950881325003795487407393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70633920883335863658271595 105950881325003795487407393)
  ·
    refine ⟨79463160993752846615555545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105950881325003795487407393 79463160993752846615555545)
    ·
      refine ⟨59597370745314634961666659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79463160993752846615555545 59597370745314634961666659)
      ·
        refine ⟨89396056117971952442499989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59597370745314634961666659 89396056117971952442499989)
        ·
          refine ⟨4190440130529935270742187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89396056117971952442499989 4190440130529935270742187)
          ·
            refine ⟨6285660195794902906113281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4190440130529935270742187 6285660195794902906113281)
            ·
              refine ⟨4714245146846177179584961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6285660195794902906113281 4714245146846177179584961)
              ·
                refine ⟨3535683860134632884688721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4714245146846177179584961 3535683860134632884688721)
                ·
                  refine ⟨2651762895100974663516541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3535683860134632884688721 2651762895100974663516541)
                  ·
                    refine ⟨994411085662865498818703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2651762895100974663516541 994411085662865498818703)
                    ·
                      rfl

theorem cell22_2904913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_2904913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904913 prefixEnd_2904913 := by exact prefixLift 2904913
  have htrace : WordTrace (prefixWord ++ tailWord_2904913) baseStart_2904913 baseEnd_2904913 := by
    simpa [prefixWord, tailWord_2904913, baseEnd_2904913] using wordTrace_append hprefix tailTrace_2904913
  have hstable : (prefixWord ++ tailWord_2904913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904913).length < 2 ^ (prefixWord ++ tailWord_2904913).sum := by decide
  have hdescent : baseEnd_2904913 < baseStart_2904913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904937 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 11]
def baseStart_2904937 : Nat := 118140960795 + 2904937 * 2 ^ 59
def prefixEnd_2904937 : Nat := 4983230072969 + 3 ^ 40 * 2904937 * 2
def baseEnd_2904937 : Nat := 331473100451112478739543

theorem tailTrace_2904937 : CollatzResearch.WordTrace tailWord_2904937 prefixEnd_2904937 331473100451112478739543 := by
  unfold tailWord_2904937
  simp only [CollatzResearch.WordTrace]
  refine ⟨105951756676916847586281065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70634504451277898390854043 105951756676916847586281065)
  ·
    refine ⟨79463817507687635689710799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105951756676916847586281065 79463817507687635689710799)
    ·
      refine ⟨119195726261531453534566199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79463817507687635689710799 119195726261531453534566199)
      ·
        refine ⟨178793589392297180301849299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119195726261531453534566199 178793589392297180301849299)
        ·
          refine ⟨268190384088445770452773949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178793589392297180301849299 268190384088445770452773949)
          ·
            refine ⟨100571394033167163919790231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268190384088445770452773949 100571394033167163919790231)
            ·
              refine ⟨150857091049750745879685347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100571394033167163919790231 150857091049750745879685347)
              ·
                refine ⟨226285636574626118819528021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150857091049750745879685347 226285636574626118819528021)
                ·
                  refine ⟨331473100451112478739543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 226285636574626118819528021 331473100451112478739543)
                  ·
                    rfl

theorem cell22_2904937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_2904937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904937 prefixEnd_2904937 := by exact prefixLift 2904937
  have htrace : WordTrace (prefixWord ++ tailWord_2904937) baseStart_2904937 baseEnd_2904937 := by
    simpa [prefixWord, tailWord_2904937, baseEnd_2904937] using wordTrace_append hprefix tailTrace_2904937
  have hstable : (prefixWord ++ tailWord_2904937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904937).length < 2 ^ (prefixWord ++ tailWord_2904937).sum := by decide
  have hdescent : baseEnd_2904937 < baseStart_2904937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904969 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 2, 5]
def baseStart_2904969 : Nat := 118140960795 + 2904969 * 2 ^ 59
def prefixEnd_2904969 : Nat := 4983230072969 + 3 ^ 40 * 2904969 * 2
def baseEnd_2904969 : Nat := 994430255607300019418531

theorem tailTrace_2904969 : CollatzResearch.WordTrace tailWord_2904969 prefixEnd_2904969 994430255607300019418531 := by
  unfold tailWord_2904969
  simp only [CollatzResearch.WordTrace]
  refine ⟨105952923812800917051445961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70635282541867278034297307 105952923812800917051445961)
  ·
    refine ⟨79464692859600687788584471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105952923812800917051445961 79464692859600687788584471)
    ·
      refine ⟨119197039289401031682876707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79464692859600687788584471 119197039289401031682876707)
      ·
        refine ⟨178795558934101547524315061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119197039289401031682876707 178795558934101547524315061)
        ·
          refine ⟨16762083650072020080404537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178795558934101547524315061 16762083650072020080404537)
          ·
            refine ⟨12571562737554015060303403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16762083650072020080404537 12571562737554015060303403)
            ·
              refine ⟨18857344106331022590455105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12571562737554015060303403 18857344106331022590455105)
              ·
                refine ⟨14143008079748266942841329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18857344106331022590455105 14143008079748266942841329)
                ·
                  refine ⟨10607256059811200207130997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14143008079748266942841329 10607256059811200207130997)
                  ·
                    refine ⟨994430255607300019418531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10607256059811200207130997 994430255607300019418531)
                    ·
                      rfl

theorem cell22_2904969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_2904969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2904969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2904969 prefixEnd_2904969 := by exact prefixLift 2904969
  have htrace : WordTrace (prefixWord ++ tailWord_2904969) baseStart_2904969 baseEnd_2904969 := by
    simpa [prefixWord, tailWord_2904969, baseEnd_2904969] using wordTrace_append hprefix tailTrace_2904969
  have hstable : (prefixWord ++ tailWord_2904969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904969).length < 2 ^ (prefixWord ++ tailWord_2904969).sum := by decide
  have hdescent : baseEnd_2904969 < baseStart_2904969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905001 : List Nat := [1, 2, 1, 1, 1, 1, 8, 2, 1, 4]
def baseStart_2905001 : Nat := 118140960795 + 2905001 * 2 ^ 59
def prefixEnd_2905001 : Nat := 4983230072969 + 3 ^ 40 * 2905001 * 2
def baseEnd_2905001 : Nat := 994441209861262602618433

theorem tailTrace_2905001 : CollatzResearch.WordTrace tailWord_2905001 prefixEnd_2905001 994441209861262602618433 := by
  unfold tailWord_2905001
  simp only [CollatzResearch.WordTrace]
  refine ⟨105954090948684986516610857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70636060632456657677740571 105954090948684986516610857)
  ·
    refine ⟨79465568211513739887458143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105954090948684986516610857 79465568211513739887458143)
    ·
      refine ⟨119198352317270609831187215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79465568211513739887458143 119198352317270609831187215)
      ·
        refine ⟨178797528475905914746780823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119198352317270609831187215 178797528475905914746780823)
        ·
          refine ⟨268196292713858872120171235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178797528475905914746780823 268196292713858872120171235)
          ·
            refine ⟨402294439070788308180256853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268196292713858872120171235 402294439070788308180256853)
            ·
              refine ⟨4714387957860800486487385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 402294439070788308180256853 4714387957860800486487385)
              ·
                refine ⟨3535790968395600364865539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4714387957860800486487385 3535790968395600364865539)
                ·
                  refine ⟨5303686452593400547298309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3535790968395600364865539 5303686452593400547298309)
                  ·
                    refine ⟨994441209861262602618433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5303686452593400547298309 994441209861262602618433)
                    ·
                      rfl

theorem cell22_2905001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_2905001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905001 prefixEnd_2905001 := by exact prefixLift 2905001
  have htrace : WordTrace (prefixWord ++ tailWord_2905001) baseStart_2905001 baseEnd_2905001 := by
    simpa [prefixWord, tailWord_2905001, baseEnd_2905001] using wordTrace_append hprefix tailTrace_2905001
  have hstable : (prefixWord ++ tailWord_2905001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905001).length < 2 ^ (prefixWord ++ tailWord_2905001).sum := by decide
  have hdescent : baseEnd_2905001 < baseStart_2905001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905031 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 4, 3]
def baseStart_2905031 : Nat := 118140960795 + 2905031 * 2 ^ 59
def prefixEnd_2905031 : Nat := 4983230072969 + 3 ^ 40 * 2905031 * 2
def baseEnd_2905031 : Nat := 994451479474352524368341

theorem tailTrace_2905031 : CollatzResearch.WordTrace tailWord_2905031 prefixEnd_2905031 994451479474352524368341 := by
  unfold tailWord_2905031
  simp only [CollatzResearch.WordTrace]
  refine ⟨105955185138576301640202947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70636790092384201093468631 105955185138576301640202947)
  ·
    refine ⟨158932777707864452460304421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105955185138576301640202947 158932777707864452460304421)
    ·
      refine ⟨29799895820224584836307079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158932777707864452460304421 29799895820224584836307079)
      ·
        refine ⟨44699843730336877254460619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29799895820224584836307079 44699843730336877254460619)
        ·
          refine ⟨67049765595505315881690929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44699843730336877254460619 67049765595505315881690929)
          ·
            refine ⟨50287324196628986911268197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67049765595505315881690929 50287324196628986911268197)
            ·
              refine ⟨9428873286867935045862787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50287324196628986911268197 9428873286867935045862787)
              ·
                refine ⟨14143309930301902568794181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9428873286867935045862787 14143309930301902568794181)
                ·
                  refine ⟨2651870611931606731648909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14143309930301902568794181 2651870611931606731648909)
                  ·
                    refine ⟨994451479474352524368341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2651870611931606731648909 994451479474352524368341)
                    ·
                      rfl

theorem cell22_2905031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_2905031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905031 prefixEnd_2905031 := by exact prefixLift 2905031
  have htrace : WordTrace (prefixWord ++ tailWord_2905031) baseStart_2905031 baseEnd_2905031 := by
    simpa [prefixWord, tailWord_2905031, baseEnd_2905031] using wordTrace_append hprefix tailTrace_2905031
  have hstable : (prefixWord ++ tailWord_2905031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905031).length < 2 ^ (prefixWord ++ tailWord_2905031).sum := by decide
  have hdescent : baseEnd_2905031 < baseStart_2905031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905048 : List Nat := [2, 1, 2, 2, 2, 4, 1, 3, 2, 3]
def baseStart_2905048 : Nat := 118140960795 + 2905048 * 2 ^ 59
def prefixEnd_2905048 : Nat := 4983230072969 + 3 ^ 40 * 2905048 * 2
def baseEnd_2905048 : Nat := 994457298921770146693289

theorem tailTrace_2905048 : CollatzResearch.WordTrace tailWord_2905048 prefixEnd_2905048 994457298921770146693289 := by
  unfold tailWord_2905048
  simp only [CollatzResearch.WordTrace]
  refine ⟨52977902589757356771785899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70637203453009809029047865 52977902589757356771785899)
  ·
    refine ⟨79466853884636035157678849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52977902589757356771785899 79466853884636035157678849)
    ·
      refine ⟨59600140413477026368259137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79466853884636035157678849 59600140413477026368259137)
      ·
        refine ⟨44700105310107769776194353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59600140413477026368259137 44700105310107769776194353)
        ·
          refine ⟨33525078982580827332145765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44700105310107769776194353 33525078982580827332145765)
          ·
            refine ⟨6285952309233905124777331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33525078982580827332145765 6285952309233905124777331)
            ·
              refine ⟨9428928463850857687165997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6285952309233905124777331 9428928463850857687165997)
              ·
                refine ⟨3535848173944071632687249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9428928463850857687165997 3535848173944071632687249)
                ·
                  refine ⟨2651886130458053724515437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3535848173944071632687249 2651886130458053724515437)
                  ·
                    refine ⟨994457298921770146693289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2651886130458053724515437 994457298921770146693289)
                    ·
                      rfl

theorem cell22_2905048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_2905048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905048 prefixEnd_2905048 := by exact prefixLift 2905048
  have htrace : WordTrace (prefixWord ++ tailWord_2905048) baseStart_2905048 baseEnd_2905048 := by
    simpa [prefixWord, tailWord_2905048, baseEnd_2905048] using wordTrace_append hprefix tailTrace_2905048
  have hstable : (prefixWord ++ tailWord_2905048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905048).length < 2 ^ (prefixWord ++ tailWord_2905048).sum := by decide
  have hdescent : baseEnd_2905048 < baseStart_2905048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905063 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 2, 4]
def baseStart_2905063 : Nat := 118140960795 + 2905063 * 2 ^ 59
def prefixEnd_2905063 : Nat := 4983230072969 + 3 ^ 40 * 2905063 * 2
def baseEnd_2905063 : Nat := 994462433728315107568243

theorem tailTrace_2905063 : CollatzResearch.WordTrace tailWord_2905063 prefixEnd_2905063 994462433728315107568243 := by
  unfold tailWord_2905063
  simp only [CollatzResearch.WordTrace]
  refine ⟨105956352274460371105367843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70637568182973580736911895 105956352274460371105367843)
  ·
    refine ⟨158934528411690556658051765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105956352274460371105367843 158934528411690556658051765)
    ·
      refine ⟨14900112038595989686692353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158934528411690556658051765 14900112038595989686692353)
      ·
        refine ⟨11175084028946992265019265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14900112038595989686692353 11175084028946992265019265)
        ·
          refine ⟨8381313021710244198764449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11175084028946992265019265 8381313021710244198764449)
          ·
            refine ⟨6285984766282683149073337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8381313021710244198764449 6285984766282683149073337)
            ·
              refine ⟨4714488574712012361805003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6285984766282683149073337 4714488574712012361805003)
              ·
                refine ⟨7071732862068018542707505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4714488574712012361805003 7071732862068018542707505)
                ·
                  refine ⟨5303799646551013907030629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7071732862068018542707505 5303799646551013907030629)
                  ·
                    refine ⟨994462433728315107568243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5303799646551013907030629 994462433728315107568243)
                    ·
                      rfl

theorem cell22_2905063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_2905063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905063 prefixEnd_2905063 := by exact prefixLift 2905063
  have htrace : WordTrace (prefixWord ++ tailWord_2905063) baseStart_2905063 baseEnd_2905063 := by
    simpa [prefixWord, tailWord_2905063, baseEnd_2905063] using wordTrace_append hprefix tailTrace_2905063
  have hstable : (prefixWord ++ tailWord_2905063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905063).length < 2 ^ (prefixWord ++ tailWord_2905063).sum := by decide
  have hdescent : baseEnd_2905063 < baseStart_2905063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905127 : List Nat := [1, 1, 7, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2905127 : Nat := 118140960795 + 2905127 * 2 ^ 59
def prefixEnd_2905127 : Nat := 4983230072969 + 3 ^ 40 * 2905127 * 2
def baseEnd_2905127 : Nat := 994484342236240273968047

theorem tailTrace_2905127 : CollatzResearch.WordTrace tailWord_2905127 prefixEnd_2905127 994484342236240273968047 := by
  unfold tailWord_2905127
  simp only [CollatzResearch.WordTrace]
  refine ⟨105958686546228510035697635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70639124364152340023798423 105958686546228510035697635)
  ·
    refine ⟨158938029819342765053546453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105958686546228510035697635 158938029819342765053546453)
    ·
      refine ⟨3725110073890846055942495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 158938029819342765053546453 3725110073890846055942495)
      ·
        refine ⟨5587665110836269083913743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3725110073890846055942495 5587665110836269083913743)
        ·
          refine ⟨8381497666254403625870615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5587665110836269083913743 8381497666254403625870615)
          ·
            refine ⟨12572246499381605438805923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8381497666254403625870615 12572246499381605438805923)
            ·
              refine ⟨18858369749072408158208885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12572246499381605438805923 18858369749072408158208885)
              ·
                refine ⟨1767972163975538264832083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18858369749072408158208885 1767972163975538264832083)
                ·
                  refine ⟨2651958245963307397248125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767972163975538264832083 2651958245963307397248125)
                  ·
                    refine ⟨994484342236240273968047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2651958245963307397248125 994484342236240273968047)
                    ·
                      rfl

theorem cell22_2905127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2905127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905127 prefixEnd_2905127 := by exact prefixLift 2905127
  have htrace : WordTrace (prefixWord ++ tailWord_2905127) baseStart_2905127 baseEnd_2905127 := by
    simpa [prefixWord, tailWord_2905127, baseEnd_2905127] using wordTrace_append hprefix tailTrace_2905127
  have hstable : (prefixWord ++ tailWord_2905127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905127).length < 2 ^ (prefixWord ++ tailWord_2905127).sum := by decide
  have hdescent : baseEnd_2905127 < baseStart_2905127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905140 : List Nat := [2, 5, 1, 2, 1, 1, 3, 2, 5]
def baseStart_2905140 : Nat := 118140960795 + 2905140 * 2 ^ 59
def prefixEnd_2905140 : Nat := 4983230072969 + 3 ^ 40 * 2905140 * 2
def baseEnd_2905140 : Nat := 331496264133970857797669

theorem tailTrace_2905140 : CollatzResearch.WordTrace tailWord_2905140 prefixEnd_2905140 331496264133970857797669 := by
  unfold tailWord_2905140
  simp only [CollatzResearch.WordTrace]
  refine ⟨52979580347590706627960437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70639440463454275503947249 52979580347590706627960437)
  ·
    refine ⟨4966835657586628746371291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52979580347590706627960437 4966835657586628746371291)
    ·
      refine ⟨7450253486379943119556937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4966835657586628746371291 7450253486379943119556937)
      ·
        refine ⟨5587690114784957339667703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7450253486379943119556937 5587690114784957339667703)
        ·
          refine ⟨8381535172177436009501555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5587690114784957339667703 8381535172177436009501555)
          ·
            refine ⟨12572302758266154014252333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8381535172177436009501555 12572302758266154014252333)
            ·
              refine ⟨4714613534349807755344625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12572302758266154014252333 4714613534349807755344625)
              ·
                refine ⟨3535960150762355816508469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4714613534349807755344625 3535960150762355816508469)
                ·
                  refine ⟨331496264133970857797669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3535960150762355816508469 331496264133970857797669)
                  ·
                    rfl

theorem cell22_2905140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_2905140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905140 prefixEnd_2905140 := by exact prefixLift 2905140
  have htrace : WordTrace (prefixWord ++ tailWord_2905140) baseStart_2905140 baseEnd_2905140 := by
    simpa [prefixWord, tailWord_2905140, baseEnd_2905140] using wordTrace_append hprefix tailTrace_2905140
  have hstable : (prefixWord ++ tailWord_2905140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905140).length < 2 ^ (prefixWord ++ tailWord_2905140).sum := by decide
  have hdescent : baseEnd_2905140 < baseStart_2905140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905170 : List Nat := [3, 2, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_2905170 : Nat := 118140960795 + 2905170 * 2 ^ 59
def prefixEnd_2905170 : Nat := 4983230072969 + 3 ^ 40 * 2905170 * 2
def baseEnd_2905170 : Nat := 994499062015002495142915

theorem tailTrace_2905170 : CollatzResearch.WordTrace tailWord_2905170 prefixEnd_2905170 994499062015002495142915 := by
  unfold tailWord_2905170
  simp only [CollatzResearch.WordTrace]
  refine ⟨26490063721268182094878241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70640169923381818919675309 26490063721268182094878241)
  ·
    refine ⟨19867547790951136571158681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26490063721268182094878241 19867547790951136571158681)
    ·
      refine ⟨14900660843213352428369011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19867547790951136571158681 14900660843213352428369011)
      ·
        refine ⟨22350991264820028642553517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14900660843213352428369011 22350991264820028642553517)
        ·
          refine ⟨8381621724307510740957569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22350991264820028642553517 8381621724307510740957569)
          ·
            refine ⟨6286216293230633055718177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8381621724307510740957569 6286216293230633055718177)
            ·
              refine ⟨4714662219922974791788633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6286216293230633055718177 4714662219922974791788633)
              ·
                refine ⟨3535996664942231093841475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4714662219922974791788633 3535996664942231093841475)
                ·
                  refine ⟨5303994997413346640762213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3535996664942231093841475 5303994997413346640762213)
                  ·
                    refine ⟨994499062015002495142915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5303994997413346640762213 994499062015002495142915)
                    ·
                      rfl

theorem cell22_2905170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_2905170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905170 prefixEnd_2905170 := by exact prefixLift 2905170
  have htrace : WordTrace (prefixWord ++ tailWord_2905170) baseStart_2905170 baseEnd_2905170 := by
    simpa [prefixWord, tailWord_2905170, baseEnd_2905170] using wordTrace_append hprefix tailTrace_2905170
  have hstable : (prefixWord ++ tailWord_2905170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905170).length < 2 ^ (prefixWord ++ tailWord_2905170).sum := by decide
  have hdescent : baseEnd_2905170 < baseStart_2905170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905198 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_2905198 : Nat := 118140960795 + 2905198 * 2 ^ 59
def prefixEnd_2905198 : Nat := 4983230072969 + 3 ^ 40 * 2905198 * 2
def baseEnd_2905198 : Nat := 994508646987219755442829

theorem tailTrace_2905198 : CollatzResearch.WordTrace tailWord_2905198 prefixEnd_2905198 994508646987219755442829 := by
  unfold tailWord_2905198
  simp only [CollatzResearch.WordTrace]
  refine ⟨13245159516121411145191531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70640850752647526107688165 13245159516121411145191531)
  ·
    refine ⟨19867739274182116717787297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13245159516121411145191531 19867739274182116717787297)
    ·
      refine ⟨14900804455636587538340473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19867739274182116717787297 14900804455636587538340473)
      ·
        refine ⟨11175603341727440653755355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14900804455636587538340473 11175603341727440653755355)
        ·
          refine ⟨16763405012591160980633033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11175603341727440653755355 16763405012591160980633033)
          ·
            refine ⟨12572553759443370735474775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16763405012591160980633033 12572553759443370735474775)
            ·
              refine ⟨18858830639165056103212163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12572553759443370735474775 18858830639165056103212163)
              ·
                refine ⟨28288245958747584154818245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18858830639165056103212163 28288245958747584154818245)
                ·
                  refine ⟨5304046117265172029028421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28288245958747584154818245 5304046117265172029028421)
                  ·
                    refine ⟨994508646987219755442829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5304046117265172029028421 994508646987219755442829)
                    ·
                      rfl

theorem cell22_2905198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_2905198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905198 prefixEnd_2905198 := by exact prefixLift 2905198
  have htrace : WordTrace (prefixWord ++ tailWord_2905198) baseStart_2905198 baseEnd_2905198 := by
    simpa [prefixWord, tailWord_2905198, baseEnd_2905198] using wordTrace_append hprefix tailTrace_2905198
  have hstable : (prefixWord ++ tailWord_2905198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905198).length < 2 ^ (prefixWord ++ tailWord_2905198).sum := by decide
  have hdescent : baseEnd_2905198 < baseStart_2905198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905217 : List Nat := [1, 2, 4, 2, 2, 1, 4, 1, 2, 3]
def baseStart_2905217 : Nat := 118140960795 + 2905217 * 2 ^ 59
def prefixEnd_2905217 : Nat := 4983230072969 + 3 ^ 40 * 2905217 * 2
def baseEnd_2905217 : Nat := 994515151075510039217771

theorem tailTrace_2905217 : CollatzResearch.WordTrace tailWord_2905217 prefixEnd_2905217 994515151075510039217771 := by
  unfold tailWord_2905217
  simp only [CollatzResearch.WordTrace]
  refine ⟨105961969115902455406473905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70641312743934970270982603 105961969115902455406473905)
  ·
    refine ⟨79471476836926841554855429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105961969115902455406473905 79471476836926841554855429)
    ·
      refine ⟨14900901906923782791535393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79471476836926841554855429 14900901906923782791535393)
      ·
        refine ⟨11175676430192837093651545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14900901906923782791535393 11175676430192837093651545)
        ·
          refine ⟨8381757322644627820238659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11175676430192837093651545 8381757322644627820238659)
          ·
            refine ⟨12572635983966941730357989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8381757322644627820238659 12572635983966941730357989)
            ·
              refine ⟨2357369246993801574442123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12572635983966941730357989 2357369246993801574442123)
              ·
                refine ⟨3536053870490702361663185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357369246993801574442123 3536053870490702361663185)
                ·
                  refine ⟨2652040402868026771247389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3536053870490702361663185 2652040402868026771247389)
                  ·
                    refine ⟨994515151075510039217771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652040402868026771247389 994515151075510039217771)
                    ·
                      rfl

theorem cell22_2905217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_2905217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905217 prefixEnd_2905217 := by exact prefixLift 2905217
  have htrace : WordTrace (prefixWord ++ tailWord_2905217) baseStart_2905217 baseEnd_2905217 := by
    simpa [prefixWord, tailWord_2905217, baseEnd_2905217] using wordTrace_append hprefix tailTrace_2905217
  have hstable : (prefixWord ++ tailWord_2905217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905217).length < 2 ^ (prefixWord ++ tailWord_2905217).sum := by decide
  have hdescent : baseEnd_2905217 < baseStart_2905217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905228 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 3, 3]
def baseStart_2905228 : Nat := 118140960795 + 2905228 * 2 ^ 59
def prefixEnd_2905228 : Nat := 4983230072969 + 3 ^ 40 * 2905228 * 2
def baseEnd_2905228 : Nat := 994518916600309677192737

theorem tailTrace_2905228 : CollatzResearch.WordTrace tailWord_2905228 prefixEnd_2905228 994518916600309677192737 := by
  unfold tailWord_2905228
  simp only [CollatzResearch.WordTrace]
  refine ⟨52981185159431302142562169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70641580212575069523416225 52981185159431302142562169)
  ·
    refine ⟨39735888869573476606921627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52981185159431302142562169 39735888869573476606921627)
    ·
      refine ⟨59603833304360214910382441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39735888869573476606921627 59603833304360214910382441)
      ·
        refine ⟨44702874978270161182786831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59603833304360214910382441 44702874978270161182786831)
        ·
          refine ⟨67054312467405241774180247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44702874978270161182786831 67054312467405241774180247)
          ·
            refine ⟨100581468701107862661270371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67054312467405241774180247 100581468701107862661270371)
            ·
              refine ⟨150872203051661793991905557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100581468701107862661270371 150872203051661793991905557)
              ·
                refine ⟨7072134518046646593370573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150872203051661793991905557 7072134518046646593370573)
                ·
                  refine ⟨2652050444267492472513965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7072134518046646593370573 2652050444267492472513965)
                  ·
                    refine ⟨994518916600309677192737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652050444267492472513965 994518916600309677192737)
                    ·
                      rfl

theorem cell22_2905228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_2905228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905228 prefixEnd_2905228 := by exact prefixLift 2905228
  have htrace : WordTrace (prefixWord ++ tailWord_2905228) baseStart_2905228 baseEnd_2905228 := by
    simpa [prefixWord, tailWord_2905228, baseEnd_2905228] using wordTrace_append hprefix tailTrace_2905228
  have hstable : (prefixWord ++ tailWord_2905228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905228).length < 2 ^ (prefixWord ++ tailWord_2905228).sum := by decide
  have hdescent : baseEnd_2905228 < baseStart_2905228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905273 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 2, 5]
def baseStart_2905273 : Nat := 118140960795 + 2905273 * 2 ^ 59
def prefixEnd_2905273 : Nat := 4983230072969 + 3 ^ 40 * 2905273 * 2
def baseEnd_2905273 : Nat := 994534321019944559817599

theorem tailTrace_2905273 : CollatzResearch.WordTrace tailWord_2905273 prefixEnd_2905273 994534321019944559817599 := by
  unfold tailWord_2905273
  simp only [CollatzResearch.WordTrace]
  refine ⟨105964011603699576970512473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70642674402466384647008315 105964011603699576970512473)
  ·
    refine ⟨79473008702774682727884355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105964011603699576970512473 79473008702774682727884355)
    ·
      refine ⟨119209513054162024091826533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79473008702774682727884355 119209513054162024091826533)
      ·
        refine ⟨22351783697655379517217475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119209513054162024091826533 22351783697655379517217475)
        ·
          refine ⟨33527675546483069275826213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22351783697655379517217475 33527675546483069275826213)
          ·
            refine ⟨6286439164965575489217415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33527675546483069275826213 6286439164965575489217415)
            ·
              refine ⟨9429658747448363233826123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6286439164965575489217415 9429658747448363233826123)
              ·
                refine ⟨14144488121172544850739185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9429658747448363233826123 14144488121172544850739185)
                ·
                  refine ⟨10608366090879408638054389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14144488121172544850739185 10608366090879408638054389)
                  ·
                    refine ⟨994534321019944559817599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10608366090879408638054389 994534321019944559817599)
                    ·
                      rfl

theorem cell22_2905273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_2905273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905273 prefixEnd_2905273 := by exact prefixLift 2905273
  have htrace : WordTrace (prefixWord ++ tailWord_2905273) baseStart_2905273 baseEnd_2905273 := by
    simpa [prefixWord, tailWord_2905273, baseEnd_2905273] using wordTrace_append hprefix tailTrace_2905273
  have hstable : (prefixWord ++ tailWord_2905273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905273).length < 2 ^ (prefixWord ++ tailWord_2905273).sum := by decide
  have hdescent : baseEnd_2905273 < baseStart_2905273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905288 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 3, 4]
def baseStart_2905288 : Nat := 118140960795 + 2905288 * 2 ^ 59
def prefixEnd_2905288 : Nat := 4983230072969 + 3 ^ 40 * 2905288 * 2
def baseEnd_2905288 : Nat := 994539455826489520692553

theorem tailTrace_2905288 : CollatzResearch.WordTrace tailWord_2905288 prefixEnd_2905288 994539455826489520692553 := by
  unfold tailWord_2905288
  simp only [CollatzResearch.WordTrace]
  refine ⟨52982279349322617266154259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70643039132430156354872345 52982279349322617266154259)
  ·
    refine ⟨79473419023983925899231389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52982279349322617266154259 79473419023983925899231389)
    ·
      refine ⟨29802532133993972212211771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79473419023983925899231389 29802532133993972212211771)
      ·
        refine ⟨44703798200990958318317657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29802532133993972212211771 44703798200990958318317657)
        ·
          refine ⟨33527848650743218738738243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44703798200990958318317657 33527848650743218738738243)
          ·
            refine ⟨50291772976114828108107365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33527848650743218738738243 50291772976114828108107365)
            ·
              refine ⟨9429707433021530270270131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50291772976114828108107365 9429707433021530270270131)
              ·
                refine ⟨14144561149532295405405197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9429707433021530270270131 14144561149532295405405197)
                ·
                  refine ⟨5304210431074610777026949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14144561149532295405405197 5304210431074610777026949)
                  ·
                    refine ⟨994539455826489520692553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5304210431074610777026949 994539455826489520692553)
                    ·
                      rfl

theorem cell22_2905288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_2905288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905288 prefixEnd_2905288 := by exact prefixLift 2905288
  have htrace : WordTrace (prefixWord ++ tailWord_2905288) baseStart_2905288 baseEnd_2905288 := by
    simpa [prefixWord, tailWord_2905288, baseEnd_2905288] using wordTrace_append hprefix tailTrace_2905288
  have hstable : (prefixWord ++ tailWord_2905288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905288).length < 2 ^ (prefixWord ++ tailWord_2905288).sum := by decide
  have hdescent : baseEnd_2905288 < baseStart_2905288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905309 : List Nat := [1, 4, 3, 2, 3, 1, 1, 2, 5]
def baseStart_2905309 : Nat := 118140960795 + 2905309 * 2 ^ 59
def prefixEnd_2905309 : Nat := 4983230072969 + 3 ^ 40 * 2905309 * 2
def baseEnd_2905309 : Nat := 331515548185217488639163

theorem tailTrace_2905309 : CollatzResearch.WordTrace tailWord_2905309 prefixEnd_2905309 331515548185217488639163 := by
  unfold tailWord_2905309
  simp only [CollatzResearch.WordTrace]
  refine ⟨105965324631569155118822981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70643549754379436745881987 105965324631569155118822981)
  ·
    refine ⟨19868498368419216584779309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105965324631569155118822981 19868498368419216584779309)
    ·
      refine ⟨7450686888157206219292241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19868498368419216584779309 7450686888157206219292241)
      ·
        refine ⟨5588015166117904664469181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7450686888157206219292241 5588015166117904664469181)
        ·
          refine ⟨2095505687294214249175943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5588015166117904664469181 2095505687294214249175943)
          ·
            refine ⟨3143258530941321373763915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095505687294214249175943 3143258530941321373763915)
            ·
              refine ⟨4714887796411982060645873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3143258530941321373763915 4714887796411982060645873)
              ·
                refine ⟨3536165847308986545484405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4714887796411982060645873 3536165847308986545484405)
                ·
                  refine ⟨331515548185217488639163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3536165847308986545484405 331515548185217488639163)
                  ·
                    rfl

theorem cell22_2905309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_2905309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905309 prefixEnd_2905309 := by exact prefixLift 2905309
  have htrace : WordTrace (prefixWord ++ tailWord_2905309) baseStart_2905309 baseEnd_2905309 := by
    simpa [prefixWord, tailWord_2905309, baseEnd_2905309] using wordTrace_append hprefix tailTrace_2905309
  have hstable : (prefixWord ++ tailWord_2905309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905309).length < 2 ^ (prefixWord ++ tailWord_2905309).sum := by decide
  have hdescent : baseEnd_2905309 < baseStart_2905309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905320 : List Nat := [2, 1, 4, 1, 2, 1, 1, 6, 4]
def baseStart_2905320 : Nat := 118140960795 + 2905320 * 2 ^ 59
def prefixEnd_2905320 : Nat := 4983230072969 + 3 ^ 40 * 2905320 * 2
def baseEnd_2905320 : Nat := 331516803360150701297485

theorem tailTrace_2905320 : CollatzResearch.WordTrace tailWord_2905320 prefixEnd_2905320 331516803360150701297485 := by
  unfold tailWord_2905320
  simp only [CollatzResearch.WordTrace]
  refine ⟨52982862917264651998736707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70643817223019535998315609 52982862917264651998736707)
  ·
    refine ⟨79474294375896977998105061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52982862917264651998736707 79474294375896977998105061)
    ·
      refine ⟨14901430195480683374644699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79474294375896977998105061 14901430195480683374644699)
      ·
        refine ⟨22352145293221025061967049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14901430195480683374644699 22352145293221025061967049)
        ·
          refine ⟨16764108969915768796475287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22352145293221025061967049 16764108969915768796475287)
          ·
            refine ⟨25146163454873653194712931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16764108969915768796475287 25146163454873653194712931)
            ·
              refine ⟨37719245182310479792069397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25146163454873653194712931 37719245182310479792069397)
              ·
                refine ⟨1768089617920803740253253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37719245182310479792069397 1768089617920803740253253)
                ·
                  refine ⟨331516803360150701297485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1768089617920803740253253 331516803360150701297485)
                  ·
                    rfl

theorem cell22_2905320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 4].length) (baseStart_2905320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905320 prefixEnd_2905320 := by exact prefixLift 2905320
  have htrace : WordTrace (prefixWord ++ tailWord_2905320) baseStart_2905320 baseEnd_2905320 := by
    simpa [prefixWord, tailWord_2905320, baseEnd_2905320] using wordTrace_append hprefix tailTrace_2905320
  have hstable : (prefixWord ++ tailWord_2905320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905320).length < 2 ^ (prefixWord ++ tailWord_2905320).sum := by decide
  have hdescent : baseEnd_2905320 < baseStart_2905320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905386 : List Nat := [3, 1, 4, 2, 1, 3, 2, 1, 2, 3]
def baseStart_2905386 : Nat := 118140960795 + 2905386 * 2 ^ 59
def prefixEnd_2905386 : Nat := 4983230072969 + 3 ^ 40 * 2905386 * 2
def baseEnd_2905386 : Nat := 994573003229249931742253

theorem tailTrace_2905386 : CollatzResearch.WordTrace tailWord_2905386 prefixEnd_2905386 994573003229249931742253 := by
  unfold tailWord_2905386
  simp only [CollatzResearch.WordTrace]
  refine ⟨26492033263072549317344003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70645422034860131512917341 26492033263072549317344003)
  ·
    refine ⟨39738049894608823976016005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26492033263072549317344003 39738049894608823976016005)
    ·
      refine ⟨7450884355239154495503001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39738049894608823976016005 7450884355239154495503001)
      ·
        refine ⟨5588163266429365871627251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7450884355239154495503001 5588163266429365871627251)
        ·
          refine ⟨8382244899644048807440877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5588163266429365871627251 8382244899644048807440877)
          ·
            refine ⟨3143341837366518302790329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8382244899644048807440877 3143341837366518302790329)
            ·
              refine ⟨2357506378024888727092747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3143341837366518302790329 2357506378024888727092747)
              ·
                refine ⟨3536259567037333090639121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357506378024888727092747 3536259567037333090639121)
                ·
                  refine ⟨2652194675277999817979341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3536259567037333090639121 2652194675277999817979341)
                  ·
                    refine ⟨994573003229249931742253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652194675277999817979341 994573003229249931742253)
                    ·
                      rfl

theorem cell22_2905386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_2905386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905386 prefixEnd_2905386 := by exact prefixLift 2905386
  have htrace : WordTrace (prefixWord ++ tailWord_2905386) baseStart_2905386 baseEnd_2905386 := by
    simpa [prefixWord, tailWord_2905386, baseEnd_2905386] using wordTrace_append hprefix tailTrace_2905386
  have hstable : (prefixWord ++ tailWord_2905386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905386).length < 2 ^ (prefixWord ++ tailWord_2905386).sum := by decide
  have hdescent : baseEnd_2905386 < baseStart_2905386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905431 : List Nat := [1, 1, 3, 2, 3, 4, 2, 2, 1, 3]
def baseStart_2905431 : Nat := 118140960795 + 2905431 * 2 ^ 59
def prefixEnd_2905431 : Nat := 4983230072969 + 3 ^ 40 * 2905431 * 2
def baseEnd_2905431 : Nat := 994588407648884814367115

theorem tailTrace_2905431 : CollatzResearch.WordTrace tailWord_2905431 prefixEnd_2905431 994588407648884814367115 := by
  unfold tailWord_2905431
  simp only [CollatzResearch.WordTrace]
  refine ⟨105969774337127169954764147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70646516224751446636509431 105969774337127169954764147)
  ·
    refine ⟨158954661505690754932146221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105969774337127169954764147 158954661505690754932146221)
    ·
      refine ⟨59607998064634033099554833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158954661505690754932146221 59607998064634033099554833)
      ·
        refine ⟨44705998548475524824666125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59607998064634033099554833 44705998548475524824666125)
        ·
          refine ⟨16764749455678321809249797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44705998548475524824666125 16764749455678321809249797)
          ·
            refine ⟨3143390522939685339234337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16764749455678321809249797 3143390522939685339234337)
            ·
              refine ⟨2357542892204764004425753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3143390522939685339234337 2357542892204764004425753)
              ·
                refine ⟨1768157169153573003319315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2357542892204764004425753 1768157169153573003319315)
                ·
                  refine ⟨2652235753730359504978973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768157169153573003319315 2652235753730359504978973)
                  ·
                    refine ⟨994588407648884814367115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652235753730359504978973 994588407648884814367115)
                    ·
                      rfl

theorem cell22_2905431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_2905431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905431 prefixEnd_2905431 := by exact prefixLift 2905431
  have htrace : WordTrace (prefixWord ++ tailWord_2905431) baseStart_2905431 baseEnd_2905431 := by
    simpa [prefixWord, tailWord_2905431, baseEnd_2905431] using wordTrace_append hprefix tailTrace_2905431
  have hstable : (prefixWord ++ tailWord_2905431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905431).length < 2 ^ (prefixWord ++ tailWord_2905431).sum := by decide
  have hdescent : baseEnd_2905431 < baseStart_2905431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905440 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 3, 4]
def baseStart_2905440 : Nat := 118140960795 + 2905440 * 2 ^ 59
def prefixEnd_2905440 : Nat := 4983230072969 + 3 ^ 40 * 2905440 * 2
def baseEnd_2905440 : Nat := 994591488532811790892087

theorem tailTrace_2905440 : CollatzResearch.WordTrace tailWord_2905440 prefixEnd_2905440 994591488532811790892087 := by
  unfold tailWord_2905440
  simp only [CollatzResearch.WordTrace]
  refine ⟨52985051297047282245920887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70646735062729709661227849 52985051297047282245920887)
  ·
    refine ⟨79477576945570923368881331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52985051297047282245920887 79477576945570923368881331)
    ·
      refine ⟨119216365418356385053321997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79477576945570923368881331 119216365418356385053321997)
      ·
        refine ⟨44706137031883644394995749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119216365418356385053321997 44706137031883644394995749)
        ·
          refine ⟨8382400693478183324061703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44706137031883644394995749 8382400693478183324061703)
          ·
            refine ⟨12573601040217274986092555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8382400693478183324061703 12573601040217274986092555)
            ·
              refine ⟨18860401560325912479138833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12573601040217274986092555 18860401560325912479138833)
              ·
                refine ⟨14145301170244434359354125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18860401560325912479138833 14145301170244434359354125)
                ·
                  refine ⟨5304487938841662884757797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14145301170244434359354125 5304487938841662884757797)
                  ·
                    refine ⟨994591488532811790892087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5304487938841662884757797 994591488532811790892087)
                    ·
                      rfl

theorem cell22_2905440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_2905440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905440 prefixEnd_2905440 := by exact prefixLift 2905440
  have htrace : WordTrace (prefixWord ++ tailWord_2905440) baseStart_2905440 baseEnd_2905440 := by
    simpa [prefixWord, tailWord_2905440, baseEnd_2905440] using wordTrace_append hprefix tailTrace_2905440
  have hstable : (prefixWord ++ tailWord_2905440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905440).length < 2 ^ (prefixWord ++ tailWord_2905440).sum := by decide
  have hdescent : baseEnd_2905440 < baseStart_2905440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905483 : List Nat := [1, 1, 1, 1, 4, 3, 11]
def baseStart_2905483 : Nat := 118140960795 + 2905483 * 2 ^ 59
def prefixEnd_2905483 : Nat := 4983230072969 + 3 ^ 40 * 2905483 * 2
def baseEnd_2905483 : Nat := 36837266974502741187665

theorem tailTrace_2905483 : CollatzResearch.WordTrace tailWord_2905483 prefixEnd_2905483 36837266974502741187665 := by
  unfold tailWord_2905483
  simp only [CollatzResearch.WordTrace]
  refine ⟨105971670932938782835657103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70647780621959188557104735 105971670932938782835657103)
  ·
    refine ⟨158957506399408174253485655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105971670932938782835657103 158957506399408174253485655)
    ·
      refine ⟨238436259599112261380228483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158957506399408174253485655 238436259599112261380228483)
      ·
        refine ⟨357654389398668392070342725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238436259599112261380228483 357654389398668392070342725)
        ·
          refine ⟨67060198012250323513189261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357654389398668392070342725 67060198012250323513189261)
          ·
            refine ⟨25147574254593871317445973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67060198012250323513189261 25147574254593871317445973)
            ·
              refine ⟨36837266974502741187665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25147574254593871317445973 36837266974502741187665)
              ·
                rfl

theorem cell22_2905483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 11].length) (baseStart_2905483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905483 prefixEnd_2905483 := by exact prefixLift 2905483
  have htrace : WordTrace (prefixWord ++ tailWord_2905483) baseStart_2905483 baseEnd_2905483 := by
    simpa [prefixWord, tailWord_2905483, baseEnd_2905483] using wordTrace_append hprefix tailTrace_2905483
  have hstable : (prefixWord ++ tailWord_2905483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905483).length < 2 ^ (prefixWord ++ tailWord_2905483).sum := by decide
  have hdescent : baseEnd_2905483 < baseStart_2905483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905504 : List Nat := [2, 1, 1, 4, 1, 2, 5, 1, 2, 3]
def baseStart_2905504 : Nat := 118140960795 + 2905504 * 2 ^ 59
def prefixEnd_2905504 : Nat := 4983230072969 + 3 ^ 40 * 2905504 * 2
def baseEnd_2905504 : Nat := 994613397040736957291891

theorem tailTrace_2905504 : CollatzResearch.WordTrace tailWord_2905504 prefixEnd_2905504 994613397040736957291891 := by
  unfold tailWord_2905504
  simp only [CollatzResearch.WordTrace]
  refine ⟨52986218432931351711085783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70648291243908468948114377 52986218432931351711085783)
  ·
    refine ⟨79479327649397027566628675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52986218432931351711085783 79479327649397027566628675)
    ·
      refine ⟨119218991474095541349943013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79479327649397027566628675 119218991474095541349943013)
      ·
        refine ⟨22353560901392914003114315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119218991474095541349943013 22353560901392914003114315)
        ·
          refine ⟨33530341352089371004671473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22353560901392914003114315 33530341352089371004671473)
          ·
            refine ⟨25147756014067028253503605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33530341352089371004671473 25147756014067028253503605)
            ·
              refine ⟨2357602126318783898765963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25147756014067028253503605 2357602126318783898765963)
              ·
                refine ⟨3536403189478175848148945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357602126318783898765963 3536403189478175848148945)
                ·
                  refine ⟨2652302392108631886111709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3536403189478175848148945 2652302392108631886111709)
                  ·
                    refine ⟨994613397040736957291891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652302392108631886111709 994613397040736957291891)
                    ·
                      rfl

theorem cell22_2905504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 2, 3].length) (baseStart_2905504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905504 prefixEnd_2905504 := by exact prefixLift 2905504
  have htrace : WordTrace (prefixWord ++ tailWord_2905504) baseStart_2905504 baseEnd_2905504 := by
    simpa [prefixWord, tailWord_2905504, baseEnd_2905504] using wordTrace_append hprefix tailTrace_2905504
  have hstable : (prefixWord ++ tailWord_2905504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905504).length < 2 ^ (prefixWord ++ tailWord_2905504).sum := by decide
  have hdescent : baseEnd_2905504 < baseStart_2905504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905515 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 9, 3]
def baseStart_2905515 : Nat := 118140960795 + 2905515 * 2 ^ 59
def prefixEnd_2905515 : Nat := 4983230072969 + 3 ^ 40 * 2905515 * 2
def baseEnd_2905515 : Nat := 994617162565536595266857

theorem tailTrace_2905515 : CollatzResearch.WordTrace tailWord_2905515 prefixEnd_2905515 994617162565536595266857 := by
  unfold tailWord_2905515
  simp only [CollatzResearch.WordTrace]
  refine ⟨105972838068822852300821999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70648558712548568200547999 105972838068822852300821999)
  ·
    refine ⟨158959257103234278451232999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105972838068822852300821999 158959257103234278451232999)
    ·
      refine ⟨238438885654851417676849499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158959257103234278451232999 238438885654851417676849499)
      ·
        refine ⟨357658328482277126515274249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238438885654851417676849499 357658328482277126515274249)
        ·
          refine ⟨268243746361707844886455687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357658328482277126515274249 268243746361707844886455687)
          ·
            refine ⟨402365619542561767329683531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268243746361707844886455687 402365619542561767329683531)
            ·
              refine ⟨603548429313842650994525297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402365619542561767329683531 603548429313842650994525297)
              ·
                refine ⟨452661321985381988245893973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603548429313842650994525297 452661321985381988245893973)
                ·
                  refine ⟨2652312433508097587378285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 452661321985381988245893973 2652312433508097587378285)
                  ·
                    refine ⟨994617162565536595266857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652312433508097587378285 994617162565536595266857)
                    ·
                      rfl

theorem cell22_2905515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 3].length) (baseStart_2905515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905515 prefixEnd_2905515 := by exact prefixLift 2905515
  have htrace : WordTrace (prefixWord ++ tailWord_2905515) baseStart_2905515 baseEnd_2905515 := by
    simpa [prefixWord, tailWord_2905515, baseEnd_2905515] using wordTrace_append hprefix tailTrace_2905515
  have hstable : (prefixWord ++ tailWord_2905515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905515).length < 2 ^ (prefixWord ++ tailWord_2905515).sum := by decide
  have hdescent : baseEnd_2905515 < baseStart_2905515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905517 : List Nat := [1, 5, 2, 2, 1, 2, 1, 8]
def baseStart_2905517 : Nat := 118140960795 + 2905517 * 2 ^ 59
def prefixEnd_2905517 : Nat := 4983230072969 + 3 ^ 40 * 2905517 * 2
def baseEnd_2905517 : Nat := 110513094134045472968539

theorem tailTrace_2905517 : CollatzResearch.WordTrace tailWord_2905517 prefixEnd_2905517 110513094134045472968539 := by
  unfold tailWord_2905517
  simp only [CollatzResearch.WordTrace]
  refine ⟨105972911014815606642394805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70648607343210404428263203 105972911014815606642394805)
  ·
    refine ⟨9934960407638963122724513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105972911014815606642394805 9934960407638963122724513)
    ·
      refine ⟨7451220305729222342043385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9934960407638963122724513 7451220305729222342043385)
      ·
        refine ⟨5588415229296916756532539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7451220305729222342043385 5588415229296916756532539)
        ·
          refine ⟨8382622843945375134798809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5588415229296916756532539 8382622843945375134798809)
          ·
            refine ⟨6286967132959031351099107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8382622843945375134798809 6286967132959031351099107)
            ·
              refine ⟨9430450699438547026648661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6286967132959031351099107 9430450699438547026648661)
              ·
                refine ⟨110513094134045472968539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9430450699438547026648661 110513094134045472968539)
                ·
                  rfl

theorem cell22_2905517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 8].length) (baseStart_2905517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905517 prefixEnd_2905517 := by exact prefixLift 2905517
  have htrace : WordTrace (prefixWord ++ tailWord_2905517) baseStart_2905517 baseEnd_2905517 := by
    simpa [prefixWord, tailWord_2905517, baseEnd_2905517] using wordTrace_append hprefix tailTrace_2905517
  have hstable : (prefixWord ++ tailWord_2905517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905517).length < 2 ^ (prefixWord ++ tailWord_2905517).sum := by decide
  have hdescent : baseEnd_2905517 < baseStart_2905517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905545 : List Nat := [1, 2, 1, 1, 2, 1, 3, 6, 5]
def baseStart_2905545 : Nat := 118140960795 + 2905545 * 2 ^ 59
def prefixEnd_2905545 : Nat := 4983230072969 + 3 ^ 40 * 2905545 * 2
def baseEnd_2905545 : Nat := 331542477392875505672255

theorem tailTrace_2905545 : CollatzResearch.WordTrace tailWord_2905545 prefixEnd_2905545 331542477392875505672255 := by
  unfold tailWord_2905545
  simp only [CollatzResearch.WordTrace]
  refine ⟨105973932258714167424414089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70649288172476111616276059 105973932258714167424414089)
  ·
    refine ⟨79480449194035625568310567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105973932258714167424414089 79480449194035625568310567)
    ·
      refine ⟨119220673791053438352465851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79480449194035625568310567 119220673791053438352465851)
      ·
        refine ⟨178831010686580157528698777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119220673791053438352465851 178831010686580157528698777)
        ·
          refine ⟨134123258014935118146524083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178831010686580157528698777 134123258014935118146524083)
          ·
            refine ⟨201184887022402677219786125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134123258014935118146524083 201184887022402677219786125)
            ·
              refine ⟨75444332633401003957419797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201184887022402677219786125 75444332633401003957419797)
              ·
                refine ⟨3536453092190672060504053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75444332633401003957419797 3536453092190672060504053)
                ·
                  refine ⟨331542477392875505672255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3536453092190672060504053 331542477392875505672255)
                  ·
                    rfl

theorem cell22_2905545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 5].length) (baseStart_2905545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905545 prefixEnd_2905545 := by exact prefixLift 2905545
  have htrace : WordTrace (prefixWord ++ tailWord_2905545) baseStart_2905545 baseEnd_2905545 := by
    simpa [prefixWord, tailWord_2905545, baseEnd_2905545] using wordTrace_append hprefix tailTrace_2905545
  have hstable : (prefixWord ++ tailWord_2905545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905545).length < 2 ^ (prefixWord ++ tailWord_2905545).sum := by decide
  have hdescent : baseEnd_2905545 < baseStart_2905545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905560 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 2, 5]
def baseStart_2905560 : Nat := 118140960795 + 2905560 * 2 ^ 59
def prefixEnd_2905560 : Nat := 4983230072969 + 3 ^ 40 * 2905560 * 2
def baseEnd_2905560 : Nat := 994632566985171477891719

theorem tailTrace_2905560 : CollatzResearch.WordTrace tailWord_2905560 prefixEnd_2905560 994632566985171477891719 := by
  unfold tailWord_2905560
  simp only [CollatzResearch.WordTrace]
  refine ⟨52987239676829912493105067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70649652902439883324140089 52987239676829912493105067)
  ·
    refine ⟨79480859515244868739657601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52987239676829912493105067 79480859515244868739657601)
    ·
      refine ⟨59610644636433651554743201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79480859515244868739657601 59610644636433651554743201)
      ·
        refine ⟨44707983477325238666057401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59610644636433651554743201 44707983477325238666057401)
        ·
          refine ⟨33530987607993928999543051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44707983477325238666057401 33530987607993928999543051)
          ·
            refine ⟨50296481411990893499314577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33530987607993928999543051 50296481411990893499314577)
            ·
              refine ⟨37722361058993170124485933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50296481411990893499314577 37722361058993170124485933)
              ·
                refine ⟨14145885397122438796682225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37722361058993170124485933 14145885397122438796682225)
                ·
                  refine ⟨10609414047841829097511669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14145885397122438796682225 10609414047841829097511669)
                  ·
                    refine ⟨994632566985171477891719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10609414047841829097511669 994632566985171477891719)
                    ·
                      rfl

theorem cell22_2905560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_2905560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905560 prefixEnd_2905560 := by exact prefixLift 2905560
  have htrace : WordTrace (prefixWord ++ tailWord_2905560) baseStart_2905560 baseEnd_2905560 := by
    simpa [prefixWord, tailWord_2905560, baseEnd_2905560] using wordTrace_append hprefix tailTrace_2905560
  have hstable : (prefixWord ++ tailWord_2905560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905560).length < 2 ^ (prefixWord ++ tailWord_2905560).sum := by decide
  have hdescent : baseEnd_2905560 < baseStart_2905560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905562 : List Nat := [3, 1, 1, 2, 3, 3, 1, 3, 5]
def baseStart_2905562 : Nat := 118140960795 + 2905562 * 2 ^ 59
def prefixEnd_2905562 : Nat := 4983230072969 + 3 ^ 40 * 2905562 * 2
def baseEnd_2905562 : Nat := 331544417208681379780571

theorem tailTrace_2905562 : CollatzResearch.WordTrace tailWord_2905562 prefixEnd_2905562 331544417208681379780571 := by
  unfold tailWord_2905562
  simp only [CollatzResearch.WordTrace]
  refine ⟨26493638074913144831945735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70649701533101719551855293 26493638074913144831945735)
  ·
    refine ⟨39740457112369717247918603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26493638074913144831945735 39740457112369717247918603)
    ·
      refine ⟨59610685668554575871877905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39740457112369717247918603 59610685668554575871877905)
      ·
        refine ⟨44708014251415931903908429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59610685668554575871877905 44708014251415931903908429)
        ·
          refine ⟨16765505344280974463965661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44708014251415931903908429 16765505344280974463965661)
          ·
            refine ⟨6287064504105365423987123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16765505344280974463965661 6287064504105365423987123)
            ·
              refine ⟨9430596756158048135980685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6287064504105365423987123 9430596756158048135980685)
              ·
                refine ⟨3536473783559268050992757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9430596756158048135980685 3536473783559268050992757)
                ·
                  refine ⟨331544417208681379780571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3536473783559268050992757 331544417208681379780571)
                  ·
                    rfl

theorem cell22_2905562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_2905562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905562 prefixEnd_2905562 := by exact prefixLift 2905562
  have htrace : WordTrace (prefixWord ++ tailWord_2905562) baseStart_2905562 baseEnd_2905562 := by
    simpa [prefixWord, tailWord_2905562, baseEnd_2905562] using wordTrace_append hprefix tailTrace_2905562
  have hstable : (prefixWord ++ tailWord_2905562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905562).length < 2 ^ (prefixWord ++ tailWord_2905562).sum := by decide
  have hdescent : baseEnd_2905562 < baseStart_2905562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905605 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_2905605 : Nat := 118140960795 + 2905605 * 2 ^ 59
def prefixEnd_2905605 : Nat := 4983230072969 + 3 ^ 40 * 2905605 * 2
def baseEnd_2905605 : Nat := 994647971404806360516581

theorem tailTrace_2905605 : CollatzResearch.WordTrace tailWord_2905605 prefixEnd_2905605 994647971404806360516581 := by
  unfold tailWord_2905605
  simp only [CollatzResearch.WordTrace]
  refine ⟨105976120638496797671598269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70650747092331198447732179 105976120638496797671598269)
  ·
    refine ⟨39741045239436299126849351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105976120638496797671598269 39741045239436299126849351)
    ·
      refine ⟨59611567859154448690274027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39741045239436299126849351 59611567859154448690274027)
      ·
        refine ⟨89417351788731673035411041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59611567859154448690274027 89417351788731673035411041)
        ·
          refine ⟨67063013841548754776558281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89417351788731673035411041 67063013841548754776558281)
          ·
            refine ⟨50297260381161566082418711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67063013841548754776558281 50297260381161566082418711)
            ·
              refine ⟨75445890571742349123628067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50297260381161566082418711 75445890571742349123628067)
              ·
                refine ⟨113168835857613523685442101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75445890571742349123628067 113168835857613523685442101)
                ·
                  refine ⟨10609578361651267845510197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113168835857613523685442101 10609578361651267845510197)
                  ·
                    refine ⟨994647971404806360516581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10609578361651267845510197 994647971404806360516581)
                    ·
                      rfl

theorem cell22_2905605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_2905605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905605 prefixEnd_2905605 := by exact prefixLift 2905605
  have htrace : WordTrace (prefixWord ++ tailWord_2905605) baseStart_2905605 baseEnd_2905605 := by
    simpa [prefixWord, tailWord_2905605, baseEnd_2905605] using wordTrace_append hprefix tailTrace_2905605
  have hstable : (prefixWord ++ tailWord_2905605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905605).length < 2 ^ (prefixWord ++ tailWord_2905605).sum := by decide
  have hdescent : baseEnd_2905605 < baseStart_2905605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905656 : List Nat := [2, 1, 2, 1, 4, 4, 1, 2, 2, 3]
def baseStart_2905656 : Nat := 118140960795 + 2905656 * 2 ^ 59
def prefixEnd_2905656 : Nat := 4983230072969 + 3 ^ 40 * 2905656 * 2
def baseEnd_2905656 : Nat := 994665429747059227491425

theorem tailTrace_2905656 : CollatzResearch.WordTrace tailWord_2905656 prefixEnd_2905656 994665429747059227491425 := by
  unfold tailWord_2905656
  simp only [CollatzResearch.WordTrace]
  refine ⟨52988990380656016690852411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70651987174208022254469881 52988990380656016690852411)
  ·
    refine ⟨79483485570984025036278617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52988990380656016690852411 79483485570984025036278617)
    ·
      refine ⟨59612614178238018777208963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79483485570984025036278617 59612614178238018777208963)
      ·
        refine ⟨89418921267357028165813445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59612614178238018777208963 89418921267357028165813445)
        ·
          refine ⟨16766047737629442781090021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89418921267357028165813445 16766047737629442781090021)
          ·
            refine ⟨3143633950805520521454379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16766047737629442781090021 3143633950805520521454379)
            ·
              refine ⟨4715450926208280782181569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3143633950805520521454379 4715450926208280782181569)
              ·
                refine ⟨3536588194656210586636177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4715450926208280782181569 3536588194656210586636177)
                ·
                  refine ⟨2652441145992157939977133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3536588194656210586636177 2652441145992157939977133)
                  ·
                    refine ⟨994665429747059227491425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652441145992157939977133 994665429747059227491425)
                    ·
                      rfl

theorem cell22_2905656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_2905656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905656 prefixEnd_2905656 := by exact prefixLift 2905656
  have htrace : WordTrace (prefixWord ++ tailWord_2905656) baseStart_2905656 baseEnd_2905656 := by
    simpa [prefixWord, tailWord_2905656, baseEnd_2905656] using wordTrace_append hprefix tailTrace_2905656
  have hstable : (prefixWord ++ tailWord_2905656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905656).length < 2 ^ (prefixWord ++ tailWord_2905656).sum := by decide
  have hdescent : baseEnd_2905656 < baseStart_2905656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905684 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_2905684 : Nat := 118140960795 + 2905684 * 2 ^ 59
def prefixEnd_2905684 : Nat := 4983230072969 + 3 ^ 40 * 2905684 * 2
def baseEnd_2905684 : Nat := 994675014719276487791339

theorem tailTrace_2905684 : CollatzResearch.WordTrace tailWord_2905684 prefixEnd_2905684 994675014719276487791339 := by
  unfold tailWord_2905684
  simp only [CollatzResearch.WordTrace]
  refine ⟨52989501002605297081862053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70652668003473729442482737 52989501002605297081862053)
  ·
    refine ⟨9935531437988493202849135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52989501002605297081862053 9935531437988493202849135)
    ·
      refine ⟨14903297156982739804273703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9935531437988493202849135 14903297156982739804273703)
      ·
        refine ⟨22354945735474109706410555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14903297156982739804273703 22354945735474109706410555)
        ·
          refine ⟨33532418603211164559615833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22354945735474109706410555 33532418603211164559615833)
          ·
            refine ⟨25149313952408373419711875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33532418603211164559615833 25149313952408373419711875)
            ·
              refine ⟨37723970928612560129567813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25149313952408373419711875 37723970928612560129567813)
              ·
                refine ⟨7073244549114855024293965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37723970928612560129567813 7073244549114855024293965)
                ·
                  refine ⟨2652466705918070634110237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7073244549114855024293965 2652466705918070634110237)
                  ·
                    refine ⟨994675014719276487791339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652466705918070634110237 994675014719276487791339)
                    ·
                      rfl

theorem cell22_2905684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_2905684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905684 prefixEnd_2905684 := by exact prefixLift 2905684
  have htrace : WordTrace (prefixWord ++ tailWord_2905684) baseStart_2905684 baseEnd_2905684 := by
    simpa [prefixWord, tailWord_2905684, baseEnd_2905684] using wordTrace_append hprefix tailTrace_2905684
  have hstable : (prefixWord ++ tailWord_2905684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905684).length < 2 ^ (prefixWord ++ tailWord_2905684).sum := by decide
  have hdescent : baseEnd_2905684 < baseStart_2905684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905718 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_2905718 : Nat := 118140960795 + 2905718 * 2 ^ 59
def prefixEnd_2905718 : Nat := 4983230072969 + 3 ^ 40 * 2905718 * 2
def baseEnd_2905718 : Nat := 994686653614111732441235

theorem tailTrace_2905718 : CollatzResearch.WordTrace tailWord_2905718 prefixEnd_2905718 994686653614111732441235 := by
  unfold tailWord_2905718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6623765130442963623153863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70653494724724945313641205 6623765130442963623153863)
  ·
    refine ⟨9935647695664445434730795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6623765130442963623153863 9935647695664445434730795)
    ·
      refine ⟨14903471543496668152096193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9935647695664445434730795 14903471543496668152096193)
      ·
        refine ⟨11177603657622501114072145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14903471543496668152096193 11177603657622501114072145)
        ·
          refine ⟨8383202743216875835554109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11177603657622501114072145 8383202743216875835554109)
          ·
            refine ⟨3143701028706328438332791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8383202743216875835554109 3143701028706328438332791)
            ·
              refine ⟨4715551543059492657499187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3143701028706328438332791 4715551543059492657499187)
              ·
                refine ⟨7073327314589238986248781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4715551543059492657499187 7073327314589238986248781)
                ·
                  refine ⟨2652497742970964619843293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7073327314589238986248781 2652497742970964619843293)
                  ·
                    refine ⟨994686653614111732441235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652497742970964619843293 994686653614111732441235)
                    ·
                      rfl

theorem cell22_2905718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_2905718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905718 prefixEnd_2905718 := by exact prefixLift 2905718
  have htrace : WordTrace (prefixWord ++ tailWord_2905718) baseStart_2905718 baseEnd_2905718 := by
    simpa [prefixWord, tailWord_2905718, baseEnd_2905718] using wordTrace_append hprefix tailTrace_2905718
  have hstable : (prefixWord ++ tailWord_2905718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905718).length < 2 ^ (prefixWord ++ tailWord_2905718).sum := by decide
  have hdescent : baseEnd_2905718 < baseStart_2905718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905776 : List Nat := [2, 1, 1, 1, 2, 1, 8, 2, 4]
def baseStart_2905776 : Nat := 118140960795 + 2905776 * 2 ^ 59
def prefixEnd_2905776 : Nat := 4983230072969 + 3 ^ 40 * 2905776 * 2
def baseEnd_2905776 : Nat := 331568836066472971497019

theorem tailTrace_2905776 : CollatzResearch.WordTrace tailWord_2905776 prefixEnd_2905776 331568836066472971497019 := by
  unfold tailWord_2905776
  simp only [CollatzResearch.WordTrace]
  refine ⟨52991178760438646938036591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70654905013918195917382121 52991178760438646938036591)
  ·
    refine ⟨79486768140657970407054887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52991178760438646938036591 79486768140657970407054887)
    ·
      refine ⟨119230152210986955610582331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79486768140657970407054887 119230152210986955610582331)
      ·
        refine ⟨178845228316480433415873497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119230152210986955610582331 178845228316480433415873497)
        ·
          refine ⟨134133921237360325061905123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178845228316480433415873497 134133921237360325061905123)
          ·
            refine ⟨201200881856040487592857685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134133921237360325061905123 201200881856040487592857685)
            ·
              refine ⟨2357822834250474463978801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 201200881856040487592857685 2357822834250474463978801)
              ·
                refine ⟨1768367125687855847984101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2357822834250474463978801 1768367125687855847984101)
                ·
                  refine ⟨331568836066472971497019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1768367125687855847984101 331568836066472971497019)
                  ·
                    rfl

theorem cell22_2905776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 4].length) (baseStart_2905776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905776 prefixEnd_2905776 := by exact prefixLift 2905776
  have htrace : WordTrace (prefixWord ++ tailWord_2905776) baseStart_2905776 baseEnd_2905776 := by
    simpa [prefixWord, tailWord_2905776, baseEnd_2905776] using wordTrace_append hprefix tailTrace_2905776
  have hstable : (prefixWord ++ tailWord_2905776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905776).length < 2 ^ (prefixWord ++ tailWord_2905776).sum := by decide
  have hdescent : baseEnd_2905776 < baseStart_2905776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905821 : List Nat := [1, 4, 3, 3, 1, 1, 9]
def baseStart_2905821 : Nat := 118140960795 + 2905821 * 2 ^ 59
def prefixEnd_2905821 : Nat := 4983230072969 + 3 ^ 40 * 2905821 * 2
def baseEnd_2905821 : Nat := 36841552319224214707997

theorem tailTrace_2905821 : CollatzResearch.WordTrace tailWord_2905821 prefixEnd_2905821 36841552319224214707997 := by
  unfold tailWord_2905821
  simp only [CollatzResearch.WordTrace]
  refine ⟨105983998805714266561461317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70655999203809511040974211 105983998805714266561461317)
  ·
    refine ⟨19871999776071424980273997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105983998805714266561461317 19871999776071424980273997)
    ·
      refine ⟨7451999916026784367602749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19871999776071424980273997 7451999916026784367602749)
      ·
        refine ⟨2794499968510044137851031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7451999916026784367602749 2794499968510044137851031)
        ·
          refine ⟨4191749952765066206776547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794499968510044137851031 4191749952765066206776547)
          ·
            refine ⟨6287624929147599310164821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4191749952765066206776547 6287624929147599310164821)
            ·
              refine ⟨36841552319224214707997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6287624929147599310164821 36841552319224214707997)
              ·
                rfl

theorem cell22_2905821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 9].length) (baseStart_2905821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905821 prefixEnd_2905821 := by exact prefixLift 2905821
  have htrace : WordTrace (prefixWord ++ tailWord_2905821) baseStart_2905821 baseEnd_2905821 := by
    simpa [prefixWord, tailWord_2905821, baseEnd_2905821] using wordTrace_append hprefix tailTrace_2905821
  have hstable : (prefixWord ++ tailWord_2905821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905821).length < 2 ^ (prefixWord ++ tailWord_2905821).sum := by decide
  have hdescent : baseEnd_2905821 < baseStart_2905821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905825 : List Nat := [1, 2, 3, 1, 6, 1, 1, 2, 2, 3]
def baseStart_2905825 : Nat := 118140960795 + 2905825 * 2 ^ 59
def prefixEnd_2905825 : Nat := 4983230072969 + 3 ^ 40 * 2905825 * 2
def baseEnd_2905825 : Nat := 994723281900799120015907

theorem tailTrace_2905825 : CollatzResearch.WordTrace tailWord_2905825 prefixEnd_2905825 994723281900799120015907 := by
  unfold tailWord_2905825
  simp only [CollatzResearch.WordTrace]
  refine ⟨105984144697699775244606929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70656096465133183496404619 105984144697699775244606929)
  ·
    refine ⟨79488108523274831433455197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105984144697699775244606929 79488108523274831433455197)
    ·
      refine ⟨29808040696228061787545699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79488108523274831433455197 29808040696228061787545699)
      ·
        refine ⟨44712061044342092681318549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29808040696228061787545699 44712061044342092681318549)
        ·
          refine ⟨2095877861453535594436807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44712061044342092681318549 2095877861453535594436807)
          ·
            refine ⟨3143816792180303391655211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095877861453535594436807 3143816792180303391655211)
            ·
              refine ⟨4715725188270455087482817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3143816792180303391655211 4715725188270455087482817)
              ·
                refine ⟨3536793891202841315612113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4715725188270455087482817 3536793891202841315612113)
                ·
                  refine ⟨2652595418402130986709085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3536793891202841315612113 2652595418402130986709085)
                  ·
                    refine ⟨994723281900799120015907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652595418402130986709085 994723281900799120015907)
                    ·
                      rfl

theorem cell22_2905825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_2905825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905825 prefixEnd_2905825 := by exact prefixLift 2905825
  have htrace : WordTrace (prefixWord ++ tailWord_2905825) baseStart_2905825 baseEnd_2905825 := by
    simpa [prefixWord, tailWord_2905825, baseEnd_2905825] using wordTrace_append hprefix tailTrace_2905825
  have hstable : (prefixWord ++ tailWord_2905825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905825).length < 2 ^ (prefixWord ++ tailWord_2905825).sum := by decide
  have hdescent : baseEnd_2905825 < baseStart_2905825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905913 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 3, 4]
def baseStart_2905913 : Nat := 118140960795 + 2905913 * 2 ^ 59
def prefixEnd_2905913 : Nat := 4983230072969 + 3 ^ 40 * 2905913 * 2
def baseEnd_2905913 : Nat := 994753406099196223815637

theorem tailTrace_2905913 : CollatzResearch.WordTrace tailWord_2905913 prefixEnd_2905913 994753406099196223815637 := by
  unfold tailWord_2905913
  simp only [CollatzResearch.WordTrace]
  refine ⟨105987354321380966273810393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70658236214253977515873595 105987354321380966273810393)
  ·
    refine ⟨79490515741035724705357795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105987354321380966273810393 79490515741035724705357795)
    ·
      refine ⟨119235773611553587058036693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79490515741035724705357795 119235773611553587058036693)
      ·
        refine ⟨2794588444020787196672735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 119235773611553587058036693 2794588444020787196672735)
        ·
          refine ⟨4191882666031180795009103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794588444020787196672735 4191882666031180795009103)
          ·
            refine ⟨6287823999046771192513655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4191882666031180795009103 6287823999046771192513655)
            ·
              refine ⟨9431735998570156788770483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6287823999046771192513655 9431735998570156788770483)
              ·
                refine ⟨14147603997855235183155725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9431735998570156788770483 14147603997855235183155725)
                ·
                  refine ⟨5305351499195713193683397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14147603997855235183155725 5305351499195713193683397)
                  ·
                    refine ⟨994753406099196223815637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5305351499195713193683397 994753406099196223815637)
                    ·
                      rfl

theorem cell22_2905913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 4].length) (baseStart_2905913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905913 prefixEnd_2905913 := by exact prefixLift 2905913
  have htrace : WordTrace (prefixWord ++ tailWord_2905913) baseStart_2905913 baseEnd_2905913 := by
    simpa [prefixWord, tailWord_2905913, baseEnd_2905913] using wordTrace_append hprefix tailTrace_2905913
  have hstable : (prefixWord ++ tailWord_2905913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905913).length < 2 ^ (prefixWord ++ tailWord_2905913).sum := by decide
  have hdescent : baseEnd_2905913 < baseStart_2905913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905941 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_2905941 : Nat := 118140960795 + 2905941 * 2 ^ 59
def prefixEnd_2905941 : Nat := 4983230072969 + 3 ^ 40 * 2905941 * 2
def baseEnd_2905941 : Nat := 994762991071413484115551

theorem tailTrace_2905941 : CollatzResearch.WordTrace tailWord_2905941 prefixEnd_2905941 994762991071413484115551 := by
  unfold tailWord_2905941
  simp only [CollatzResearch.WordTrace]
  refine ⟨105988375565279527055829677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70658917043519684703886451 105988375565279527055829677)
  ·
    refine ⟨39745640836979822645936129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105988375565279527055829677 39745640836979822645936129)
    ·
      refine ⟨29809230627734866984452097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39745640836979822645936129 29809230627734866984452097)
      ·
        refine ⟨22356922970801150238339073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29809230627734866984452097 22356922970801150238339073)
        ·
          refine ⟨16767692228100862678754305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22356922970801150238339073 16767692228100862678754305)
          ·
            refine ⟨12575769171075647009065729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16767692228100862678754305 12575769171075647009065729)
            ·
              refine ⟨9431826878306735256799297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12575769171075647009065729 9431826878306735256799297)
              ·
                refine ⟨7073870158730051442599473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9431826878306735256799297 7073870158730051442599473)
                ·
                  refine ⟨5305402619047538581949605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7073870158730051442599473 5305402619047538581949605)
                  ·
                    refine ⟨994762991071413484115551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5305402619047538581949605 994762991071413484115551)
                    ·
                      rfl

theorem cell22_2905941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_2905941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905941 prefixEnd_2905941 := by exact prefixLift 2905941
  have htrace : WordTrace (prefixWord ++ tailWord_2905941) baseStart_2905941 baseEnd_2905941 := by
    simpa [prefixWord, tailWord_2905941, baseEnd_2905941] using wordTrace_append hprefix tailTrace_2905941
  have hstable : (prefixWord ++ tailWord_2905941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905941).length < 2 ^ (prefixWord ++ tailWord_2905941).sum := by decide
  have hdescent : baseEnd_2905941 < baseStart_2905941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905969 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 2, 6]
def baseStart_2905969 : Nat := 118140960795 + 2905969 * 2 ^ 59
def prefixEnd_2905969 : Nat := 4983230072969 + 3 ^ 40 * 2905969 * 2
def baseEnd_2905969 : Nat := 994772576043630744415465

theorem tailTrace_2905969 : CollatzResearch.WordTrace tailWord_2905969 prefixEnd_2905969 994772576043630744415465 := by
  unfold tailWord_2905969
  simp only [CollatzResearch.WordTrace]
  refine ⟨105989396809178087837848961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70659597872785391891899307 105989396809178087837848961)
  ·
    refine ⟨79492047606883565878386721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105989396809178087837848961 79492047606883565878386721)
    ·
      refine ⟨59619035705162674408790041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79492047606883565878386721 59619035705162674408790041)
      ·
        refine ⟨44714276778872005806592531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59619035705162674408790041 44714276778872005806592531)
        ·
          refine ⟨67071415168308008709888797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44714276778872005806592531 67071415168308008709888797)
          ·
            refine ⟨25151780688115503266208299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67071415168308008709888797 25151780688115503266208299)
            ·
              refine ⟨37727671032173254899312449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25151780688115503266208299 37727671032173254899312449)
              ·
                refine ⟨28295753274129941174484337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37727671032173254899312449 28295753274129941174484337)
                ·
                  refine ⟨21221814955597455880863253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28295753274129941174484337 21221814955597455880863253)
                  ·
                    refine ⟨994772576043630744415465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21221814955597455880863253 994772576043630744415465)
                    ·
                      rfl

theorem cell22_2905969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_2905969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905969 prefixEnd_2905969 := by exact prefixLift 2905969
  have htrace : WordTrace (prefixWord ++ tailWord_2905969) baseStart_2905969 baseEnd_2905969 := by
    simpa [prefixWord, tailWord_2905969, baseEnd_2905969] using wordTrace_append hprefix tailTrace_2905969
  have hstable : (prefixWord ++ tailWord_2905969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905969).length < 2 ^ (prefixWord ++ tailWord_2905969).sum := by decide
  have hdescent : baseEnd_2905969 < baseStart_2905969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905984 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 7]
def baseStart_2905984 : Nat := 118140960795 + 2905984 * 2 ^ 59
def prefixEnd_2905984 : Nat := 4983230072969 + 3 ^ 40 * 2905984 * 2
def baseEnd_2905984 : Nat := 331592570283391901763473

theorem tailTrace_2905984 : CollatzResearch.WordTrace tailWord_2905984 prefixEnd_2905984 331592570283391901763473 := by
  unfold tailWord_2905984
  simp only [CollatzResearch.WordTrace]
  refine ⟨52994971952061872699822503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70659962602749163599763337 52994971952061872699822503)
  ·
    refine ⟨79492457928092809049733755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52994971952061872699822503 79492457928092809049733755)
    ·
      refine ⟨119238686892139213574600633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79492457928092809049733755 119238686892139213574600633)
      ·
        refine ⟨89429015169104410180950475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119238686892139213574600633 89429015169104410180950475)
        ·
          refine ⟨134143522753656615271425713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89429015169104410180950475 134143522753656615271425713)
          ·
            refine ⟨100607642065242461453569285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134143522753656615271425713 100607642065242461453569285)
            ·
              refine ⟨18863932887232961522544241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100607642065242461453569285 18863932887232961522544241)
              ·
                refine ⟨14147949665424721141908181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18863932887232961522544241 14147949665424721141908181)
                ·
                  refine ⟨331592570283391901763473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14147949665424721141908181 331592570283391901763473)
                  ·
                    rfl

theorem cell22_2905984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_2905984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2905984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2905984 prefixEnd_2905984 := by exact prefixLift 2905984
  have htrace : WordTrace (prefixWord ++ tailWord_2905984) baseStart_2905984 baseEnd_2905984 := by
    simpa [prefixWord, tailWord_2905984, baseEnd_2905984] using wordTrace_append hprefix tailTrace_2905984
  have hstable : (prefixWord ++ tailWord_2905984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905984).length < 2 ^ (prefixWord ++ tailWord_2905984).sum := by decide
  have hdescent : baseEnd_2905984 < baseStart_2905984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906001 : List Nat := [1, 2, 2, 1, 1, 1, 7, 2, 5]
def baseStart_2906001 : Nat := 118140960795 + 2906001 * 2 ^ 59
def prefixEnd_2906001 : Nat := 4983230072969 + 3 ^ 40 * 2906001 * 2
def baseEnd_2906001 : Nat := 331594510099197775871789

theorem tailTrace_2906001 : CollatzResearch.WordTrace tailWord_2906001 prefixEnd_2906001 331594510099197775871789 := by
  unfold tailWord_2906001
  simp only [CollatzResearch.WordTrace]
  refine ⟨105990563945062157303013857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70660375963374771535342571 105990563945062157303013857)
  ·
    refine ⟨79492922958796617977260393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105990563945062157303013857 79492922958796617977260393)
    ·
      refine ⟨59619692219097463482945295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79492922958796617977260393 59619692219097463482945295)
      ·
        refine ⟨89429538328646195224417943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59619692219097463482945295 89429538328646195224417943)
        ·
          refine ⟨134144307492969292836626915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89429538328646195224417943 134144307492969292836626915)
          ·
            refine ⟨201216461239453939254940373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134144307492969292836626915 201216461239453939254940373)
            ·
              refine ⟨4716010810299701701287665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 201216461239453939254940373 4716010810299701701287665)
              ·
                refine ⟨3537008107724776275965749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4716010810299701701287665 3537008107724776275965749)
                ·
                  refine ⟨331594510099197775871789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3537008107724776275965749 331594510099197775871789)
                  ·
                    rfl

theorem cell22_2906001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 5].length) (baseStart_2906001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906001 prefixEnd_2906001 := by exact prefixLift 2906001
  have htrace : WordTrace (prefixWord ++ tailWord_2906001) baseStart_2906001 baseEnd_2906001 := by
    simpa [prefixWord, tailWord_2906001, baseEnd_2906001] using wordTrace_append hprefix tailTrace_2906001
  have hstable : (prefixWord ++ tailWord_2906001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906001).length < 2 ^ (prefixWord ++ tailWord_2906001).sum := by decide
  have hdescent : baseEnd_2906001 < baseStart_2906001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906110 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2906110 : Nat := 118140960795 + 2906110 * 2 ^ 59
def prefixEnd_2906110 : Nat := 4983230072969 + 3 ^ 40 * 2906110 * 2
def baseEnd_2906110 : Nat := 994820843225153376640033

theorem tailTrace_2906110 : CollatzResearch.WordTrace tailWord_2906110 prefixEnd_2906110 994820843225153376640033 := by
  unfold tailWord_2906110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13249317437708408614841473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70663026334444845945821189 13249317437708408614841473)
  ·
    refine ⟨9936988078281306461131105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13249317437708408614841473 9936988078281306461131105)
    ·
      refine ⟨7452741058710979845848329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9936988078281306461131105 7452741058710979845848329)
      ·
        refine ⟨5589555794033234884386247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7452741058710979845848329 5589555794033234884386247)
        ·
          refine ⟨8384333691049852326579371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5589555794033234884386247 8384333691049852326579371)
          ·
            refine ⟨12576500536574778489869057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8384333691049852326579371 12576500536574778489869057)
            ·
              refine ⟨9432375402431083867401793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12576500536574778489869057 9432375402431083867401793)
              ·
                refine ⟨7074281551823312900551345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9432375402431083867401793 7074281551823312900551345)
                ·
                  refine ⟨5305711163867484675413509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7074281551823312900551345 5305711163867484675413509)
                  ·
                    refine ⟨994820843225153376640033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5305711163867484675413509 994820843225153376640033)
                    ·
                      rfl

theorem cell22_2906110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2906110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906110 prefixEnd_2906110 := by exact prefixLift 2906110
  have htrace : WordTrace (prefixWord ++ tailWord_2906110) baseStart_2906110 baseEnd_2906110 := by
    simpa [prefixWord, tailWord_2906110, baseEnd_2906110] using wordTrace_append hprefix tailTrace_2906110
  have hstable : (prefixWord ++ tailWord_2906110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906110).length < 2 ^ (prefixWord ++ tailWord_2906110).sum := by decide
  have hdescent : baseEnd_2906110 < baseStart_2906110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906123 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 3, 3]
def baseStart_2906123 : Nat := 118140960795 + 2906123 * 2 ^ 59
def prefixEnd_2906123 : Nat := 4983230072969 + 3 ^ 40 * 2906123 * 2
def baseEnd_2906123 : Nat := 994825293390825676064993

theorem tailTrace_2906123 : CollatzResearch.WordTrace tailWord_2906123 prefixEnd_2906123 994825293390825676064993 := by
  unfold tailWord_2906123
  simp only [CollatzResearch.WordTrace]
  refine ⟨105995013650620172138955023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70663342433746781425970015 105995013650620172138955023)
  ·
    refine ⟨158992520475930258208432535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105995013650620172138955023 158992520475930258208432535)
    ·
      refine ⟨238488780713895387312648803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158992520475930258208432535 238488780713895387312648803)
      ·
        refine ⟨357733171070843080968973205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238488780713895387312648803 357733171070843080968973205)
        ·
          refine ⟨16768742393945769420420619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 357733171070843080968973205 16768742393945769420420619)
          ·
            refine ⟨25153113590918654130630929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16768742393945769420420619 25153113590918654130630929)
            ·
              refine ⟨18864835193188990597973197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25153113590918654130630929 18864835193188990597973197)
              ·
                refine ⟨7074313197445871474239949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18864835193188990597973197 7074313197445871474239949)
                ·
                  refine ⟨2652867449042201802839981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7074313197445871474239949 2652867449042201802839981)
                  ·
                    refine ⟨994825293390825676064993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652867449042201802839981 994825293390825676064993)
                    ·
                      rfl

theorem cell22_2906123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 3].length) (baseStart_2906123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906123 prefixEnd_2906123 := by exact prefixLift 2906123
  have htrace : WordTrace (prefixWord ++ tailWord_2906123) baseStart_2906123 baseEnd_2906123 := by
    simpa [prefixWord, tailWord_2906123, baseEnd_2906123] using wordTrace_append hprefix tailTrace_2906123
  have hstable : (prefixWord ++ tailWord_2906123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906123).length < 2 ^ (prefixWord ++ tailWord_2906123).sum := by decide
  have hdescent : baseEnd_2906123 < baseStart_2906123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906140 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 3, 3]
def baseStart_2906140 : Nat := 118140960795 + 2906140 * 2 ^ 59
def prefixEnd_2906140 : Nat := 4983230072969 + 3 ^ 40 * 2906140 * 2
def baseEnd_2906140 : Nat := 994831112838243298389941

theorem tailTrace_2906140 : CollatzResearch.WordTrace tailWord_2906140 prefixEnd_2906140 994831112838243298389941 := by
  unfold tailWord_2906140
  simp only [CollatzResearch.WordTrace]
  refine ⟨52997816845779292021161937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70663755794372389361549249 52997816845779292021161937)
  ·
    refine ⟨39748362634334469015871453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52997816845779292021161937 39748362634334469015871453)
    ·
      refine ⟨14905635987875425880951795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39748362634334469015871453 14905635987875425880951795)
      ·
        refine ⟨22358453981813138821427693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14905635987875425880951795 22358453981813138821427693)
        ·
          refine ⟨8384420243179927058035385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22358453981813138821427693 8384420243179927058035385)
          ·
            refine ⟨6288315182384945293526539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8384420243179927058035385 6288315182384945293526539)
            ·
              refine ⟨9432472773577417940289809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6288315182384945293526539 9432472773577417940289809)
              ·
                refine ⟨7074354580183063455217357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9432472773577417940289809 7074354580183063455217357)
                ·
                  refine ⟨2652882967568648795706509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7074354580183063455217357 2652882967568648795706509)
                  ·
                    refine ⟨994831112838243298389941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652882967568648795706509 994831112838243298389941)
                    ·
                      rfl

theorem cell22_2906140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_2906140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906140 prefixEnd_2906140 := by exact prefixLift 2906140
  have htrace : WordTrace (prefixWord ++ tailWord_2906140) baseStart_2906140 baseEnd_2906140 := by
    simpa [prefixWord, tailWord_2906140, baseEnd_2906140] using wordTrace_append hprefix tailTrace_2906140
  have hstable : (prefixWord ++ tailWord_2906140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906140).length < 2 ^ (prefixWord ++ tailWord_2906140).sum := by decide
  have hdescent : baseEnd_2906140 < baseStart_2906140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906200 : List Nat := [2, 1, 2, 2, 1, 5, 2, 2, 1, 4]
def baseStart_2906200 : Nat := 118140960795 + 2906200 * 2 ^ 59
def prefixEnd_2906200 : Nat := 4983230072969 + 3 ^ 40 * 2906200 * 2
def baseEnd_2906200 : Nat := 994851652064423141889757

theorem tailTrace_2906200 : CollatzResearch.WordTrace tailWord_2906200 prefixEnd_2906200 994851652064423141889757 := by
  unfold tailWord_2906200
  simp only [CollatzResearch.WordTrace]
  refine ⟨52998911035670607144754027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70665214714227476193005369 52998911035670607144754027)
  ·
    refine ⟨79498366553505910717131041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52998911035670607144754027 79498366553505910717131041)
    ·
      refine ⟨59623774915129433037848281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79498366553505910717131041 59623774915129433037848281)
      ·
        refine ⟨44717831186347074778386211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59623774915129433037848281 44717831186347074778386211)
        ·
          refine ⟨67076746779520612167579317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44717831186347074778386211 67076746779520612167579317)
          ·
            refine ⟨6288445010580057390710561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67076746779520612167579317 6288445010580057390710561)
            ·
              refine ⟨4716333757935043043032921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6288445010580057390710561 4716333757935043043032921)
              ·
                refine ⟨3537250318451282282274691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4716333757935043043032921 3537250318451282282274691)
                ·
                  refine ⟨5305875477676923423412037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3537250318451282282274691 5305875477676923423412037)
                  ·
                    refine ⟨994851652064423141889757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5305875477676923423412037 994851652064423141889757)
                    ·
                      rfl

theorem cell22_2906200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_2906200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906200 prefixEnd_2906200 := by exact prefixLift 2906200
  have htrace : WordTrace (prefixWord ++ tailWord_2906200) baseStart_2906200 baseEnd_2906200 := by
    simpa [prefixWord, tailWord_2906200, baseEnd_2906200] using wordTrace_append hprefix tailTrace_2906200
  have hstable : (prefixWord ++ tailWord_2906200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906200).length < 2 ^ (prefixWord ++ tailWord_2906200).sum := by decide
  have hdescent : baseEnd_2906200 < baseStart_2906200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906243 : List Nat := [1, 1, 1, 3, 3, 4, 2, 7]
def baseStart_2906243 : Nat := 118140960795 + 2906243 * 2 ^ 59
def prefixEnd_2906243 : Nat := 4983230072969 + 3 ^ 40 * 2906243 * 2
def baseEnd_2906243 : Nat := 110540707982576151451625

theorem tailTrace_2906243 : CollatzResearch.WordTrace tailWord_2906243 prefixEnd_2906243 110540707982576151451625 := by
  unfold tailWord_2906243
  simp only [CollatzResearch.WordTrace]
  refine ⟨105999390410185432633323383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70666260273456955088882255 105999390410185432633323383)
  ·
    refine ⟨158999085615278148949985075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105999390410185432633323383 158999085615278148949985075)
    ·
      refine ⟨238498628422917223424977613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158999085615278148949985075 238498628422917223424977613)
      ·
        refine ⟨89436985658593958784366605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238498628422917223424977613 89436985658593958784366605)
        ·
          refine ⟨33538869621972734544137477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89436985658593958784366605 33538869621972734544137477)
          ·
            refine ⟨6288538054119887727025777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33538869621972734544137477 6288538054119887727025777)
            ·
              refine ⟨4716403540589915795269333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6288538054119887727025777 4716403540589915795269333)
              ·
                refine ⟨110540707982576151451625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4716403540589915795269333 110540707982576151451625)
                ·
                  rfl

theorem cell22_2906243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 7].length) (baseStart_2906243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906243 prefixEnd_2906243 := by exact prefixLift 2906243
  have htrace : WordTrace (prefixWord ++ tailWord_2906243) baseStart_2906243 baseEnd_2906243 := by
    simpa [prefixWord, tailWord_2906243, baseEnd_2906243] using wordTrace_append hprefix tailTrace_2906243
  have hstable : (prefixWord ++ tailWord_2906243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906243).length < 2 ^ (prefixWord ++ tailWord_2906243).sum := by decide
  have hdescent : baseEnd_2906243 < baseStart_2906243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906247 : List Nat := [1, 1, 4, 2, 1, 1, 6, 1, 2, 3]
def baseStart_2906247 : Nat := 118140960795 + 2906247 * 2 ^ 59
def prefixEnd_2906247 : Nat := 4983230072969 + 3 ^ 40 * 2906247 * 2
def baseEnd_2906247 : Nat := 994867741124930685964613

theorem tailTrace_2906247 : CollatzResearch.WordTrace tailWord_2906247 prefixEnd_2906247 994867741124930685964613 := by
  unfold tailWord_2906247
  simp only [CollatzResearch.WordTrace]
  refine ⟨105999536302170941316468995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70666357534780627544312663 105999536302170941316468995)
  ·
    refine ⟨158999304453256411974703493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105999536302170941316468995 158999304453256411974703493)
    ·
      refine ⟨29812369584985577245256905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158999304453256411974703493 29812369584985577245256905)
      ·
        refine ⟨22359277188739182933942679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29812369584985577245256905 22359277188739182933942679)
        ·
          refine ⟨33538915783108774400914019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22359277188739182933942679 33538915783108774400914019)
          ·
            refine ⟨50308373674663161601371029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33538915783108774400914019 50308373674663161601371029)
            ·
              refine ⟨2358205015999835700064267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50308373674663161601371029 2358205015999835700064267)
              ·
                refine ⟨3537307523999753550096401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358205015999835700064267 3537307523999753550096401)
                ·
                  refine ⟨2652980642999815162572301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3537307523999753550096401 2652980642999815162572301)
                  ·
                    refine ⟨994867741124930685964613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652980642999815162572301 994867741124930685964613)
                    ·
                      rfl

theorem cell22_2906247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_2906247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906247 prefixEnd_2906247 := by exact prefixLift 2906247
  have htrace : WordTrace (prefixWord ++ tailWord_2906247) baseStart_2906247 baseEnd_2906247 := by
    simpa [prefixWord, tailWord_2906247, baseEnd_2906247] using wordTrace_append hprefix tailTrace_2906247
  have hstable : (prefixWord ++ tailWord_2906247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906247).length < 2 ^ (prefixWord ++ tailWord_2906247).sum := by decide
  have hdescent : baseEnd_2906247 < baseStart_2906247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906326 : List Nat := [5, 2, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_2906326 : Nat := 118140960795 + 2906326 * 2 ^ 59
def prefixEnd_2906326 : Nat := 4983230072969 + 3 ^ 40 * 2906326 * 2
def baseEnd_2906326 : Nat := 994894784439400813239371

theorem tailTrace_2906326 : CollatzResearch.WordTrace tailWord_2906326 prefixEnd_2906326 994894784439400813239371 := by
  unfold tailWord_2906326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6625151104305296113037177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70668278445923158539063221 6625151104305296113037177)
  ·
    refine ⟨4968863328228972084777883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6625151104305296113037177 4968863328228972084777883)
    ·
      refine ⟨7453294992343458127166825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4968863328228972084777883 7453294992343458127166825)
      ·
        refine ⟨5589971244257593595375119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7453294992343458127166825 5589971244257593595375119)
        ·
          refine ⟨8384956866386390393062679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5589971244257593595375119 8384956866386390393062679)
          ·
            refine ⟨12577435299579585589594019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8384956866386390393062679 12577435299579585589594019)
            ·
              refine ⟨18866152949369378384391029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12577435299579585589594019 18866152949369378384391029)
              ·
                refine ⟨1768701839003379223536659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18866152949369378384391029 1768701839003379223536659)
                ·
                  refine ⟨2653052758505068835304989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768701839003379223536659 2653052758505068835304989)
                  ·
                    refine ⟨994894784439400813239371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2653052758505068835304989 994894784439400813239371)
                    ·
                      rfl

theorem cell22_2906326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_2906326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906326 prefixEnd_2906326 := by exact prefixLift 2906326
  have htrace : WordTrace (prefixWord ++ tailWord_2906326) baseStart_2906326 baseEnd_2906326 := by
    simpa [prefixWord, tailWord_2906326, baseEnd_2906326] using wordTrace_append hprefix tailTrace_2906326
  have hstable : (prefixWord ++ tailWord_2906326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906326).length < 2 ^ (prefixWord ++ tailWord_2906326).sum := by decide
  have hdescent : baseEnd_2906326 < baseStart_2906326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906339 : List Nat := [1, 1, 1, 8, 1, 2, 1, 2, 5]
def baseStart_2906339 : Nat := 118140960795 + 2906339 * 2 ^ 59
def prefixEnd_2906339 : Nat := 4983230072969 + 3 ^ 40 * 2906339 * 2
def baseEnd_2906339 : Nat := 331633078201691037554777

theorem tailTrace_2906339 : CollatzResearch.WordTrace tailWord_2906339 prefixEnd_2906339 331633078201691037554777 := by
  unfold tailWord_2906339
  simp only [CollatzResearch.WordTrace]
  refine ⟨106002891817837641028818071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70668594545225094019212047 106002891817837641028818071)
  ·
    refine ⟨159004337726756461543227107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106002891817837641028818071 159004337726756461543227107)
    ·
      refine ⟨238506506590134692314840661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159004337726756461543227107 238506506590134692314840661)
      ·
        refine ⟨2794998124103140925564539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 238506506590134692314840661 2794998124103140925564539)
        ·
          refine ⟨4192497186154711388346809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794998124103140925564539 4192497186154711388346809)
          ·
            refine ⟨3144372889616033541260107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4192497186154711388346809 3144372889616033541260107)
            ·
              refine ⟨4716559334424050311890161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144372889616033541260107 4716559334424050311890161)
              ·
                refine ⟨3537419500818037733917621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4716559334424050311890161 3537419500818037733917621)
                ·
                  refine ⟨331633078201691037554777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3537419500818037733917621 331633078201691037554777)
                  ·
                    rfl

theorem cell22_2906339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 5].length) (baseStart_2906339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906339 prefixEnd_2906339 := by exact prefixLift 2906339
  have htrace : WordTrace (prefixWord ++ tailWord_2906339) baseStart_2906339 baseEnd_2906339 := by
    simpa [prefixWord, tailWord_2906339, baseEnd_2906339] using wordTrace_append hprefix tailTrace_2906339
  have hstable : (prefixWord ++ tailWord_2906339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906339).length < 2 ^ (prefixWord ++ tailWord_2906339).sum := by decide
  have hdescent : baseEnd_2906339 < baseStart_2906339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906380 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_2906380 : Nat := 118140960795 + 2906380 * 2 ^ 59
def prefixEnd_2906380 : Nat := 4983230072969 + 3 ^ 40 * 2906380 * 2
def baseEnd_2906380 : Nat := 994913269742962672389205

theorem tailTrace_2906380 : CollatzResearch.WordTrace tailWord_2906380 prefixEnd_2906380 994913269742962672389205 := by
  unfold tailWord_2906380
  simp only [CollatzResearch.WordTrace]
  refine ⟨53002193605344552515530297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70669591473792736687373729 53002193605344552515530297)
  ·
    refine ⟨39751645204008414386647723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53002193605344552515530297 39751645204008414386647723)
    ·
      refine ⟨59627467806012621579971585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39751645204008414386647723 59627467806012621579971585)
      ·
        refine ⟨44720600854509466184978689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59627467806012621579971585 44720600854509466184978689)
        ·
          refine ⟨33540450640882099638734017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44720600854509466184978689 33540450640882099638734017)
          ·
            refine ⟨25155337980661574729050513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33540450640882099638734017 25155337980661574729050513)
            ·
              refine ⟨18866503485496181046787885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25155337980661574729050513 18866503485496181046787885)
              ·
                refine ⟨7074938807061067892545457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18866503485496181046787885 7074938807061067892545457)
                ·
                  refine ⟨5306204105295800919409093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7074938807061067892545457 5306204105295800919409093)
                  ·
                    refine ⟨994913269742962672389205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5306204105295800919409093 994913269742962672389205)
                    ·
                      rfl

theorem cell22_2906380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_2906380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906380 prefixEnd_2906380 := by exact prefixLift 2906380
  have htrace : WordTrace (prefixWord ++ tailWord_2906380) baseStart_2906380 baseEnd_2906380 := by
    simpa [prefixWord, tailWord_2906380, baseEnd_2906380] using wordTrace_append hprefix tailTrace_2906380
  have hstable : (prefixWord ++ tailWord_2906380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906380).length < 2 ^ (prefixWord ++ tailWord_2906380).sum := by decide
  have hdescent : baseEnd_2906380 < baseStart_2906380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906444 : List Nat := [2, 2, 1, 3, 2, 1, 2, 5, 1, 3]
def baseStart_2906444 : Nat := 118140960795 + 2906444 * 2 ^ 59
def prefixEnd_2906444 : Nat := 4983230072969 + 3 ^ 40 * 2906444 * 2
def baseEnd_2906444 : Nat := 994935178250887838789009

theorem tailTrace_2906444 : CollatzResearch.WordTrace tailWord_2906444 prefixEnd_2906444 994935178250887838789009 := by
  unfold tailWord_2906444
  simp only [CollatzResearch.WordTrace]
  refine ⟨53003360741228621980695193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70671147654971495974260257 53003360741228621980695193)
  ·
    refine ⟨39752520555921466485521395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53003360741228621980695193 39752520555921466485521395)
    ·
      refine ⟨59628780833882199728282093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39752520555921466485521395 59628780833882199728282093)
      ·
        refine ⟨22360792812705824898105785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59628780833882199728282093 22360792812705824898105785)
        ·
          refine ⟨16770594609529368673579339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22360792812705824898105785 16770594609529368673579339)
          ·
            refine ⟨25155891914294053010369009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16770594609529368673579339 25155891914294053010369009)
            ·
              refine ⟨18866918935720539757776757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25155891914294053010369009 18866918935720539757776757)
              ·
                refine ⟨1768773650223800602291571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18866918935720539757776757 1768773650223800602291571)
                ·
                  refine ⟨2653160475335700903437357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768773650223800602291571 2653160475335700903437357)
                  ·
                    refine ⟨994935178250887838789009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2653160475335700903437357 994935178250887838789009)
                    ·
                      rfl

theorem cell22_2906444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_2906444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906444 prefixEnd_2906444 := by exact prefixLift 2906444
  have htrace : WordTrace (prefixWord ++ tailWord_2906444) baseStart_2906444 baseEnd_2906444 := by
    simpa [prefixWord, tailWord_2906444, baseEnd_2906444] using wordTrace_append hprefix tailTrace_2906444
  have hstable : (prefixWord ++ tailWord_2906444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906444).length < 2 ^ (prefixWord ++ tailWord_2906444).sum := by decide
  have hdescent : baseEnd_2906444 < baseStart_2906444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906455 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 2, 5]
def baseStart_2906455 : Nat := 118140960795 + 2906455 * 2 ^ 59
def prefixEnd_2906455 : Nat := 4983230072969 + 3 ^ 40 * 2906455 * 2
def baseEnd_2906455 : Nat := 994938943775687476763975

theorem tailTrace_2906455 : CollatzResearch.WordTrace tailWord_2906455 prefixEnd_2906455 994938943775687476763975 := by
  unfold tailWord_2906455
  simp only [CollatzResearch.WordTrace]
  refine ⟨106007122685417392840040819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70671415123611595226693879 106007122685417392840040819)
  ·
    refine ⟨159010684028126089260061229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106007122685417392840040819 159010684028126089260061229)
    ·
      refine ⟨59629006510547283472522961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159010684028126089260061229 59629006510547283472522961)
      ·
        refine ⟨44721754882910462604392221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59629006510547283472522961 44721754882910462604392221)
        ·
          refine ⟨16770658081091423476647083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44721754882910462604392221 16770658081091423476647083)
          ·
            refine ⟨25155987121637135214970625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16770658081091423476647083 25155987121637135214970625)
            ·
              refine ⟨18866990341227851411227969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25155987121637135214970625 18866990341227851411227969)
              ·
                refine ⟨14150242755920888558420977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18866990341227851411227969 14150242755920888558420977)
                ·
                  refine ⟨10612682066940666418815733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14150242755920888558420977 10612682066940666418815733)
                  ·
                    refine ⟨994938943775687476763975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10612682066940666418815733 994938943775687476763975)
                    ·
                      rfl

theorem cell22_2906455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_2906455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906455 prefixEnd_2906455 := by exact prefixLift 2906455
  have htrace : WordTrace (prefixWord ++ tailWord_2906455) baseStart_2906455 baseEnd_2906455 := by
    simpa [prefixWord, tailWord_2906455, baseEnd_2906455] using wordTrace_append hprefix tailTrace_2906455
  have hstable : (prefixWord ++ tailWord_2906455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906455).length < 2 ^ (prefixWord ++ tailWord_2906455).sum := by decide
  have hdescent : baseEnd_2906455 < baseStart_2906455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906472 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 2, 5]
def baseStart_2906472 : Nat := 118140960795 + 2906472 * 2 ^ 59
def prefixEnd_2906472 : Nat := 4983230072969 + 3 ^ 40 * 2906472 * 2
def baseEnd_2906472 : Nat := 994944763223105099088923

theorem tailTrace_2906472 : CollatzResearch.WordTrace tailWord_2906472 prefixEnd_2906472 994944763223105099088923 := by
  unfold tailWord_2906472
  simp only [CollatzResearch.WordTrace]
  refine ⟨53003871363177902371704835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70671828484237203162273113 53003871363177902371704835)
  ·
    refine ⟨79505807044766853557557253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53003871363177902371704835 79505807044766853557557253)
    ·
      refine ⟨14907338820893785042041985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79505807044766853557557253 14907338820893785042041985)
      ·
        refine ⟨11180504115670338781531489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14907338820893785042041985 11180504115670338781531489)
        ·
          refine ⟨8385378086752754086148617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11180504115670338781531489 8385378086752754086148617)
          ·
            refine ⟨6289033565064565564611463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8385378086752754086148617 6289033565064565564611463)
            ·
              refine ⟨9433550347596848346917195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6289033565064565564611463 9433550347596848346917195)
              ·
                refine ⟨14150325521395272520375793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9433550347596848346917195 14150325521395272520375793)
                ·
                  refine ⟨10612744141046454390281845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14150325521395272520375793 10612744141046454390281845)
                  ·
                    refine ⟨994944763223105099088923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10612744141046454390281845 994944763223105099088923)
                    ·
                      rfl

theorem cell22_2906472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_2906472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906472 prefixEnd_2906472 := by exact prefixLift 2906472
  have htrace : WordTrace (prefixWord ++ tailWord_2906472) baseStart_2906472 baseEnd_2906472 := by
    simpa [prefixWord, tailWord_2906472, baseEnd_2906472] using wordTrace_append hprefix tailTrace_2906472
  have hstable : (prefixWord ++ tailWord_2906472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906472).length < 2 ^ (prefixWord ++ tailWord_2906472).sum := by decide
  have hdescent : baseEnd_2906472 < baseStart_2906472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906560 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 1, 8]
def baseStart_2906560 : Nat := 118140960795 + 2906560 * 2 ^ 59
def prefixEnd_2906560 : Nat := 4983230072969 + 3 ^ 40 * 2906560 * 2
def baseEnd_2906560 : Nat := 994974887421502202888653

theorem tailTrace_2906560 : CollatzResearch.WordTrace tailWord_2906560 prefixEnd_2906560 994974887421502202888653 := by
  unfold tailWord_2906560
  simp only [CollatzResearch.WordTrace]
  refine ⟨53005476175018497886306567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70673968233357997181742089 53005476175018497886306567)
  ·
    refine ⟨79508214262527746829459851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53005476175018497886306567 79508214262527746829459851)
    ·
      refine ⟨119262321393791620244189777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79508214262527746829459851 119262321393791620244189777)
      ·
        refine ⟨89446741045343715183142333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119262321393791620244189777 89446741045343715183142333)
        ·
          refine ⟨33542527892003893193678375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89446741045343715183142333 33542527892003893193678375)
          ·
            refine ⟨50313791838005839790517563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33542527892003893193678375 50313791838005839790517563)
            ·
              refine ⟨75470687757008759685776345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50313791838005839790517563 75470687757008759685776345)
              ·
                refine ⟨56603015817756569764332259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75470687757008759685776345 56603015817756569764332259)
                ·
                  refine ⟨84904523726634854646498389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56603015817756569764332259 84904523726634854646498389)
                  ·
                    refine ⟨994974887421502202888653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84904523726634854646498389 994974887421502202888653)
                    ·
                      rfl

theorem cell22_2906560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_2906560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906560 prefixEnd_2906560 := by exact prefixLift 2906560
  have htrace : WordTrace (prefixWord ++ tailWord_2906560) baseStart_2906560 baseEnd_2906560 := by
    simpa [prefixWord, tailWord_2906560, baseEnd_2906560] using wordTrace_append hprefix tailTrace_2906560
  have hstable : (prefixWord ++ tailWord_2906560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906560).length < 2 ^ (prefixWord ++ tailWord_2906560).sum := by decide
  have hdescent : baseEnd_2906560 < baseStart_2906560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906564 : List Nat := [2, 3, 3, 2, 2, 2, 8]
def baseStart_2906564 : Nat := 118140960795 + 2906564 * 2 ^ 59
def prefixEnd_2906564 : Nat := 4983230072969 + 3 ^ 40 * 2906564 * 2
def baseEnd_2906564 : Nat := 36850972470490649103283

theorem tailTrace_2906564 : CollatzResearch.WordTrace tailWord_2906564 prefixEnd_2906564 36850972470490649103283 := by
  unfold tailWord_2906564
  simp only [CollatzResearch.WordTrace]
  refine ⟨53005549121011252227879373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70674065494681669637172497 53005549121011252227879373)
  ·
    refine ⟨19877080920379219585454765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53005549121011252227879373 19877080920379219585454765)
    ·
      refine ⟨7453905345142207344545537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19877080920379219585454765 7453905345142207344545537)
      ·
        refine ⟨5590429008856655508409153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7453905345142207344545537 5590429008856655508409153)
        ·
          refine ⟨4192821756642491631306865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5590429008856655508409153 4192821756642491631306865)
          ·
            refine ⟨3144616317481868723480149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4192821756642491631306865 3144616317481868723480149)
            ·
              refine ⟨36850972470490649103283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3144616317481868723480149 36850972470490649103283)
              ·
                rfl

theorem cell22_2906564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 8].length) (baseStart_2906564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906564 prefixEnd_2906564 := by exact prefixLift 2906564
  have htrace : WordTrace (prefixWord ++ tailWord_2906564) baseStart_2906564 baseEnd_2906564 := by
    simpa [prefixWord, tailWord_2906564, baseEnd_2906564] using wordTrace_append hprefix tailTrace_2906564
  have hstable : (prefixWord ++ tailWord_2906564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906564).length < 2 ^ (prefixWord ++ tailWord_2906564).sum := by decide
  have hdescent : baseEnd_2906564 < baseStart_2906564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906592 : List Nat := [2, 1, 1, 3, 1, 1, 5, 3, 5]
def baseStart_2906592 : Nat := 118140960795 + 2906592 * 2 ^ 59
def prefixEnd_2906592 : Nat := 4983230072969 + 3 ^ 40 * 2906592 * 2
def baseEnd_2906592 : Nat := 331661947225154928696185

theorem tailTrace_2906592 : CollatzResearch.WordTrace tailWord_2906592 prefixEnd_2906592 331661947225154928696185 := by
  unfold tailWord_2906592
  simp only [CollatzResearch.WordTrace]
  refine ⟨53006059742960532618889015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70674746323947376825185353 53006059742960532618889015)
  ·
    refine ⟨79509089614440798928333523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53006059742960532618889015 79509089614440798928333523)
    ·
      refine ⟨119263634421661198392500285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79509089614440798928333523 119263634421661198392500285)
      ·
        refine ⟨44723862908122949397187607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119263634421661198392500285 44723862908122949397187607)
        ·
          refine ⟨67085794362184424095781411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44723862908122949397187607 67085794362184424095781411)
          ·
            refine ⟨100628691543276636143672117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67085794362184424095781411 100628691543276636143672117)
            ·
              refine ⟨9433939832182184638469261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100628691543276636143672117 9433939832182184638469261)
              ·
                refine ⟨3537727437068319239425973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9433939832182184638469261 3537727437068319239425973)
                ·
                  refine ⟨331661947225154928696185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3537727437068319239425973 331661947225154928696185)
                  ·
                    rfl

theorem cell22_2906592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 5].length) (baseStart_2906592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906592 prefixEnd_2906592 := by exact prefixLift 2906592
  have htrace : WordTrace (prefixWord ++ tailWord_2906592) baseStart_2906592 baseEnd_2906592 := by
    simpa [prefixWord, tailWord_2906592, baseEnd_2906592] using wordTrace_append hprefix tailTrace_2906592
  have hstable : (prefixWord ++ tailWord_2906592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906592).length < 2 ^ (prefixWord ++ tailWord_2906592).sum := by decide
  have hdescent : baseEnd_2906592 < baseStart_2906592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906682 : List Nat := [3, 1, 1, 1, 3, 4, 9]
def baseStart_2906682 : Nat := 118140960795 + 2906682 * 2 ^ 59
def prefixEnd_2906682 : Nat := 4983230072969 + 3 ^ 40 * 2906682 * 2
def baseEnd_2906682 : Nat := 36852468537582761160677

theorem tailTrace_2906682 : CollatzResearch.WordTrace tailWord_2906682 prefixEnd_2906682 36852468537582761160677 := by
  unfold tailWord_2906682
  simp only [CollatzResearch.WordTrace]
  refine ⟨26503850513898752652138575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70676934703730007072369533 26503850513898752652138575)
  ·
    refine ⟨39755775770848128978207863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26503850513898752652138575 39755775770848128978207863)
    ·
      refine ⟨59633663656272193467311795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39755775770848128978207863 59633663656272193467311795)
      ·
        refine ⟨89450495484408290200967693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59633663656272193467311795 89450495484408290200967693)
        ·
          refine ⟨33543935806653108825362885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89450495484408290200967693 33543935806653108825362885)
          ·
            refine ⟨6289487963747457904755541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33543935806653108825362885 6289487963747457904755541)
            ·
              refine ⟨36852468537582761160677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6289487963747457904755541 36852468537582761160677)
              ·
                rfl

theorem cell22_2906682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 9].length) (baseStart_2906682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906682 prefixEnd_2906682 := by exact prefixLift 2906682
  have htrace : WordTrace (prefixWord ++ tailWord_2906682) baseStart_2906682 baseEnd_2906682 := by
    simpa [prefixWord, tailWord_2906682, baseEnd_2906682] using wordTrace_append hprefix tailTrace_2906682
  have hstable : (prefixWord ++ tailWord_2906682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906682).length < 2 ^ (prefixWord ++ tailWord_2906682).sum := by decide
  have hdescent : baseEnd_2906682 < baseStart_2906682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906712 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 2, 6]
def baseStart_2906712 : Nat := 118140960795 + 2906712 * 2 ^ 59
def prefixEnd_2906712 : Nat := 4983230072969 + 3 ^ 40 * 2906712 * 2
def baseEnd_2906712 : Nat := 995026920127824473088187

theorem tailTrace_2906712 : CollatzResearch.WordTrace tailWord_2906712 prefixEnd_2906712 995026920127824473088187 := by
  unfold tailWord_2906712
  simp only [CollatzResearch.WordTrace]
  refine ⟨53008248122743162866073195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70677664163657550488097593 53008248122743162866073195)
  ·
    refine ⟨79512372184114744299109793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53008248122743162866073195 79512372184114744299109793)
    ·
      refine ⟨59634279138086058224332345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79512372184114744299109793 59634279138086058224332345)
      ·
        refine ⟨44725709353564543668249259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59634279138086058224332345 44725709353564543668249259)
        ·
          refine ⟨67088564030346815502373889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44725709353564543668249259 67088564030346815502373889)
          ·
            refine ⟨50316423022760111626780417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67088564030346815502373889 50316423022760111626780417)
            ·
              refine ⟨37737317267070083720085313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50316423022760111626780417 37737317267070083720085313)
              ·
                refine ⟨28302987950302562790063985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37737317267070083720085313 28302987950302562790063985)
                ·
                  refine ⟨21227240962726922092547989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28302987950302562790063985 21227240962726922092547989)
                  ·
                    refine ⟨995026920127824473088187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21227240962726922092547989 995026920127824473088187)
                    ·
                      rfl

theorem cell22_2906712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_2906712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906712 prefixEnd_2906712 := by exact prefixLift 2906712
  have htrace : WordTrace (prefixWord ++ tailWord_2906712) baseStart_2906712 baseEnd_2906712 := by
    simpa [prefixWord, tailWord_2906712, baseEnd_2906712] using wordTrace_append hprefix tailTrace_2906712
  have hstable : (prefixWord ++ tailWord_2906712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906712).length < 2 ^ (prefixWord ++ tailWord_2906712).sum := by decide
  have hdescent : baseEnd_2906712 < baseStart_2906712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906722 : List Nat := [3, 3, 2, 3, 2, 1, 1, 3, 4]
def baseStart_2906722 : Nat := 118140960795 + 2906722 * 2 ^ 59
def prefixEnd_2906722 : Nat := 4983230072969 + 3 ^ 40 * 2906722 * 2
def baseEnd_2906722 : Nat := 331676781110729260112719

theorem tailTrace_2906722 : CollatzResearch.WordTrace tailWord_2906722 prefixEnd_2906722 331676781110729260112719 := by
  unfold tailWord_2906722
  simp only [CollatzResearch.WordTrace]
  refine ⟨26504215243862524360002605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70677907316966731626673613 26504215243862524360002605)
  ·
    refine ⟨9939080716448446635000977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26504215243862524360002605 9939080716448446635000977)
    ·
      refine ⟨7454310537336334976250733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9939080716448446635000977 7454310537336334976250733)
      ·
        refine ⟨2795366451501125616094025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7454310537336334976250733 2795366451501125616094025)
        ·
          refine ⟨2096524838625844212070519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2795366451501125616094025 2096524838625844212070519)
          ·
            refine ⟨3144787257938766318105779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096524838625844212070519 3144787257938766318105779)
            ·
              refine ⟨4717180886908149477158669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144787257938766318105779 4717180886908149477158669)
              ·
                refine ⟨1768942832590556053934501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4717180886908149477158669 1768942832590556053934501)
                ·
                  refine ⟨331676781110729260112719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1768942832590556053934501 331676781110729260112719)
                  ·
                    rfl

theorem cell22_2906722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_2906722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906722 prefixEnd_2906722 := by exact prefixLift 2906722
  have htrace : WordTrace (prefixWord ++ tailWord_2906722) baseStart_2906722 baseEnd_2906722 := by
    simpa [prefixWord, tailWord_2906722, baseEnd_2906722] using wordTrace_append hprefix tailTrace_2906722
  have hstable : (prefixWord ++ tailWord_2906722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906722).length < 2 ^ (prefixWord ++ tailWord_2906722).sum := by decide
  have hdescent : baseEnd_2906722 < baseStart_2906722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906731 : List Nat := [1, 1, 1, 1, 2, 2, 1, 9, 1, 3]
def baseStart_2906731 : Nat := 118140960795 + 2906731 * 2 ^ 59
def prefixEnd_2906731 : Nat := 4983230072969 + 3 ^ 40 * 2906731 * 2
def baseEnd_2906731 : Nat := 995033424216114756863129

theorem tailTrace_2906731 : CollatzResearch.WordTrace tailWord_2906731 prefixEnd_2906731 995033424216114756863129 := by
  unfold tailWord_2906731
  simp only [CollatzResearch.WordTrace]
  refine ⟨106017189232417491977088047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70678126154944994651392031 106017189232417491977088047)
  ·
    refine ⟨159025783848626237965632071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106017189232417491977088047 159025783848626237965632071)
    ·
      refine ⟨238538675772939356948448107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159025783848626237965632071 238538675772939356948448107)
      ·
        refine ⟨357808013659409035422672161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238538675772939356948448107 357808013659409035422672161)
        ·
          refine ⟨268356010244556776567004121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357808013659409035422672161 268356010244556776567004121)
          ·
            refine ⟨201267007683417582425253091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268356010244556776567004121 201267007683417582425253091)
            ·
              refine ⟨301900511525126373637879637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201267007683417582425253091 301900511525126373637879637)
              ·
                refine ⟨1768948309717537345534451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 301900511525126373637879637 1768948309717537345534451)
                ·
                  refine ⟨2653422464576306018301677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768948309717537345534451 2653422464576306018301677)
                  ·
                    refine ⟨995033424216114756863129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2653422464576306018301677 995033424216114756863129)
                    ·
                      rfl

theorem cell22_2906731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 1, 3].length) (baseStart_2906731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906731 prefixEnd_2906731 := by exact prefixLift 2906731
  have htrace : WordTrace (prefixWord ++ tailWord_2906731) baseStart_2906731 baseEnd_2906731 := by
    simpa [prefixWord, tailWord_2906731, baseEnd_2906731] using wordTrace_append hprefix tailTrace_2906731
  have hstable : (prefixWord ++ tailWord_2906731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906731).length < 2 ^ (prefixWord ++ tailWord_2906731).sum := by decide
  have hdescent : baseEnd_2906731 < baseStart_2906731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906943 : List Nat := [1, 1, 2, 2, 5, 1, 3, 2, 1, 4]
def baseStart_2906943 : Nat := 118140960795 + 2906943 * 2 ^ 59
def prefixEnd_2906943 : Nat := 4983230072969 + 3 ^ 40 * 2906943 * 2
def baseEnd_2906943 : Nat := 995105996148616870562479

theorem tailTrace_2906943 : CollatzResearch.WordTrace tailWord_2906943 prefixEnd_2906943 995105996148616870562479 := by
  unfold tailWord_2906943
  simp only [CollatzResearch.WordTrace]
  refine ⟨106024921507649452183805483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70683281005099634789203655 106024921507649452183805483)
  ·
    refine ⟨159037382261474178275708225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106024921507649452183805483 159037382261474178275708225)
    ·
      refine ⟨119278036696105633706781169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159037382261474178275708225 119278036696105633706781169)
      ·
        refine ⟨89458527522079225280085877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119278036696105633706781169 89458527522079225280085877)
        ·
          refine ⟨8386736955194927370008051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89458527522079225280085877 8386736955194927370008051)
          ·
            refine ⟨12580105432792391055012077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8386736955194927370008051 12580105432792391055012077)
            ·
              refine ⟨4717539537297146645629529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12580105432792391055012077 4717539537297146645629529)
              ·
                refine ⟨3538154652972859984222147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4717539537297146645629529 3538154652972859984222147)
                ·
                  refine ⟨5307231979459289976333221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538154652972859984222147 5307231979459289976333221)
                  ·
                    refine ⟨995105996148616870562479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5307231979459289976333221 995105996148616870562479)
                    ·
                      rfl

theorem cell22_2906943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_2906943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906943 prefixEnd_2906943 := by exact prefixLift 2906943
  have htrace : WordTrace (prefixWord ++ tailWord_2906943) baseStart_2906943 baseEnd_2906943 := by
    simpa [prefixWord, tailWord_2906943, baseEnd_2906943] using wordTrace_append hprefix tailTrace_2906943
  have hstable : (prefixWord ++ tailWord_2906943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906943).length < 2 ^ (prefixWord ++ tailWord_2906943).sum := by decide
  have hdescent : baseEnd_2906943 < baseStart_2906943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906956 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_2906956 : Nat := 118140960795 + 2906956 * 2 ^ 59
def prefixEnd_2906956 : Nat := 4983230072969 + 3 ^ 40 * 2906956 * 2
def baseEnd_2906956 : Nat := 995110446314289169987439

theorem tailTrace_2906956 : CollatzResearch.WordTrace tailWord_2906956 prefixEnd_2906956 995110446314289169987439 := by
  unfold tailWord_2906956
  simp only [CollatzResearch.WordTrace]
  refine ⟨53012697828301177702014361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70683597104401570269352481 53012697828301177702014361)
  ·
    refine ⟨39759523371225883276510771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53012697828301177702014361 39759523371225883276510771)
    ·
      refine ⟨59639285056838824914766157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39759523371225883276510771 59639285056838824914766157)
      ·
        refine ⟨22364731896314559343037309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59639285056838824914766157 22364731896314559343037309)
        ·
          refine ⟨8386774461117959753638991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22364731896314559343037309 8386774461117959753638991)
          ·
            refine ⟨12580161691676939630458487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8386774461117959753638991 12580161691676939630458487)
            ·
              refine ⟨18870242537515409445687731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12580161691676939630458487 18870242537515409445687731)
              ·
                refine ⟨28305363806273114168531597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18870242537515409445687731 28305363806273114168531597)
                ·
                  refine ⟨10614511427352417813199349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28305363806273114168531597 10614511427352417813199349)
                  ·
                    refine ⟨995110446314289169987439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10614511427352417813199349 995110446314289169987439)
                    ·
                      rfl

theorem cell22_2906956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_2906956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906956 prefixEnd_2906956 := by exact prefixLift 2906956
  have htrace : WordTrace (prefixWord ++ tailWord_2906956) baseStart_2906956 baseEnd_2906956 := by
    simpa [prefixWord, tailWord_2906956, baseEnd_2906956] using wordTrace_append hprefix tailTrace_2906956
  have hstable : (prefixWord ++ tailWord_2906956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906956).length < 2 ^ (prefixWord ++ tailWord_2906956).sum := by decide
  have hdescent : baseEnd_2906956 < baseStart_2906956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906969 : List Nat := [1, 2, 1, 2, 2, 14]
def baseStart_2906969 : Nat := 118140960795 + 2906969 * 2 ^ 59
def prefixEnd_2906969 : Nat := 4983230072969 + 3 ^ 40 * 2906969 * 2
def baseEnd_2906969 : Nat := 12285369092345203326079

theorem tailTrace_2906969 : CollatzResearch.WordTrace tailWord_2906969 prefixEnd_2906969 12285369092345203326079 := by
  unfold tailWord_2906969
  simp only [CollatzResearch.WordTrace]
  refine ⟨106025869805555258624251961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70683913203703505749501307 106025869805555258624251961)
  ·
    refine ⟨79519402354166443968188971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106025869805555258624251961 79519402354166443968188971)
    ·
      refine ⟨119279103531249665952283457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79519402354166443968188971 119279103531249665952283457)
      ·
        refine ⟨89459327648437249464212593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119279103531249665952283457 89459327648437249464212593)
        ·
          refine ⟨67094495736327937098159445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89459327648437249464212593 67094495736327937098159445)
          ·
            refine ⟨12285369092345203326079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 67094495736327937098159445 12285369092345203326079)
            ·
              rfl

theorem cell22_2906969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 14].length) (baseStart_2906969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906969 prefixEnd_2906969 := by exact prefixLift 2906969
  have htrace : WordTrace (prefixWord ++ tailWord_2906969) baseStart_2906969 baseEnd_2906969 := by
    simpa [prefixWord, tailWord_2906969, baseEnd_2906969] using wordTrace_append hprefix tailTrace_2906969
  have hstable : (prefixWord ++ tailWord_2906969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906969).length < 2 ^ (prefixWord ++ tailWord_2906969).sum := by decide
  have hdescent : baseEnd_2906969 < baseStart_2906969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906990 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_2906990 : Nat := 118140960795 + 2906990 * 2 ^ 59
def prefixEnd_2906990 : Nat := 4983230072969 + 3 ^ 40 * 2906990 * 2
def baseEnd_2906990 : Nat := 995122085209124414637335

theorem tailTrace_2906990 : CollatzResearch.WordTrace tailWord_2906990 prefixEnd_2906990 995122085209124414637335 := by
  unfold tailWord_2906990
  simp only [CollatzResearch.WordTrace]
  refine ⟨13253329467309897401345803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70684423825652786140510949 13253329467309897401345803)
  ·
    refine ⟨19879994200964846102018705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13253329467309897401345803 19879994200964846102018705)
    ·
      refine ⟨14909995650723634576514029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19879994200964846102018705 14909995650723634576514029)
      ·
        refine ⟨5591248369021362966192761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14909995650723634576514029 5591248369021362966192761)
        ·
          refine ⟨4193436276766022224644571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5591248369021362966192761 4193436276766022224644571)
          ·
            refine ⟨6290154415149033336966857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4193436276766022224644571 6290154415149033336966857)
            ·
              refine ⟨4717615811361775002725143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6290154415149033336966857 4717615811361775002725143)
              ·
                refine ⟨7076423717042662504087715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4717615811361775002725143 7076423717042662504087715)
                ·
                  refine ⟨10614635575563993756131573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7076423717042662504087715 10614635575563993756131573)
                  ·
                    refine ⟨995122085209124414637335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10614635575563993756131573 995122085209124414637335)
                    ·
                      rfl

theorem cell22_2906990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_2906990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2906990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2906990 prefixEnd_2906990 := by exact prefixLift 2906990
  have htrace : WordTrace (prefixWord ++ tailWord_2906990) baseStart_2906990 baseEnd_2906990 := by
    simpa [prefixWord, tailWord_2906990, baseEnd_2906990] using wordTrace_append hprefix tailTrace_2906990
  have hstable : (prefixWord ++ tailWord_2906990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906990).length < 2 ^ (prefixWord ++ tailWord_2906990).sum := by decide
  have hdescent : baseEnd_2906990 < baseStart_2906990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907031 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 7]
def baseStart_2907031 : Nat := 118140960795 + 2907031 * 2 ^ 59
def prefixEnd_2907031 : Nat := 4983230072969 + 3 ^ 40 * 2907031 * 2
def baseEnd_2907031 : Nat := 331712040115671324787403

theorem tailTrace_2907031 : CollatzResearch.WordTrace tailWord_2907031 prefixEnd_2907031 331712040115671324787403 := by
  unfold tailWord_2907031
  simp only [CollatzResearch.WordTrace]
  refine ⟨106028131131330643213008947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70685420754220428808672631 106028131131330643213008947)
  ·
    refine ⟨159042196696995964819513421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106028131131330643213008947 159042196696995964819513421)
    ·
      refine ⟨59640823761373486807317533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159042196696995964819513421 59640823761373486807317533)
      ·
        refine ⟨22365308910515057552744075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59640823761373486807317533 22365308910515057552744075)
        ·
          refine ⟨33547963365772586329116113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22365308910515057552744075 33547963365772586329116113)
          ·
            refine ⟨25160972524329439746837085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33547963365772586329116113 25160972524329439746837085)
            ·
              refine ⟨9435364696623539905063907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25160972524329439746837085 9435364696623539905063907)
              ·
                refine ⟨14153047044935309857595861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9435364696623539905063907 14153047044935309857595861)
                ·
                  refine ⟨331712040115671324787403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14153047044935309857595861 331712040115671324787403)
                  ·
                    rfl

theorem cell22_2907031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 7].length) (baseStart_2907031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907031 prefixEnd_2907031 := by exact prefixLift 2907031
  have htrace : WordTrace (prefixWord ++ tailWord_2907031) baseStart_2907031 baseEnd_2907031 := by
    simpa [prefixWord, tailWord_2907031, baseEnd_2907031] using wordTrace_append hprefix tailTrace_2907031
  have hstable : (prefixWord ++ tailWord_2907031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907031).length < 2 ^ (prefixWord ++ tailWord_2907031).sum := by decide
  have hdescent : baseEnd_2907031 < baseStart_2907031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907069 : List Nat := [1, 4, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_2907069 : Nat := 118140960795 + 2907069 * 2 ^ 59
def prefixEnd_2907069 : Nat := 4983230072969 + 3 ^ 40 * 2907069 * 2
def baseEnd_2907069 : Nat := 995149128523594541912093

theorem tailTrace_2907069 : CollatzResearch.WordTrace tailWord_2907069 prefixEnd_2907069 995149128523594541912093 := by
  unfold tailWord_2907069
  simp only [CollatzResearch.WordTrace]
  refine ⟨106029517105192975702892261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70686344736795317135261507 106029517105192975702892261)
  ·
    refine ⟨19880534457223682944292299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106029517105192975702892261 19880534457223682944292299)
    ·
      refine ⟨29820801685835524416438449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19880534457223682944292299 29820801685835524416438449)
      ·
        refine ⟨22365601264376643312328837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29820801685835524416438449 22365601264376643312328837)
        ·
          refine ⟨4193550237070620621061657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22365601264376643312328837 4193550237070620621061657)
          ·
            refine ⟨3145162677802965465796243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4193550237070620621061657 3145162677802965465796243)
            ·
              refine ⟨4717744016704448198694365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145162677802965465796243 4717744016704448198694365)
              ·
                refine ⟨1769154006264168074510387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4717744016704448198694365 1769154006264168074510387)
                ·
                  refine ⟨2653731009396252111765581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1769154006264168074510387 2653731009396252111765581)
                  ·
                    refine ⟨995149128523594541912093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2653731009396252111765581 995149128523594541912093)
                    ·
                      rfl

theorem cell22_2907069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_2907069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907069 prefixEnd_2907069 := by exact prefixLift 2907069
  have htrace : WordTrace (prefixWord ++ tailWord_2907069) baseStart_2907069 baseEnd_2907069 := by
    simpa [prefixWord, tailWord_2907069, baseEnd_2907069] using wordTrace_append hprefix tailTrace_2907069
  have hstable : (prefixWord ++ tailWord_2907069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907069).length < 2 ^ (prefixWord ++ tailWord_2907069).sum := by decide
  have hdescent : baseEnd_2907069 < baseStart_2907069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907108 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_2907108 : Nat := 118140960795 + 2907108 * 2 ^ 59
def prefixEnd_2907108 : Nat := 4983230072969 + 3 ^ 40 * 2907108 * 2
def baseEnd_2907108 : Nat := 995162479020611440186973

theorem tailTrace_2907108 : CollatzResearch.WordTrace tailWord_2907108 prefixEnd_2907108 995162479020611440186973 := by
  unfold tailWord_2907108
  simp only [CollatzResearch.WordTrace]
  refine ⟨53015469776025842681780989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70687293034701123575707985 53015469776025842681780989)
  ·
    refine ⟨19880801166009691005667871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53015469776025842681780989 19880801166009691005667871)
    ·
      refine ⟨29821201749014536508501807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19880801166009691005667871 29821201749014536508501807)
      ·
        refine ⟨44731802623521804762752711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29821201749014536508501807 44731802623521804762752711)
        ·
          refine ⟨67097703935282707144129067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44731802623521804762752711 67097703935282707144129067)
          ·
            refine ⟨100646555902924060716193601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67097703935282707144129067 100646555902924060716193601)
            ·
              refine ⟨75484916927193045537145201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100646555902924060716193601 75484916927193045537145201)
              ·
                refine ⟨56613687695394784152858901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75484916927193045537145201 56613687695394784152858901)
                ·
                  refine ⟨2653766610721630507165261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56613687695394784152858901 2653766610721630507165261)
                  ·
                    refine ⟨995162479020611440186973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2653766610721630507165261 995162479020611440186973)
                    ·
                      rfl

theorem cell22_2907108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_2907108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907108 prefixEnd_2907108 := by exact prefixLift 2907108
  have htrace : WordTrace (prefixWord ++ tailWord_2907108) baseStart_2907108 baseEnd_2907108 := by
    simpa [prefixWord, tailWord_2907108, baseEnd_2907108] using wordTrace_append hprefix tailTrace_2907108
  have hstable : (prefixWord ++ tailWord_2907108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907108).length < 2 ^ (prefixWord ++ tailWord_2907108).sum := by decide
  have hdescent : baseEnd_2907108 < baseStart_2907108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907136 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 4, 7]
def baseStart_2907136 : Nat := 118140960795 + 2907136 * 2 ^ 59
def prefixEnd_2907136 : Nat := 4983230072969 + 3 ^ 40 * 2907136 * 2
def baseEnd_2907136 : Nat := 995172063992828700486887

theorem tailTrace_2907136 : CollatzResearch.WordTrace tailWord_2907136 prefixEnd_2907136 995172063992828700486887 := by
  unfold tailWord_2907136
  simp only [CollatzResearch.WordTrace]
  refine ⟨53015980397975123072790631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70687973863966830763720841 53015980397975123072790631)
  ·
    refine ⟨79523970596962684609185947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53015980397975123072790631 79523970596962684609185947)
    ·
      refine ⟨119285955895444026913778921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79523970596962684609185947 119285955895444026913778921)
      ·
        refine ⟨89464466921583020185334191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119285955895444026913778921 89464466921583020185334191)
        ·
          refine ⟨134196700382374530278001287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89464466921583020185334191 134196700382374530278001287)
          ·
            refine ⟨201295050573561795417001931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134196700382374530278001287 201295050573561795417001931)
            ·
              refine ⟨301942575860342693125502897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201295050573561795417001931 301942575860342693125502897)
              ·
                refine ⟨226456931895257019844127173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301942575860342693125502897 226456931895257019844127173)
                ·
                  refine ⟨42460674730360691220773845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226456931895257019844127173 42460674730360691220773845)
                  ·
                    refine ⟨995172063992828700486887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42460674730360691220773845 995172063992828700486887)
                    ·
                      rfl

theorem cell22_2907136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_2907136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907136 prefixEnd_2907136 := by exact prefixLift 2907136
  have htrace : WordTrace (prefixWord ++ tailWord_2907136) baseStart_2907136 baseEnd_2907136 := by
    simpa [prefixWord, tailWord_2907136, baseEnd_2907136] using wordTrace_append hprefix tailTrace_2907136
  have hstable : (prefixWord ++ tailWord_2907136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907136).length < 2 ^ (prefixWord ++ tailWord_2907136).sum := by decide
  have hdescent : baseEnd_2907136 < baseStart_2907136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907153 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 7, 3]
def baseStart_2907153 : Nat := 118140960795 + 2907153 * 2 ^ 59
def prefixEnd_2907153 : Nat := 4983230072969 + 3 ^ 40 * 2907153 * 2
def baseEnd_2907153 : Nat := 995177883440246322811835

theorem tailTrace_2907153 : CollatzResearch.WordTrace tailWord_2907153 prefixEnd_2907153 995177883440246322811835 := by
  unfold tailWord_2907153
  simp only [CollatzResearch.WordTrace]
  refine ⟨106032580836888658048950113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70688387224592438699300075 106032580836888658048950113)
  ·
    refine ⟨79524435627666493536712585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106032580836888658048950113 79524435627666493536712585)
    ·
      refine ⟨59643326720749870152534439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79524435627666493536712585 59643326720749870152534439)
      ·
        refine ⟨89464990081124805228801659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59643326720749870152534439 89464990081124805228801659)
        ·
          refine ⟨134197485121687207843202489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89464990081124805228801659 134197485121687207843202489)
          ·
            refine ⟨100648113841265405882401867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134197485121687207843202489 100648113841265405882401867)
            ·
              refine ⟨150972170761898108823602801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100648113841265405882401867 150972170761898108823602801)
              ·
                refine ⟨113229128071423581617702101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150972170761898108823602801 113229128071423581617702101)
                ·
                  refine ⟨2653807689173990194164893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 113229128071423581617702101 2653807689173990194164893)
                  ·
                    refine ⟨995177883440246322811835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2653807689173990194164893 995177883440246322811835)
                    ·
                      rfl

theorem cell22_2907153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_2907153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907153 prefixEnd_2907153 := by exact prefixLift 2907153
  have htrace : WordTrace (prefixWord ++ tailWord_2907153) baseStart_2907153 baseEnd_2907153 := by
    simpa [prefixWord, tailWord_2907153, baseEnd_2907153] using wordTrace_append hprefix tailTrace_2907153
  have hstable : (prefixWord ++ tailWord_2907153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907153).length < 2 ^ (prefixWord ++ tailWord_2907153).sum := by decide
  have hdescent : baseEnd_2907153 < baseStart_2907153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907170 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_2907170 : Nat := 118140960795 + 2907170 * 2 ^ 59
def prefixEnd_2907170 : Nat := 4983230072969 + 3 ^ 40 * 2907170 * 2
def baseEnd_2907170 : Nat := 995183702887663945136783

theorem tailTrace_2907170 : CollatzResearch.WordTrace tailWord_2907170 prefixEnd_2907170 995183702887663945136783 := by
  unfold tailWord_2907170
  simp only [CollatzResearch.WordTrace]
  refine ⟨26508300219456767488079741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70688800585218046634879309 26508300219456767488079741)
  ·
    refine ⟨9940612582296287808029903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26508300219456767488079741 9940612582296287808029903)
    ·
      refine ⟨14910918873444431712044855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9940612582296287808029903 14910918873444431712044855)
      ·
        refine ⟨22366378310166647568067283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14910918873444431712044855 22366378310166647568067283)
        ·
          refine ⟨33549567465249971352100925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22366378310166647568067283 33549567465249971352100925)
          ·
            refine ⟨12581087799468739257037847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33549567465249971352100925 12581087799468739257037847)
            ·
              refine ⟨18871631699203108885556771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12581087799468739257037847 18871631699203108885556771)
              ·
                refine ⟨28307447548804663328335157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18871631699203108885556771 28307447548804663328335157)
                ·
                  refine ⟨2653823207700437187031421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28307447548804663328335157 2653823207700437187031421)
                  ·
                    refine ⟨995183702887663945136783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2653823207700437187031421 995183702887663945136783)
                    ·
                      rfl

theorem cell22_2907170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_2907170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907170 prefixEnd_2907170 := by exact prefixLift 2907170
  have htrace : WordTrace (prefixWord ++ tailWord_2907170) baseStart_2907170 baseEnd_2907170 := by
    simpa [prefixWord, tailWord_2907170, baseEnd_2907170] using wordTrace_append hprefix tailTrace_2907170
  have hstable : (prefixWord ++ tailWord_2907170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907170).length < 2 ^ (prefixWord ++ tailWord_2907170).sum := by decide
  have hdescent : baseEnd_2907170 < baseStart_2907170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907260 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 4, 3]
def baseStart_2907260 : Nat := 118140960795 + 2907260 * 2 ^ 59
def prefixEnd_2907260 : Nat := 4983230072969 + 3 ^ 40 * 2907260 * 2
def baseEnd_2907260 : Nat := 995214511726933710386507

theorem tailTrace_2907260 : CollatzResearch.WordTrace tailWord_2907260 prefixEnd_2907260 995214511726933710386507 := by
  unfold tailWord_2907260
  simp only [CollatzResearch.WordTrace]
  refine ⟨53018241723750507661547617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70690988965000676882063489 53018241723750507661547617)
  ·
    refine ⟨39763681292812880746160713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53018241723750507661547617 39763681292812880746160713)
    ·
      refine ⟨29822760969609660559620535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39763681292812880746160713 29822760969609660559620535)
      ·
        refine ⟨44734141454414490839430803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29822760969609660559620535 44734141454414490839430803)
        ·
          refine ⟨67101212181621736259146205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44734141454414490839430803 67101212181621736259146205)
          ·
            refine ⟨25162954568108151097179827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67101212181621736259146205 25162954568108151097179827)
            ·
              refine ⟨37744431852162226645769741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25162954568108151097179827 37744431852162226645769741)
              ·
                refine ⟨14154161944560834992163653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37744431852162226645769741 14154161944560834992163653)
                ·
                  refine ⟨2653905364605156561030685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14154161944560834992163653 2653905364605156561030685)
                  ·
                    refine ⟨995214511726933710386507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2653905364605156561030685 995214511726933710386507)
                    ·
                      rfl

theorem cell22_2907260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_2907260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907260 prefixEnd_2907260 := by exact prefixLift 2907260
  have htrace : WordTrace (prefixWord ++ tailWord_2907260) baseStart_2907260 baseEnd_2907260 := by
    simpa [prefixWord, tailWord_2907260, baseEnd_2907260] using wordTrace_append hprefix tailTrace_2907260
  have hstable : (prefixWord ++ tailWord_2907260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907260).length < 2 ^ (prefixWord ++ tailWord_2907260).sum := by decide
  have hdescent : baseEnd_2907260 < baseStart_2907260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907273 : List Nat := [1, 2, 1, 1, 4, 3, 1, 9]
def baseStart_2907273 : Nat := 118140960795 + 2907273 * 2 ^ 59
def prefixEnd_2907273 : Nat := 4983230072969 + 3 ^ 40 * 2907273 * 2
def baseEnd_2907273 : Nat := 110579884654734001090163

theorem tailTrace_2907273 : CollatzResearch.WordTrace tailWord_2907273 prefixEnd_2907273 110579884654734001090163 := by
  unfold tailWord_2907273
  simp only [CollatzResearch.WordTrace]
  refine ⟨106036957596453918543318473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70691305064302612362212315 106036957596453918543318473)
  ·
    refine ⟨79527718197340438907488855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106036957596453918543318473 79527718197340438907488855)
    ·
      refine ⟨119291577296010658361233283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79527718197340438907488855 119291577296010658361233283)
      ·
        refine ⟨178937365944015987541849925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119291577296010658361233283 178937365944015987541849925)
        ·
          refine ⟨33550756114502997664096861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178937365944015987541849925 33550756114502997664096861)
          ·
            refine ⟨12581533542938624124036323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33550756114502997664096861 12581533542938624124036323)
            ·
              refine ⟨18872300314407936186054485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12581533542938624124036323 18872300314407936186054485)
              ·
                refine ⟨110579884654734001090163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18872300314407936186054485 110579884654734001090163)
                ·
                  rfl

theorem cell22_2907273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 9].length) (baseStart_2907273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907273 prefixEnd_2907273 := by exact prefixLift 2907273
  have htrace : WordTrace (prefixWord ++ tailWord_2907273) baseStart_2907273 baseEnd_2907273 := by
    simpa [prefixWord, tailWord_2907273, baseEnd_2907273] using wordTrace_append hprefix tailTrace_2907273
  have hstable : (prefixWord ++ tailWord_2907273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907273).length < 2 ^ (prefixWord ++ tailWord_2907273).sum := by decide
  have hdescent : baseEnd_2907273 < baseStart_2907273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907290 : List Nat := [3, 1, 1, 5, 1, 1, 2, 8]
def baseStart_2907290 : Nat := 118140960795 + 2907290 * 2 ^ 59
def prefixEnd_2907290 : Nat := 4983230072969 + 3 ^ 40 * 2907290 * 2
def baseEnd_2907290 : Nat := 110580531260002625792935

theorem tailTrace_2907290 : CollatzResearch.WordTrace tailWord_2907290 prefixEnd_2907290 110580531260002625792935 := by
  unfold tailWord_2907290
  simp only [CollatzResearch.WordTrace]
  refine ⟨26509394409348082611671831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70691718424928220297791549 26509394409348082611671831)
  ·
    refine ⟨39764091614022123917507747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26509394409348082611671831 39764091614022123917507747)
    ·
      refine ⟨59646137421033185876261621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39764091614022123917507747 59646137421033185876261621)
      ·
        refine ⟨5591825383221861175899527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59646137421033185876261621 5591825383221861175899527)
        ·
          refine ⟨8387738074832791763849291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5591825383221861175899527 8387738074832791763849291)
          ·
            refine ⟨12581607112249187645773937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8387738074832791763849291 12581607112249187645773937)
            ·
              refine ⟨9436205334186890734330453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12581607112249187645773937 9436205334186890734330453)
              ·
                refine ⟨110580531260002625792935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9436205334186890734330453 110580531260002625792935)
                ·
                  rfl

theorem cell22_2907290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_2907290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907290 prefixEnd_2907290 := by exact prefixLift 2907290
  have htrace : WordTrace (prefixWord ++ tailWord_2907290) baseStart_2907290 baseEnd_2907290 := by
    simpa [prefixWord, tailWord_2907290, baseEnd_2907290] using wordTrace_append hprefix tailTrace_2907290
  have hstable : (prefixWord ++ tailWord_2907290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907290).length < 2 ^ (prefixWord ++ tailWord_2907290).sum := by decide
  have hdescent : baseEnd_2907290 < baseStart_2907290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907292 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_2907292 : Nat := 118140960795 + 2907292 * 2 ^ 59
def prefixEnd_2907292 : Nat := 4983230072969 + 3 ^ 40 * 2907292 * 2
def baseEnd_2907292 : Nat := 995225465980896293586409

theorem tailTrace_2907292 : CollatzResearch.WordTrace tailWord_2907292 prefixEnd_2907292 995225465980896293586409 := by
  unfold tailWord_2907292
  simp only [CollatzResearch.WordTrace]
  refine ⟨53018825291692542394130065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70691767055590056525506753 53018825291692542394130065)
  ·
    refine ⟨39764118968769406795597549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53018825291692542394130065 39764118968769406795597549)
    ·
      refine ⟨14911544613288527548349081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39764118968769406795597549 14911544613288527548349081)
      ·
        refine ⟨11183658459966395661261811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14911544613288527548349081 11183658459966395661261811)
        ·
          refine ⟨16775487689949593491892717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11183658459966395661261811 16775487689949593491892717)
          ·
            refine ⟨6290807883731097559459769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16775487689949593491892717 6290807883731097559459769)
            ·
              refine ⟨4718105912798323169594827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6290807883731097559459769 4718105912798323169594827)
              ·
                refine ⟨7077158869197484754392241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718105912798323169594827 7077158869197484754392241)
                ·
                  refine ⟨5307869151898113565794181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7077158869197484754392241 5307869151898113565794181)
                  ·
                    refine ⟨995225465980896293586409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5307869151898113565794181 995225465980896293586409)
                    ·
                      rfl

theorem cell22_2907292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_2907292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907292 prefixEnd_2907292 := by exact prefixLift 2907292
  have htrace : WordTrace (prefixWord ++ tailWord_2907292) baseStart_2907292 baseEnd_2907292 := by
    simpa [prefixWord, tailWord_2907292, baseEnd_2907292] using wordTrace_append hprefix tailTrace_2907292
  have hstable : (prefixWord ++ tailWord_2907292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907292).length < 2 ^ (prefixWord ++ tailWord_2907292).sum := by decide
  have hdescent : baseEnd_2907292 < baseStart_2907292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907341 : List Nat := [1, 6, 2, 2, 1, 1, 3, 6]
def baseStart_2907341 : Nat := 118140960795 + 2907341 * 2 ^ 59
def prefixEnd_2907341 : Nat := 4983230072969 + 3 ^ 40 * 2907341 * 2
def baseEnd_2907341 : Nat := 110582471075808499901251

theorem tailTrace_2907341 : CollatzResearch.WordTrace tailWord_2907341 prefixEnd_2907341 110582471075808499901251 := by
  unfold tailWord_2907341
  simp only [CollatzResearch.WordTrace]
  refine ⟨106039437760207566156793877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70692958506805044104529251 106039437760207566156793877)
  ·
    refine ⟨4970598645009729663599713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106039437760207566156793877 4970598645009729663599713)
    ·
      refine ⟨3727948983757297247699785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4970598645009729663599713 3727948983757297247699785)
      ·
        refine ⟨2795961737817972935774839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3727948983757297247699785 2795961737817972935774839)
        ·
          refine ⟨4193942606726959403662259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2795961737817972935774839 4193942606726959403662259)
          ·
            refine ⟨6290913910090439105493389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4193942606726959403662259 6290913910090439105493389)
            ·
              refine ⟨2359092716283914664560021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6290913910090439105493389 2359092716283914664560021)
              ·
                refine ⟨110582471075808499901251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2359092716283914664560021 110582471075808499901251)
                ·
                  rfl

theorem cell22_2907341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 6].length) (baseStart_2907341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907341 prefixEnd_2907341 := by exact prefixLift 2907341
  have htrace : WordTrace (prefixWord ++ tailWord_2907341) baseStart_2907341 baseEnd_2907341 := by
    simpa [prefixWord, tailWord_2907341, baseEnd_2907341] using wordTrace_append hprefix tailTrace_2907341
  have hstable : (prefixWord ++ tailWord_2907341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907341).length < 2 ^ (prefixWord ++ tailWord_2907341).sum := by decide
  have hdescent : baseEnd_2907341 < baseStart_2907341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907427 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 2, 4]
def baseStart_2907427 : Nat := 118140960795 + 2907427 * 2 ^ 59
def prefixEnd_2907427 : Nat := 4983230072969 + 3 ^ 40 * 2907427 * 2
def baseEnd_2907427 : Nat := 995271679239800941460995

theorem tailTrace_2907427 : CollatzResearch.WordTrace tailWord_2907427 prefixEnd_2907427 995271679239800941460995 := by
  unfold tailWord_2907427
  simp only [CollatzResearch.WordTrace]
  refine ⟨106042574437896002844424535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70695049625264001896283023 106042574437896002844424535)
  ·
    refine ⟨159063861656844004266636803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106042574437896002844424535 159063861656844004266636803)
    ·
      refine ⟨238595792485266006399955205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159063861656844004266636803 238595792485266006399955205)
      ·
        refine ⟨44736711090987376199991601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238595792485266006399955205 44736711090987376199991601)
        ·
          refine ⟨33552533318240532149993701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44736711090987376199991601 33552533318240532149993701)
          ·
            refine ⟨6291099997170099778123819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33552533318240532149993701 6291099997170099778123819)
            ·
              refine ⟨9436649995755149667185729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6291099997170099778123819 9436649995755149667185729)
              ·
                refine ⟨7077487496816362250389297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9436649995755149667185729 7077487496816362250389297)
                ·
                  refine ⟨5308115622612271687791973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7077487496816362250389297 5308115622612271687791973)
                  ·
                    refine ⟨995271679239800941460995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5308115622612271687791973 995271679239800941460995)
                    ·
                      rfl

theorem cell22_2907427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 4].length) (baseStart_2907427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907427 prefixEnd_2907427 := by exact prefixLift 2907427
  have htrace : WordTrace (prefixWord ++ tailWord_2907427) baseStart_2907427 baseEnd_2907427 := by
    simpa [prefixWord, tailWord_2907427, baseEnd_2907427] using wordTrace_append hprefix tailTrace_2907427
  have hstable : (prefixWord ++ tailWord_2907427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907427).length < 2 ^ (prefixWord ++ tailWord_2907427).sum := by decide
  have hdescent : baseEnd_2907427 < baseStart_2907427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907442 : List Nat := [3, 2, 1, 1, 4, 2, 2, 7]
def baseStart_2907442 : Nat := 118140960795 + 2907442 * 2 ^ 59
def prefixEnd_2907442 : Nat := 4983230072969 + 3 ^ 40 * 2907442 * 2
def baseEnd_2907442 : Nat := 110586312671816211370661

theorem tailTrace_2907442 : CollatzResearch.WordTrace tailWord_2907442 prefixEnd_2907442 110586312671816211370661 := by
  unfold tailWord_2907442
  simp only [CollatzResearch.WordTrace]
  refine ⟨26510780383210415101555145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70695414355227773604147053 26510780383210415101555145)
  ·
    refine ⟨19883085287407811326166359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26510780383210415101555145 19883085287407811326166359)
    ·
      refine ⟨29824627931111716989249539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19883085287407811326166359 29824627931111716989249539)
      ·
        refine ⟨44736941896667575483874309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29824627931111716989249539 44736941896667575483874309)
        ·
          refine ⟨8388176605625170403226433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44736941896667575483874309 8388176605625170403226433)
          ·
            refine ⟨6291132454218877802419825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8388176605625170403226433 6291132454218877802419825)
            ·
              refine ⟨4718349340664158351814869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6291132454218877802419825 4718349340664158351814869)
              ·
                refine ⟨110586312671816211370661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4718349340664158351814869 110586312671816211370661)
                ·
                  rfl

theorem cell22_2907442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_2907442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907442 prefixEnd_2907442 := by exact prefixLift 2907442
  have htrace : WordTrace (prefixWord ++ tailWord_2907442) baseStart_2907442 baseEnd_2907442 := by
    simpa [prefixWord, tailWord_2907442, baseEnd_2907442] using wordTrace_append hprefix tailTrace_2907442
  have hstable : (prefixWord ++ tailWord_2907442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907442).length < 2 ^ (prefixWord ++ tailWord_2907442).sum := by decide
  have hdescent : baseEnd_2907442 < baseStart_2907442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907491 : List Nat := [1, 1, 1, 5, 2, 3, 1, 4, 1, 3]
def baseStart_2907491 : Nat := 118140960795 + 2907491 * 2 ^ 59
def prefixEnd_2907491 : Nat := 4983230072969 + 3 ^ 40 * 2907491 * 2
def baseEnd_2907491 : Nat := 995293587747726107860799

theorem tailTrace_2907491 : CollatzResearch.WordTrace tailWord_2907491 prefixEnd_2907491 995293587747726107860799 := by
  unfold tailWord_2907491
  simp only [CollatzResearch.WordTrace]
  refine ⟨106044908709664141774754327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70696605806442761183169551 106044908709664141774754327)
  ·
    refine ⟨159067363064496212662131491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106044908709664141774754327 159067363064496212662131491)
    ·
      refine ⟨238601044596744318993197237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159067363064496212662131491 238601044596744318993197237)
      ·
        refine ⟨22368847930944779905612241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 238601044596744318993197237 22368847930944779905612241)
        ·
          refine ⟨16776635948208584929209181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22368847930944779905612241 16776635948208584929209181)
          ·
            refine ⟨6291238480578219348453443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16776635948208584929209181 6291238480578219348453443)
            ·
              refine ⟨9436857720867329022680165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6291238480578219348453443 9436857720867329022680165)
              ·
                refine ⟨1769410822662624191752531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9436857720867329022680165 1769410822662624191752531)
                ·
                  refine ⟨2654116233993936287628797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1769410822662624191752531 2654116233993936287628797)
                  ·
                    refine ⟨995293587747726107860799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2654116233993936287628797 995293587747726107860799)
                    ·
                      rfl

theorem cell22_2907491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 1, 3].length) (baseStart_2907491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907491 prefixEnd_2907491 := by exact prefixLift 2907491
  have htrace : WordTrace (prefixWord ++ tailWord_2907491) baseStart_2907491 baseEnd_2907491 := by
    simpa [prefixWord, tailWord_2907491, baseEnd_2907491] using wordTrace_append hprefix tailTrace_2907491
  have hstable : (prefixWord ++ tailWord_2907491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907491).length < 2 ^ (prefixWord ++ tailWord_2907491).sum := by decide
  have hdescent : baseEnd_2907491 < baseStart_2907491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907517 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_2907517 : Nat := 118140960795 + 2907517 * 2 ^ 59
def prefixEnd_2907517 : Nat := 4983230072969 + 3 ^ 40 * 2907517 * 2
def baseEnd_2907517 : Nat := 995302488079070706710719

theorem tailTrace_2907517 : CollatzResearch.WordTrace tailWord_2907517 prefixEnd_2907517 995302488079070706710719 := by
  unfold tailWord_2907517
  simp only [CollatzResearch.WordTrace]
  refine ⟨106045857007569948215200805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70697238005046632143467203 106045857007569948215200805)
  ·
    refine ⟨19883598188919365290350151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106045857007569948215200805 19883598188919365290350151)
    ·
      refine ⟨29825397283379047935525227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19883598188919365290350151 29825397283379047935525227)
      ·
        refine ⟨44738095925068571903287841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29825397283379047935525227 44738095925068571903287841)
        ·
          refine ⟨33553571943801428927465881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44738095925068571903287841 33553571943801428927465881)
          ·
            refine ⟨25165178957851071695599411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33553571943801428927465881 25165178957851071695599411)
            ·
              refine ⟨37747768436776607543399117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25165178957851071695599411 37747768436776607543399117)
              ·
                refine ⟨14155413163791227828774669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37747768436776607543399117 14155413163791227828774669)
                ·
                  refine ⟨5308279936421710435790501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14155413163791227828774669 5308279936421710435790501)
                  ·
                    refine ⟨995302488079070706710719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5308279936421710435790501 995302488079070706710719)
                    ·
                      rfl

theorem cell22_2907517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_2907517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907517 prefixEnd_2907517 := by exact prefixLift 2907517
  have htrace : WordTrace (prefixWord ++ tailWord_2907517) baseStart_2907517 baseEnd_2907517 := by
    simpa [prefixWord, tailWord_2907517, baseEnd_2907517] using wordTrace_append hprefix tailTrace_2907517
  have hstable : (prefixWord ++ tailWord_2907517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907517).length < 2 ^ (prefixWord ++ tailWord_2907517).sum := by decide
  have hdescent : baseEnd_2907517 < baseStart_2907517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907538 : List Nat := [3, 2, 3, 3, 1, 2, 1, 2, 5]
def baseStart_2907538 : Nat := 118140960795 + 2907538 * 2 ^ 59
def prefixEnd_2907538 : Nat := 4983230072969 + 3 ^ 40 * 2907538 * 2
def baseEnd_2907538 : Nat := 331769892269411217311885

theorem tailTrace_2907538 : CollatzResearch.WordTrace tailWord_2907538 prefixEnd_2907538 331769892269411217311885 := by
  unfold tailWord_2907538
  simp only [CollatzResearch.WordTrace]
  refine ⟨26511655735123467200428817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70697748626995912534476845 26511655735123467200428817)
  ·
    refine ⟨19883741801342600400321613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26511655735123467200428817 19883741801342600400321613)
    ·
      refine ⟨7456403175503475150120605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19883741801342600400321613 7456403175503475150120605)
      ·
        refine ⟨2796151190813803181295227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7456403175503475150120605 2796151190813803181295227)
        ·
          refine ⟨4194226786220704771942841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2796151190813803181295227 4194226786220704771942841)
          ·
            refine ⟨3145670089665528578957131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4194226786220704771942841 3145670089665528578957131)
            ·
              refine ⟨4718505134498292868435697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145670089665528578957131 4718505134498292868435697)
              ·
                refine ⟨3538878850873719651326773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4718505134498292868435697 3538878850873719651326773)
                ·
                  refine ⟨331769892269411217311885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3538878850873719651326773 331769892269411217311885)
                  ·
                    rfl

theorem cell22_2907538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_2907538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907538 prefixEnd_2907538 := by exact prefixLift 2907538
  have htrace : WordTrace (prefixWord ++ tailWord_2907538) baseStart_2907538 baseEnd_2907538 := by
    simpa [prefixWord, tailWord_2907538, baseEnd_2907538] using wordTrace_append hprefix tailTrace_2907538
  have hstable : (prefixWord ++ tailWord_2907538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907538).length < 2 ^ (prefixWord ++ tailWord_2907538).sum := by decide
  have hdescent : baseEnd_2907538 < baseStart_2907538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907547 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 10, 3]
def baseStart_2907547 : Nat := 118140960795 + 2907547 * 2 ^ 59
def prefixEnd_2907547 : Nat := 4983230072969 + 3 ^ 40 * 2907547 * 2
def baseEnd_2907547 : Nat := 995312757692160628460627

theorem tailTrace_2907547 : CollatzResearch.WordTrace tailWord_2907547 prefixEnd_2907547 995312757692160628460627 := by
  unfold tailWord_2907547
  simp only [CollatzResearch.WordTrace]
  refine ⟨106046951197461263338792895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70697967464974175559195263 106046951197461263338792895)
  ·
    refine ⟨159070426796191895008189343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106046951197461263338792895 159070426796191895008189343)
    ·
      refine ⟨238605640194287842512284015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159070426796191895008189343 238605640194287842512284015)
      ·
        refine ⟨357908460291431763768426023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238605640194287842512284015 357908460291431763768426023)
        ·
          refine ⟨536862690437147645652639035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357908460291431763768426023 536862690437147645652639035)
          ·
            refine ⟨805294035655721468478958553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536862690437147645652639035 805294035655721468478958553)
            ·
              refine ⟨603970526741791101359218915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805294035655721468478958553 603970526741791101359218915)
              ·
                refine ⟨905955790112686652038828373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603970526741791101359218915 905955790112686652038828373)
                ·
                  refine ⟨2654167353845761675895005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 905955790112686652038828373 2654167353845761675895005)
                  ·
                    refine ⟨995312757692160628460627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2654167353845761675895005 995312757692160628460627)
                    ·
                      rfl

theorem cell22_2907547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 3].length) (baseStart_2907547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907547 prefixEnd_2907547 := by exact prefixLift 2907547
  have htrace : WordTrace (prefixWord ++ tailWord_2907547) baseStart_2907547 baseEnd_2907547 := by
    simpa [prefixWord, tailWord_2907547, baseEnd_2907547] using wordTrace_append hprefix tailTrace_2907547
  have hstable : (prefixWord ++ tailWord_2907547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907547).length < 2 ^ (prefixWord ++ tailWord_2907547).sum := by decide
  have hdescent : baseEnd_2907547 < baseStart_2907547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907549 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 6]
def baseStart_2907549 : Nat := 118140960795 + 2907549 * 2 ^ 59
def prefixEnd_2907549 : Nat := 4983230072969 + 3 ^ 40 * 2907549 * 2
def baseEnd_2907549 : Nat := 331771147444344429970207

theorem tailTrace_2907549 : CollatzResearch.WordTrace tailWord_2907549 prefixEnd_2907549 331771147444344429970207 := by
  unfold tailWord_2907549
  simp only [CollatzResearch.WordTrace]
  refine ⟨106047024143454017680365701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70698016095636011786910467 106047024143454017680365701)
  ·
    refine ⟨19883817026897628315068569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106047024143454017680365701 19883817026897628315068569)
    ·
      refine ⟨14912862770173221236301427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19883817026897628315068569 14912862770173221236301427)
      ·
        refine ⟨22369294155259831854452141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14912862770173221236301427 22369294155259831854452141)
        ·
          refine ⟨8388485308222436945419553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22369294155259831854452141 8388485308222436945419553)
          ·
            refine ⟨6291363981166827709064665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8388485308222436945419553 6291363981166827709064665)
            ·
              refine ⟨4718522985875120781798499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6291363981166827709064665 4718522985875120781798499)
              ·
                refine ⟨7077784478812681172697749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718522985875120781798499 7077784478812681172697749)
                ·
                  refine ⟨331771147444344429970207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7077784478812681172697749 331771147444344429970207)
                  ·
                    rfl

theorem cell22_2907549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_2907549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907549 prefixEnd_2907549 := by exact prefixLift 2907549
  have htrace : WordTrace (prefixWord ++ tailWord_2907549) baseStart_2907549 baseEnd_2907549 := by
    simpa [prefixWord, tailWord_2907549, baseEnd_2907549] using wordTrace_append hprefix tailTrace_2907549
  have hstable : (prefixWord ++ tailWord_2907549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907549).length < 2 ^ (prefixWord ++ tailWord_2907549).sum := by decide
  have hdescent : baseEnd_2907549 < baseStart_2907549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907564 : List Nat := [2, 2, 1, 1, 1, 1, 4, 5, 2, 3]
def baseStart_2907564 : Nat := 118140960795 + 2907564 * 2 ^ 59
def prefixEnd_2907564 : Nat := 4983230072969 + 3 ^ 40 * 2907564 * 2
def baseEnd_2907564 : Nat := 995318577139578250785575

theorem tailTrace_2907564 : CollatzResearch.WordTrace tailWord_2907564 prefixEnd_2907564 995318577139578250785575 := by
  unfold tailWord_2907564
  simp only [CollatzResearch.WordTrace]
  refine ⟨53023785619199837621080873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70698380825599783494774497 53023785619199837621080873)
  ·
    refine ⟨39767839214399878215810655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53023785619199837621080873 39767839214399878215810655)
    ·
      refine ⟨59651758821599817323715983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39767839214399878215810655 59651758821599817323715983)
      ·
        refine ⟨89477638232399725985573975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59651758821599817323715983 89477638232399725985573975)
        ·
          refine ⟨134216457348599588978360963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89477638232399725985573975 134216457348599588978360963)
          ·
            refine ⟨201324686022899383467541445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134216457348599588978360963 201324686022899383467541445)
            ·
              refine ⟨37748378629293634400164021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201324686022899383467541445 37748378629293634400164021)
              ·
                refine ⟨3538910496496278225015377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37748378629293634400164021 3538910496496278225015377)
                ·
                  refine ⟨2654182872372208668761533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3538910496496278225015377 2654182872372208668761533)
                  ·
                    refine ⟨995318577139578250785575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2654182872372208668761533 995318577139578250785575)
                    ·
                      rfl

theorem cell22_2907564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_2907564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907564 prefixEnd_2907564 := by exact prefixLift 2907564
  have htrace : WordTrace (prefixWord ++ tailWord_2907564) baseStart_2907564 baseEnd_2907564 := by
    simpa [prefixWord, tailWord_2907564, baseEnd_2907564] using wordTrace_append hprefix tailTrace_2907564
  have hstable : (prefixWord ++ tailWord_2907564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907564).length < 2 ^ (prefixWord ++ tailWord_2907564).sum := by decide
  have hdescent : baseEnd_2907564 < baseStart_2907564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907669 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_2907669 : Nat := 118140960795 + 2907669 * 2 ^ 59
def prefixEnd_2907669 : Nat := 4983230072969 + 3 ^ 40 * 2907669 * 2
def baseEnd_2907669 : Nat := 995354520785392976910253

theorem tailTrace_2907669 : CollatzResearch.WordTrace tailWord_2907669 prefixEnd_2907669 995354520785392976910253 := by
  unfold tailWord_2907669
  simp only [CollatzResearch.WordTrace]
  refine ⟨106051400903019278174734061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70700933935346185449822707 106051400903019278174734061)
  ·
    refine ⟨39769275338632229315525273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106051400903019278174734061 39769275338632229315525273)
    ·
      refine ⟨29826956503974171986643955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39769275338632229315525273 29826956503974171986643955)
      ·
        refine ⟨44740434755961257979965933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29826956503974171986643955 44740434755961257979965933)
        ·
          refine ⟨16777663033485471742487225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44740434755961257979965933 16777663033485471742487225)
          ·
            refine ⟨12583247275114103806865419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16777663033485471742487225 12583247275114103806865419)
            ·
              refine ⟨18874870912671155710298129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12583247275114103806865419 18874870912671155710298129)
              ·
                refine ⟨14156153184503366782723597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18874870912671155710298129 14156153184503366782723597)
                ·
                  refine ⟨5308557444188762543521349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14156153184503366782723597 5308557444188762543521349)
                  ·
                    refine ⟨995354520785392976910253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5308557444188762543521349 995354520785392976910253)
                    ·
                      rfl

theorem cell22_2907669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_2907669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907669 prefixEnd_2907669 := by exact prefixLift 2907669
  have htrace : WordTrace (prefixWord ++ tailWord_2907669) baseStart_2907669 baseEnd_2907669 := by
    simpa [prefixWord, tailWord_2907669, baseEnd_2907669] using wordTrace_append hprefix tailTrace_2907669
  have hstable : (prefixWord ++ tailWord_2907669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907669).length < 2 ^ (prefixWord ++ tailWord_2907669).sum := by decide
  have hdescent : baseEnd_2907669 < baseStart_2907669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907699 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 1, 5]
def baseStart_2907699 : Nat := 118140960795 + 2907699 * 2 ^ 59
def prefixEnd_2907699 : Nat := 4983230072969 + 3 ^ 40 * 2907699 * 2
def baseEnd_2907699 : Nat := 995364790398482898660161

theorem tailTrace_2907699 : CollatzResearch.WordTrace tailWord_2907699 prefixEnd_2907699 995364790398482898660161 := by
  unfold tailWord_2907699
  simp only [CollatzResearch.WordTrace]
  refine ⟨106052495092910593298326151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70701663395273728865550767 106052495092910593298326151)
  ·
    refine ⟨159078742639365889947489227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106052495092910593298326151 159078742639365889947489227)
    ·
      refine ⟨238618113959048834921233841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159078742639365889947489227 238618113959048834921233841)
      ·
        refine ⟨178963585469286626190925381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238618113959048834921233841 178963585469286626190925381)
        ·
          refine ⟨33555672275491242410798509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178963585469286626190925381 33555672275491242410798509)
          ·
            refine ⟨12583377103309215904049441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33555672275491242410798509 12583377103309215904049441)
            ·
              refine ⟨9437532827481911928037081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12583377103309215904049441 9437532827481911928037081)
              ·
                refine ⟨7078149620611433946027811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9437532827481911928037081 7078149620611433946027811)
                ·
                  refine ⟨10617224430917150919041717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7078149620611433946027811 10617224430917150919041717)
                  ·
                    refine ⟨995364790398482898660161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10617224430917150919041717 995364790398482898660161)
                    ·
                      rfl

theorem cell22_2907699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 5].length) (baseStart_2907699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907699 prefixEnd_2907699 := by exact prefixLift 2907699
  have htrace : WordTrace (prefixWord ++ tailWord_2907699) baseStart_2907699 baseEnd_2907699 := by
    simpa [prefixWord, tailWord_2907699, baseEnd_2907699] using wordTrace_append hprefix tailTrace_2907699
  have hstable : (prefixWord ++ tailWord_2907699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907699).length < 2 ^ (prefixWord ++ tailWord_2907699).sum := by decide
  have hdescent : baseEnd_2907699 < baseStart_2907699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907701 : List Nat := [1, 3, 3, 1, 1, 3, 1, 5, 4]
def baseStart_2907701 : Nat := 118140960795 + 2907701 * 2 ^ 59
def prefixEnd_2907701 : Nat := 4983230072969 + 3 ^ 40 * 2907701 * 2
def baseEnd_2907701 : Nat := 331788491679785186703385

theorem tailTrace_2907701 : CollatzResearch.WordTrace tailWord_2907701 prefixEnd_2907701 331788491679785186703385 := by
  unfold tailWord_2907701
  simp only [CollatzResearch.WordTrace]
  refine ⟨106052568038903347639898957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70701712025935565093265971 106052568038903347639898957)
  ·
    refine ⟨39769713014588755364962109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106052568038903347639898957 39769713014588755364962109)
    ·
      refine ⟨14913642380470783261860791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39769713014588755364962109 14913642380470783261860791)
      ·
        refine ⟨22370463570706174892791187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14913642380470783261860791 22370463570706174892791187)
        ·
          refine ⟨33555695356059262339186781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22370463570706174892791187 33555695356059262339186781)
          ·
            refine ⟨12583385758522223377195043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33555695356059262339186781 12583385758522223377195043)
            ·
              refine ⟨18875078637783335065792565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12583385758522223377195043 18875078637783335065792565)
              ·
                refine ⟨1769538622292187662418053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18875078637783335065792565 1769538622292187662418053)
                ·
                  refine ⟨331788491679785186703385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1769538622292187662418053 331788491679785186703385)
                  ·
                    rfl

theorem cell22_2907701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_2907701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907701 prefixEnd_2907701 := by exact prefixLift 2907701
  have htrace : WordTrace (prefixWord ++ tailWord_2907701) baseStart_2907701 baseEnd_2907701 := by
    simpa [prefixWord, tailWord_2907701, baseEnd_2907701] using wordTrace_append hprefix tailTrace_2907701
  have hstable : (prefixWord ++ tailWord_2907701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907701).length < 2 ^ (prefixWord ++ tailWord_2907701).sum := by decide
  have hdescent : baseEnd_2907701 < baseStart_2907701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907703 : List Nat := [1, 1, 3, 1, 2, 6, 2, 1, 1, 4]
def baseStart_2907703 : Nat := 118140960795 + 2907703 * 2 ^ 59
def prefixEnd_2907703 : Nat := 4983230072969 + 3 ^ 40 * 2907703 * 2
def baseEnd_2907703 : Nat := 995366159680228221560149

theorem tailTrace_2907703 : CollatzResearch.WordTrace tailWord_2907703 prefixEnd_2907703 995366159680228221560149 := by
  unfold tailWord_2907703
  simp only [CollatzResearch.WordTrace]
  refine ⟨106052640984896101981471763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70701760656597401320981175 106052640984896101981471763)
  ·
    refine ⟨159078961477344152972207645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106052640984896101981471763 159078961477344152972207645)
    ·
      refine ⟨59654610554004057364577867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159078961477344152972207645 59654610554004057364577867)
      ·
        refine ⟨89481915831006086046866801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59654610554004057364577867 89481915831006086046866801)
        ·
          refine ⟨67111436873254564535150101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89481915831006086046866801 67111436873254564535150101)
          ·
            refine ⟨3145848603433807712585161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67111436873254564535150101 3145848603433807712585161)
            ·
              refine ⟨2359386452575355784438871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3145848603433807712585161 2359386452575355784438871)
              ·
                refine ⟨3539079678863033676658307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359386452575355784438871 3539079678863033676658307)
                ·
                  refine ⟨5308619518294550514987461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539079678863033676658307 5308619518294550514987461)
                  ·
                    refine ⟨995366159680228221560149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5308619518294550514987461 995366159680228221560149)
                    ·
                      rfl

theorem cell22_2907703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_2907703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907703 prefixEnd_2907703 := by exact prefixLift 2907703
  have htrace : WordTrace (prefixWord ++ tailWord_2907703) baseStart_2907703 baseEnd_2907703 := by
    simpa [prefixWord, tailWord_2907703, baseEnd_2907703] using wordTrace_append hprefix tailTrace_2907703
  have hstable : (prefixWord ++ tailWord_2907703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907703).length < 2 ^ (prefixWord ++ tailWord_2907703).sum := by decide
  have hdescent : baseEnd_2907703 < baseStart_2907703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907784 : List Nat := [2, 1, 3, 5, 2, 1, 2, 1, 2, 3]
def baseStart_2907784 : Nat := 118140960795 + 2907784 * 2 ^ 59
def prefixEnd_2907784 : Nat := 4983230072969 + 3 ^ 40 * 2907784 * 2
def baseEnd_2907784 : Nat := 995393887635571010284901

theorem tailTrace_2907784 : CollatzResearch.WordTrace tailWord_2907784 prefixEnd_2907784 995393887635571010284901 := by
  unfold tailWord_2907784
  simp only [CollatzResearch.WordTrace]
  refine ⟨53027797648801326407585203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70703730198401768543446937 53027797648801326407585203)
  ·
    refine ⟨79541696473201989611377805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53027797648801326407585203 79541696473201989611377805)
    ·
      refine ⟨29828136177450746104266677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79541696473201989611377805 29828136177450746104266677)
      ·
        refine ⟨2796387766636007447275001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29828136177450746104266677 2796387766636007447275001)
        ·
          refine ⟨2097290824977005585456251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2796387766636007447275001 2097290824977005585456251)
          ·
            refine ⟨3145936237465508378184377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097290824977005585456251 3145936237465508378184377)
            ·
              refine ⟨2359452178099131283638283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3145936237465508378184377 2359452178099131283638283)
              ·
                refine ⟨3539178267148696925457425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359452178099131283638283 3539178267148696925457425)
                ·
                  refine ⟨2654383700361522694093069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3539178267148696925457425 2654383700361522694093069)
                  ·
                    refine ⟨995393887635571010284901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2654383700361522694093069 995393887635571010284901)
                    ·
                      rfl

theorem cell22_2907784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_2907784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907784 prefixEnd_2907784 := by exact prefixLift 2907784
  have htrace : WordTrace (prefixWord ++ tailWord_2907784) baseStart_2907784 baseEnd_2907784 := by
    simpa [prefixWord, tailWord_2907784, baseEnd_2907784] using wordTrace_append hprefix tailTrace_2907784
  have hstable : (prefixWord ++ tailWord_2907784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907784).length < 2 ^ (prefixWord ++ tailWord_2907784).sum := by decide
  have hdescent : baseEnd_2907784 < baseStart_2907784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907829 : List Nat := [1, 3, 3, 3, 2, 2, 2, 2, 1, 3]
def baseStart_2907829 : Nat := 118140960795 + 2907829 * 2 ^ 59
def prefixEnd_2907829 : Nat := 4983230072969 + 3 ^ 40 * 2907829 * 2
def baseEnd_2907829 : Nat := 995409292055205892909763

theorem tailTrace_2907829 : CollatzResearch.WordTrace tailWord_2907829 prefixEnd_2907829 995409292055205892909763 := by
  unfold tailWord_2907829
  simp only [CollatzResearch.WordTrace]
  refine ⟨106057236582439625500558541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70704824388293083667039027 106057236582439625500558541)
  ·
    refine ⟨39771463718414859562709453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106057236582439625500558541 39771463718414859562709453)
    ·
      refine ⟨14914298894405572336016045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39771463718414859562709453 14914298894405572336016045)
      ·
        refine ⟨5592862085402089626006017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14914298894405572336016045 5592862085402089626006017)
        ·
          refine ⟨4194646564051567219504513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5592862085402089626006017 4194646564051567219504513)
          ·
            refine ⟨3145984923038675414628385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4194646564051567219504513 3145984923038675414628385)
            ·
              refine ⟨2359488692279006560971289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3145984923038675414628385 2359488692279006560971289)
              ·
                refine ⟨1769616519209254920728467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2359488692279006560971289 1769616519209254920728467)
                ·
                  refine ⟨2654424778813882381092701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1769616519209254920728467 2654424778813882381092701)
                  ·
                    refine ⟨995409292055205892909763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2654424778813882381092701 995409292055205892909763)
                    ·
                      rfl

theorem cell22_2907829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_2907829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907829 prefixEnd_2907829 := by exact prefixLift 2907829
  have htrace : WordTrace (prefixWord ++ tailWord_2907829) baseStart_2907829 baseEnd_2907829 := by
    simpa [prefixWord, tailWord_2907829, baseEnd_2907829] using wordTrace_append hprefix tailTrace_2907829
  have hstable : (prefixWord ++ tailWord_2907829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907829).length < 2 ^ (prefixWord ++ tailWord_2907829).sum := by decide
  have hdescent : baseEnd_2907829 < baseStart_2907829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907853 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2907853 : Nat := 118140960795 + 2907853 * 2 ^ 59
def prefixEnd_2907853 : Nat := 4983230072969 + 3 ^ 40 * 2907853 * 2
def baseEnd_2907853 : Nat := 331805835915225943436563

theorem tailTrace_2907853 : CollatzResearch.WordTrace tailWord_2907853 prefixEnd_2907853 331805835915225943436563 := by
  unfold tailWord_2907853
  simp only [CollatzResearch.WordTrace]
  refine ⟨106058111934352677599432213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70705407956235118399621475 106058111934352677599432213)
  ·
    refine ⟨4971473996922781762473385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106058111934352677599432213 4971473996922781762473385)
    ·
      refine ⟨3728605497692086321855039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4971473996922781762473385 3728605497692086321855039)
      ·
        refine ⟨5592908246538129482782559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3728605497692086321855039 5592908246538129482782559)
        ·
          refine ⟨8389362369807194224173839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5592908246538129482782559 8389362369807194224173839)
          ·
            refine ⟨12584043554710791336260759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8389362369807194224173839 12584043554710791336260759)
            ·
              refine ⟨18876065332066187004391139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12584043554710791336260759 18876065332066187004391139)
              ·
                refine ⟨28314097998099280506586709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18876065332066187004391139 28314097998099280506586709)
                ·
                  refine ⟨331805835915225943436563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28314097998099280506586709 331805835915225943436563)
                  ·
                    rfl

theorem cell22_2907853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2907853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907853 prefixEnd_2907853 := by exact prefixLift 2907853
  have htrace : WordTrace (prefixWord ++ tailWord_2907853) baseStart_2907853 baseEnd_2907853 := by
    simpa [prefixWord, tailWord_2907853, baseEnd_2907853] using wordTrace_append hprefix tailTrace_2907853
  have hstable : (prefixWord ++ tailWord_2907853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907853).length < 2 ^ (prefixWord ++ tailWord_2907853).sum := by decide
  have hdescent : baseEnd_2907853 < baseStart_2907853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907866 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_2907866 : Nat := 118140960795 + 2907866 * 2 ^ 59
def prefixEnd_2907866 : Nat := 4983230072969 + 3 ^ 40 * 2907866 * 2
def baseEnd_2907866 : Nat := 995421957911350129734649

theorem tailTrace_2907866 : CollatzResearch.WordTrace tailWord_2907866 prefixEnd_2907866 995421957911350129734649 := by
  unfold tailWord_2907866
  simp only [CollatzResearch.WordTrace]
  refine ⟨26514646520826395204913863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70705724055537053879770301 26514646520826395204913863)
  ·
    refine ⟨39771969781239592807370795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26514646520826395204913863 39771969781239592807370795)
    ·
      refine ⟨59657954671859389211056193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39771969781239592807370795 59657954671859389211056193)
      ·
        refine ⟨44743466003894541908292145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59657954671859389211056193 44743466003894541908292145)
        ·
          refine ⟨33557599502920906431219109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44743466003894541908292145 33557599502920906431219109)
          ·
            refine ⟨6292049906797669955853583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33557599502920906431219109 6292049906797669955853583)
            ·
              refine ⟨9438074860196504933780375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6292049906797669955853583 9438074860196504933780375)
              ·
                refine ⟨14157112290294757400670563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9438074860196504933780375 14157112290294757400670563)
                ·
                  refine ⟨21235668435442136101005845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14157112290294757400670563 21235668435442136101005845)
                  ·
                    refine ⟨995421957911350129734649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21235668435442136101005845 995421957911350129734649)
                    ·
                      rfl

theorem cell22_2907866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_2907866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907866 prefixEnd_2907866 := by exact prefixLift 2907866
  have htrace : WordTrace (prefixWord ++ tailWord_2907866) baseStart_2907866 baseEnd_2907866 := by
    simpa [prefixWord, tailWord_2907866, baseEnd_2907866] using wordTrace_append hprefix tailTrace_2907866
  have hstable : (prefixWord ++ tailWord_2907866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907866).length < 2 ^ (prefixWord ++ tailWord_2907866).sum := by decide
  have hdescent : baseEnd_2907866 < baseStart_2907866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907885 : List Nat := [1, 5, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_2907885 : Nat := 118140960795 + 2907885 * 2 ^ 59
def prefixEnd_2907885 : Nat := 4983230072969 + 3 ^ 40 * 2907885 * 2
def baseEnd_2907885 : Nat := 995428461999640413509591

theorem tailTrace_2907885 : CollatzResearch.WordTrace tailWord_2907885 prefixEnd_2907885 995428461999640413509591 := by
  unfold tailWord_2907885
  simp only [CollatzResearch.WordTrace]
  refine ⟨106059279070236747064597109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70706186046824498043064739 106059279070236747064597109)
  ·
    refine ⟨9943057412834695037305979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106059279070236747064597109 9943057412834695037305979)
    ·
      refine ⟨14914586119252042555958969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9943057412834695037305979 14914586119252042555958969)
      ·
        refine ⟨11185939589439031916969227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14914586119252042555958969 11185939589439031916969227)
        ·
          refine ⟨16778909384158547875453841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11185939589439031916969227 16778909384158547875453841)
          ·
            refine ⟨12584182038118910906590381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16778909384158547875453841 12584182038118910906590381)
            ·
              refine ⟨4719068264294591589971393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12584182038118910906590381 4719068264294591589971393)
              ·
                refine ⟨3539301198220943692478545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4719068264294591589971393 3539301198220943692478545)
                ·
                  refine ⟨2654475898665707769358909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3539301198220943692478545 2654475898665707769358909)
                  ·
                    refine ⟨995428461999640413509591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2654475898665707769358909 995428461999640413509591)
                    ·
                      rfl

theorem cell22_2907885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_2907885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907885 prefixEnd_2907885 := by exact prefixLift 2907885
  have htrace : WordTrace (prefixWord ++ tailWord_2907885) baseStart_2907885 baseEnd_2907885 := by
    simpa [prefixWord, tailWord_2907885, baseEnd_2907885] using wordTrace_append hprefix tailTrace_2907885
  have hstable : (prefixWord ++ tailWord_2907885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907885).length < 2 ^ (prefixWord ++ tailWord_2907885).sum := by decide
  have hdescent : baseEnd_2907885 < baseStart_2907885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907902 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2907902 : Nat := 118140960795 + 2907902 * 2 ^ 59
def prefixEnd_2907902 : Nat := 4983230072969 + 3 ^ 40 * 2907902 * 2
def baseEnd_2907902 : Nat := 995434281447058035834539

theorem tailTrace_2907902 : CollatzResearch.WordTrace tailWord_2907902 prefixEnd_2907902 995434281447058035834539 := by
  unfold tailWord_2907902
  simp only [CollatzResearch.WordTrace]
  refine ⟨13257487388896894870995745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70706599407450105978643973 13257487388896894870995745)
  ·
    refine ⟨9943115541672671153246809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13257487388896894870995745 9943115541672671153246809)
    ·
      refine ⟨7457336656254503364935107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9943115541672671153246809 7457336656254503364935107)
      ·
        refine ⟨11186004984381755047402661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7457336656254503364935107 11186004984381755047402661)
        ·
          refine ⟨2097375934571579071387999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11186004984381755047402661 2097375934571579071387999)
          ·
            refine ⟨3146063901857368607081999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097375934571579071387999 3146063901857368607081999)
            ·
              refine ⟨4719095852786052910622999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146063901857368607081999 4719095852786052910622999)
              ·
                refine ⟨7078643779179079365934499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4719095852786052910622999 7078643779179079365934499)
                ·
                  refine ⟨10617965668768619048901749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7078643779179079365934499 10617965668768619048901749)
                  ·
                    refine ⟨995434281447058035834539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10617965668768619048901749 995434281447058035834539)
                    ·
                      rfl

theorem cell22_2907902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2907902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907902 prefixEnd_2907902 := by exact prefixLift 2907902
  have htrace : WordTrace (prefixWord ++ tailWord_2907902) baseStart_2907902 baseEnd_2907902 := by
    simpa [prefixWord, tailWord_2907902, baseEnd_2907902] using wordTrace_append hprefix tailTrace_2907902
  have hstable : (prefixWord ++ tailWord_2907902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907902).length < 2 ^ (prefixWord ++ tailWord_2907902).sum := by decide
  have hdescent : baseEnd_2907902 < baseStart_2907902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907960 : List Nat := [2, 1, 2, 1, 3, 5, 2, 1, 5]
def baseStart_2907960 : Nat := 118140960795 + 2907960 * 2 ^ 59
def prefixEnd_2907960 : Nat := 4983230072969 + 3 ^ 40 * 2907960 * 2
def baseEnd_2907960 : Nat := 331818045344121739294787

theorem tailTrace_2907960 : CollatzResearch.WordTrace tailWord_2907960 prefixEnd_2907960 331818045344121739294787 := by
  unfold tailWord_2907960
  simp only [CollatzResearch.WordTrace]
  refine ⟨53031007272482517436788667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70708009696643356582384889 53031007272482517436788667)
  ·
    refine ⟨79546510908723776155183001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53031007272482517436788667 79546510908723776155183001)
    ·
      refine ⟨59659883181542832116387251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79546510908723776155183001 59659883181542832116387251)
      ·
        refine ⟨89489824772314248174580877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59659883181542832116387251 89489824772314248174580877)
        ·
          refine ⟨33558684289617843065467829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89489824772314248174580877 33558684289617843065467829)
          ·
            refine ⟨3146126652151672787387609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33558684289617843065467829 3146126652151672787387609)
            ·
              refine ⟨2359594989113754590540707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3146126652151672787387609 2359594989113754590540707)
              ·
                refine ⟨3539392483670631885811061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359594989113754590540707 3539392483670631885811061)
                ·
                  refine ⟨331818045344121739294787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3539392483670631885811061 331818045344121739294787)
                  ·
                    rfl

theorem cell22_2907960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 5].length) (baseStart_2907960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2907960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2907960 prefixEnd_2907960 := by exact prefixLift 2907960
  have htrace : WordTrace (prefixWord ++ tailWord_2907960) baseStart_2907960 baseEnd_2907960 := by
    simpa [prefixWord, tailWord_2907960, baseEnd_2907960] using wordTrace_append hprefix tailTrace_2907960
  have hstable : (prefixWord ++ tailWord_2907960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907960).length < 2 ^ (prefixWord ++ tailWord_2907960).sum := by decide
  have hdescent : baseEnd_2907960 < baseStart_2907960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908035 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 2, 4]
def baseStart_2908035 : Nat := 118140960795 + 2908035 * 2 ^ 59
def prefixEnd_2908035 : Nat := 4983230072969 + 3 ^ 40 * 2908035 * 2
def baseEnd_2908035 : Nat := 995479810065090022259131

theorem tailTrace_2908035 : CollatzResearch.WordTrace tailWord_2908035 prefixEnd_2908035 995479810065090022259131 := by
  unfold tailWord_2908035
  simp only [CollatzResearch.WordTrace]
  refine ⟨106064750019693322682557559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70709833346462215121705039 106064750019693322682557559)
  ·
    refine ⟨159097125029539984023836339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106064750019693322682557559 159097125029539984023836339)
    ·
      refine ⟨238645687544309976035754509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159097125029539984023836339 238645687544309976035754509)
      ·
        refine ⟨89492132829116241013407941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238645687544309976035754509 89492132829116241013407941)
        ·
          refine ⟨16779774905459295190013989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89492132829116241013407941 16779774905459295190013989)
          ·
            refine ⟨3146207794773617848127623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16779774905459295190013989 3146207794773617848127623)
            ·
              refine ⟨4719311692160426772191435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146207794773617848127623 4719311692160426772191435)
              ·
                refine ⟨7078967538240640158287153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4719311692160426772191435 7078967538240640158287153)
                ·
                  refine ⟨5309225653680480118715365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7078967538240640158287153 5309225653680480118715365)
                  ·
                    refine ⟨995479810065090022259131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5309225653680480118715365 995479810065090022259131)
                    ·
                      rfl

theorem cell22_2908035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 4].length) (baseStart_2908035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908035 prefixEnd_2908035 := by exact prefixLift 2908035
  have htrace : WordTrace (prefixWord ++ tailWord_2908035) baseStart_2908035 baseEnd_2908035 := by
    simpa [prefixWord, tailWord_2908035, baseEnd_2908035] using wordTrace_append hprefix tailTrace_2908035
  have hstable : (prefixWord ++ tailWord_2908035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908035).length < 2 ^ (prefixWord ++ tailWord_2908035).sum := by decide
  have hdescent : baseEnd_2908035 < baseStart_2908035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908084 : List Nat := [2, 5, 2, 1, 2, 2, 2, 6]
def baseStart_2908084 : Nat := 118140960795 + 2908084 * 2 ^ 59
def prefixEnd_2908084 : Nat := 4983230072969 + 3 ^ 40 * 2908084 * 2
def baseEnd_2908084 : Nat := 110610731529607803087109

theorem tailTrace_2908084 : CollatzResearch.WordTrace tailWord_2908084 prefixEnd_2908084 110610731529607803087109 := by
  unfold tailWord_2908084
  simp only [CollatzResearch.WordTrace]
  refine ⟨53033268598257902025545653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70711024797677202700727537 53033268598257902025545653)
  ·
    refine ⟨4971868931086678314894905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53033268598257902025545653 4971868931086678314894905)
    ·
      refine ⟨3728901698315008736171179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4971868931086678314894905 3728901698315008736171179)
      ·
        refine ⟨5593352547472513104256769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3728901698315008736171179 5593352547472513104256769)
        ·
          refine ⟨4195014410604384828192577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5593352547472513104256769 4195014410604384828192577)
          ·
            refine ⟨3146260807953288621144433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4195014410604384828192577 3146260807953288621144433)
            ·
              refine ⟨2359695605964966465858325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3146260807953288621144433 2359695605964966465858325)
              ·
                refine ⟨110610731529607803087109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2359695605964966465858325 110610731529607803087109)
                ·
                  rfl

theorem cell22_2908084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 6].length) (baseStart_2908084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908084 prefixEnd_2908084 := by exact prefixLift 2908084
  have htrace : WordTrace (prefixWord ++ tailWord_2908084) baseStart_2908084 baseEnd_2908084 := by
    simpa [prefixWord, tailWord_2908084, baseEnd_2908084] using wordTrace_append hprefix tailTrace_2908084
  have hstable : (prefixWord ++ tailWord_2908084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908084).length < 2 ^ (prefixWord ++ tailWord_2908084).sum := by decide
  have hdescent : baseEnd_2908084 < baseStart_2908084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908142 : List Nat := [4, 1, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_2908142 : Nat := 118140960795 + 2908142 * 2 ^ 59
def prefixEnd_2908142 : Nat := 4983230072969 + 3 ^ 40 * 2908142 * 2
def baseEnd_2908142 : Nat := 995516438351777409833803

theorem tailTrace_2908142 : CollatzResearch.WordTrace tailWord_2908142 prefixEnd_2908142 995516438351777409833803 := by
  unfold tailWord_2908142
  simp only [CollatzResearch.WordTrace]
  refine ⟨13258581578788209994587835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70712435086870453304468453 13258581578788209994587835)
  ·
    refine ⟨19887872368182314991881753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13258581578788209994587835 19887872368182314991881753)
    ·
      refine ⟨14915904276136736243911315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19887872368182314991881753 14915904276136736243911315)
      ·
        refine ⟨22373856414205104365866973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14915904276136736243911315 22373856414205104365866973)
        ·
          refine ⟨8390196155326914137200115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22373856414205104365866973 8390196155326914137200115)
          ·
            refine ⟨12585294232990371205800173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8390196155326914137200115 12585294232990371205800173)
            ·
              refine ⟨4719485337371389202175065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12585294232990371205800173 4719485337371389202175065)
              ·
                refine ⟨3539614003028541901631299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4719485337371389202175065 3539614003028541901631299)
                ·
                  refine ⟨5309421004542812852446949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539614003028541901631299 5309421004542812852446949)
                  ·
                    refine ⟨995516438351777409833803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5309421004542812852446949 995516438351777409833803)
                    ·
                      rfl

theorem cell22_2908142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_2908142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908142 prefixEnd_2908142 := by exact prefixLift 2908142
  have htrace : WordTrace (prefixWord ++ tailWord_2908142) baseStart_2908142 baseEnd_2908142 := by
    simpa [prefixWord, tailWord_2908142, baseEnd_2908142] using wordTrace_append hprefix tailTrace_2908142
  have hstable : (prefixWord ++ tailWord_2908142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908142).length < 2 ^ (prefixWord ++ tailWord_2908142).sum := by decide
  have hdescent : baseEnd_2908142 < baseStart_2908142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908172 : List Nat := [2, 2, 1, 2, 3, 1, 4, 2, 2, 3]
def baseStart_2908172 : Nat := 118140960795 + 2908172 * 2 ^ 59
def prefixEnd_2908172 : Nat := 4983230072969 + 3 ^ 40 * 2908172 * 2
def baseEnd_2908172 : Nat := 995526707964867331583711

theorem tailTrace_2908172 : CollatzResearch.WordTrace tailWord_2908172 prefixEnd_2908172 995526707964867331583711 := by
  unfold tailWord_2908172
  simp only [CollatzResearch.WordTrace]
  refine ⟨53034873410098497540147385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70713164546797996720196513 53034873410098497540147385)
  ·
    refine ⟨39776155057573873155110539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53034873410098497540147385 39776155057573873155110539)
    ·
      refine ⟨59664232586360809732665809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39776155057573873155110539 59664232586360809732665809)
      ·
        refine ⟨44748174439770607299499357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59664232586360809732665809 44748174439770607299499357)
        ·
          refine ⟨16780565414913977737312259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44748174439770607299499357 16780565414913977737312259)
          ·
            refine ⟨25170848122370966605968389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16780565414913977737312259 25170848122370966605968389)
            ·
              refine ⟨4719534022944556238619073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25170848122370966605968389 4719534022944556238619073)
              ·
                refine ⟨3539650517208417178964305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4719534022944556238619073 3539650517208417178964305)
                ·
                  refine ⟨2654737887906312884223229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3539650517208417178964305 2654737887906312884223229)
                  ·
                    refine ⟨995526707964867331583711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2654737887906312884223229 995526707964867331583711)
                    ·
                      rfl

theorem cell22_2908172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_2908172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908172 prefixEnd_2908172 := by exact prefixLift 2908172
  have htrace : WordTrace (prefixWord ++ tailWord_2908172) baseStart_2908172 baseEnd_2908172 := by
    simpa [prefixWord, tailWord_2908172, baseEnd_2908172] using wordTrace_append hprefix tailTrace_2908172
  have hstable : (prefixWord ++ tailWord_2908172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908172).length < 2 ^ (prefixWord ++ tailWord_2908172).sum := by decide
  have hdescent : baseEnd_2908172 < baseStart_2908172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908202 : List Nat := [3, 1, 4, 1, 2, 2, 3, 6]
def baseStart_2908202 : Nat := 118140960795 + 2908202 * 2 ^ 59
def prefixEnd_2908202 : Nat := 4983230072969 + 3 ^ 40 * 2908202 * 2
def baseEnd_2908202 : Nat := 110615219730884139259291

theorem tailTrace_2908202 : CollatzResearch.WordTrace tailWord_2908202 prefixEnd_2908202 110615219730884139259291 := by
  unfold tailWord_2908202
  simp only [CollatzResearch.WordTrace]
  refine ⟨26517710252522077550971715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70713894006725540135924573 26517710252522077550971715)
  ·
    refine ⟨39776565378783116326457573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26517710252522077550971715 39776565378783116326457573)
    ·
      refine ⟨7458106008521834311210795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39776565378783116326457573 7458106008521834311210795)
      ·
        refine ⟨11187159012782751466816193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7458106008521834311210795 11187159012782751466816193)
        ·
          refine ⟨8390369259587063600112145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11187159012782751466816193 8390369259587063600112145)
          ·
            refine ⟨6292776944690297700084109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8390369259587063600112145 6292776944690297700084109)
            ·
              refine ⟨2359791354258861637531541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6292776944690297700084109 2359791354258861637531541)
              ·
                refine ⟨110615219730884139259291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2359791354258861637531541 110615219730884139259291)
                ·
                  rfl

theorem cell22_2908202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_2908202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908202 prefixEnd_2908202 := by exact prefixLift 2908202
  have htrace : WordTrace (prefixWord ++ tailWord_2908202) baseStart_2908202 baseEnd_2908202 := by
    simpa [prefixWord, tailWord_2908202, baseEnd_2908202] using wordTrace_append hprefix tailTrace_2908202
  have hstable : (prefixWord ++ tailWord_2908202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908202).length < 2 ^ (prefixWord ++ tailWord_2908202).sum := by decide
  have hdescent : baseEnd_2908202 < baseStart_2908202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908245 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_2908245 : Nat := 118140960795 + 2908245 * 2 ^ 59
def prefixEnd_2908245 : Nat := 4983230072969 + 3 ^ 40 * 2908245 * 2
def baseEnd_2908245 : Nat := 995551697356719474508487

theorem tailTrace_2908245 : CollatzResearch.WordTrace tailWord_2908245 prefixEnd_2908245 995551697356719474508487 := by
  unfold tailWord_2908245
  simp only [CollatzResearch.WordTrace]
  refine ⟨106072409348932528547702189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70714939565955019031801459 106072409348932528547702189)
  ·
    refine ⟨39777153505849698205388321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106072409348932528547702189 39777153505849698205388321)
    ·
      refine ⟨29832865129387273654041241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39777153505849698205388321 29832865129387273654041241)
      ·
        refine ⟨22374648847040455240530931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29832865129387273654041241 22374648847040455240530931)
        ·
          refine ⟨33561973270560682860796397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22374648847040455240530931 33561973270560682860796397)
          ·
            refine ⟨12585739976460256072798649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33561973270560682860796397 12585739976460256072798649)
            ·
              refine ⟨9439304982345192054598987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12585739976460256072798649 9439304982345192054598987)
              ·
                refine ⟨14158957473517788081898481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9439304982345192054598987 14158957473517788081898481)
                ·
                  refine ⟨10619218105138341061423861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14158957473517788081898481 10619218105138341061423861)
                  ·
                    refine ⟨995551697356719474508487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10619218105138341061423861 995551697356719474508487)
                    ·
                      rfl

theorem cell22_2908245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_2908245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908245 prefixEnd_2908245 := by exact prefixLift 2908245
  have htrace : WordTrace (prefixWord ++ tailWord_2908245) baseStart_2908245 baseEnd_2908245 := by
    simpa [prefixWord, tailWord_2908245, baseEnd_2908245] using wordTrace_append hprefix tailTrace_2908245
  have hstable : (prefixWord ++ tailWord_2908245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908245).length < 2 ^ (prefixWord ++ tailWord_2908245).sum := by decide
  have hdescent : baseEnd_2908245 < baseStart_2908245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908260 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_2908260 : Nat := 118140960795 + 2908260 * 2 ^ 59
def prefixEnd_2908260 : Nat := 4983230072969 + 3 ^ 40 * 2908260 * 2
def baseEnd_2908260 : Nat := 995556832163264435383441

theorem tailTrace_2908260 : CollatzResearch.WordTrace tailWord_2908260 prefixEnd_2908260 995556832163264435383441 := by
  unfold tailWord_2908260
  simp only [CollatzResearch.WordTrace]
  refine ⟨53036478221939093054749117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70715304295918790739665489 53036478221939093054749117)
  ·
    refine ⟨19888679333227159895530919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53036478221939093054749117 19888679333227159895530919)
    ·
      refine ⟨29833018999840739843296379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19888679333227159895530919 29833018999840739843296379)
      ·
        refine ⟨44749528499761109764944569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29833018999840739843296379 44749528499761109764944569)
        ·
          refine ⟨33562146374820832323708427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44749528499761109764944569 33562146374820832323708427)
          ·
            refine ⟨50343219562231248485562641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33562146374820832323708427 50343219562231248485562641)
            ·
              refine ⟨37757414671673436364171981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50343219562231248485562641 37757414671673436364171981)
              ·
                refine ⟨14159030501877538636564493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37757414671673436364171981 14159030501877538636564493)
                ·
                  refine ⟨5309636438204076988711685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14159030501877538636564493 5309636438204076988711685)
                  ·
                    refine ⟨995556832163264435383441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5309636438204076988711685 995556832163264435383441)
                    ·
                      rfl

theorem cell22_2908260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_2908260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908260 prefixEnd_2908260 := by exact prefixLift 2908260
  have htrace : WordTrace (prefixWord ++ tailWord_2908260) baseStart_2908260 baseEnd_2908260 := by
    simpa [prefixWord, tailWord_2908260, baseEnd_2908260] using wordTrace_append hprefix tailTrace_2908260
  have hstable : (prefixWord ++ tailWord_2908260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908260).length < 2 ^ (prefixWord ++ tailWord_2908260).sum := by decide
  have hdescent : baseEnd_2908260 < baseStart_2908260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908311 : List Nat := [1, 1, 3, 3, 5, 1, 1, 2, 1, 4]
def baseStart_2908311 : Nat := 118140960795 + 2908311 * 2 ^ 59
def prefixEnd_2908311 : Nat := 4983230072969 + 3 ^ 40 * 2908311 * 2
def baseEnd_2908311 : Nat := 995574290505517302358285

theorem tailTrace_2908311 : CollatzResearch.WordTrace tailWord_2908311 prefixEnd_2908311 995574290505517302358285 := by
  unfold tailWord_2908311
  simp only [CollatzResearch.WordTrace]
  refine ⟨106074816566693421819604787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70716544377795614546403191 106074816566693421819604787)
  ·
    refine ⟨159112224850040132729407181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106074816566693421819604787 159112224850040132729407181)
    ·
      refine ⟨59667084318765049773527693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159112224850040132729407181 59667084318765049773527693)
      ·
        refine ⟨22375156619536893665072885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59667084318765049773527693 22375156619536893665072885)
        ·
          refine ⟨2097670933081583781100583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22375156619536893665072885 2097670933081583781100583)
          ·
            refine ⟨3146506399622375671650875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097670933081583781100583 3146506399622375671650875)
            ·
              refine ⟨4719759599433563507476313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146506399622375671650875 4719759599433563507476313)
              ·
                refine ⟨3539819699575172630607235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4719759599433563507476313 3539819699575172630607235)
                ·
                  refine ⟨5309729549362758945910853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539819699575172630607235 5309729549362758945910853)
                  ·
                    refine ⟨995574290505517302358285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5309729549362758945910853 995574290505517302358285)
                    ·
                      rfl

theorem cell22_2908311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_2908311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908311 prefixEnd_2908311 := by exact prefixLift 2908311
  have htrace : WordTrace (prefixWord ++ tailWord_2908311) baseStart_2908311 baseEnd_2908311 := by
    simpa [prefixWord, tailWord_2908311, baseEnd_2908311] using wordTrace_append hprefix tailTrace_2908311
  have hstable : (prefixWord ++ tailWord_2908311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908311).length < 2 ^ (prefixWord ++ tailWord_2908311).sum := by decide
  have hdescent : baseEnd_2908311 < baseStart_2908311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908320 : List Nat := [2, 1, 1, 4, 2, 2, 2, 8]
def baseStart_2908320 : Nat := 118140960795 + 2908320 * 2 ^ 59
def prefixEnd_2908320 : Nat := 4983230072969 + 3 ^ 40 * 2908320 * 2
def baseEnd_2908320 : Nat := 110619707932160475431473

theorem tailTrace_2908320 : CollatzResearch.WordTrace tailWord_2908320 prefixEnd_2908320 110619707932160475431473 := by
  unfold tailWord_2908320
  simp only [CollatzResearch.WordTrace]
  refine ⟨53037572411830408178341207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70716763215773877571121609 53037572411830408178341207)
  ·
    refine ⟨79556358617745612267511811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53037572411830408178341207 79556358617745612267511811)
    ·
      refine ⟨119334537926618418401267717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79556358617745612267511811 119334537926618418401267717)
      ·
        refine ⟨22375225861240953450237697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119334537926618418401267717 22375225861240953450237697)
        ·
          refine ⟨16781419395930715087678273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22375225861240953450237697 16781419395930715087678273)
          ·
            refine ⟨12586064546948036315758705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16781419395930715087678273 12586064546948036315758705)
            ·
              refine ⟨9439548410211027236819029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12586064546948036315758705 9439548410211027236819029)
              ·
                refine ⟨110619707932160475431473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9439548410211027236819029 110619707932160475431473)
                ·
                  rfl

theorem cell22_2908320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 8].length) (baseStart_2908320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908320 prefixEnd_2908320 := by exact prefixLift 2908320
  have htrace : WordTrace (prefixWord ++ tailWord_2908320) baseStart_2908320 baseEnd_2908320 := by
    simpa [prefixWord, tailWord_2908320, baseEnd_2908320] using wordTrace_append hprefix tailTrace_2908320
  have hstable : (prefixWord ++ tailWord_2908320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908320).length < 2 ^ (prefixWord ++ tailWord_2908320).sum := by decide
  have hdescent : baseEnd_2908320 < baseStart_2908320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908337 : List Nat := [1, 2, 2, 5, 3, 9]
def baseStart_2908337 : Nat := 118140960795 + 2908337 * 2 ^ 59
def prefixEnd_2908337 : Nat := 4983230072969 + 3 ^ 40 * 2908337 * 2
def baseEnd_2908337 : Nat := 12291150504158788903805

theorem tailTrace_2908337 : CollatzResearch.WordTrace tailWord_2908337 prefixEnd_2908337 12291150504158788903805 := by
  unfold tailWord_2908337
  simp only [CollatzResearch.WordTrace]
  refine ⟨106075764864599228260051265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70717176576399485506700843 106075764864599228260051265)
  ·
    refine ⟨79556823648449421195038449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106075764864599228260051265 79556823648449421195038449)
    ·
      refine ⟨59667617736337065896278837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79556823648449421195038449 59667617736337065896278837)
      ·
        refine ⟨5593839162781599927776141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59667617736337065896278837 5593839162781599927776141)
        ·
          refine ⟨2097689686043099972916053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5593839162781599927776141 2097689686043099972916053)
          ·
            refine ⟨12291150504158788903805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2097689686043099972916053 12291150504158788903805)
            ·
              rfl

theorem cell22_2908337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 9].length) (baseStart_2908337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908337 prefixEnd_2908337 := by exact prefixLift 2908337
  have htrace : WordTrace (prefixWord ++ tailWord_2908337) baseStart_2908337 baseEnd_2908337 := by
    simpa [prefixWord, tailWord_2908337, baseEnd_2908337] using wordTrace_append hprefix tailTrace_2908337
  have hstable : (prefixWord ++ tailWord_2908337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908337).length < 2 ^ (prefixWord ++ tailWord_2908337).sum := by decide
  have hdescent : baseEnd_2908337 < baseStart_2908337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908399 : List Nat := [1, 1, 2, 1, 6, 3, 1, 2, 5]
def baseStart_2908399 : Nat := 118140960795 + 2908399 * 2 ^ 59
def prefixEnd_2908399 : Nat := 4983230072969 + 3 ^ 40 * 2908399 * 2
def baseEnd_2908399 : Nat := 331868138234638135386005

theorem tailTrace_2908399 : CollatzResearch.WordTrace tailWord_2908399 prefixEnd_2908399 331868138234638135386005 := by
  unfold tailWord_2908399
  simp only [CollatzResearch.WordTrace]
  refine ⟨106078026190374612848808251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70718684126916408565872167 106078026190374612848808251)
  ·
    refine ⟨159117039285561919273212377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106078026190374612848808251 159117039285561919273212377)
    ·
      refine ⟨119337779464171439454909283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159117039285561919273212377 119337779464171439454909283)
      ·
        refine ⟨179006669196257159182363925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119337779464171439454909283 179006669196257159182363925)
        ·
          refine ⟨8390937618574554336673309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 179006669196257159182363925 8390937618574554336673309)
          ·
            refine ⟨3146601606965457876252491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8390937618574554336673309 3146601606965457876252491)
            ·
              refine ⟨4719902410448186814378737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146601606965457876252491 4719902410448186814378737)
              ·
                refine ⟨3539926807836140110784053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4719902410448186814378737 3539926807836140110784053)
                ·
                  refine ⟨331868138234638135386005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3539926807836140110784053 331868138234638135386005)
                  ·
                    rfl

theorem cell22_2908399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 5].length) (baseStart_2908399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908399 prefixEnd_2908399 := by exact prefixLift 2908399
  have htrace : WordTrace (prefixWord ++ tailWord_2908399) baseStart_2908399 baseEnd_2908399 := by
    simpa [prefixWord, tailWord_2908399, baseEnd_2908399] using wordTrace_append hprefix tailTrace_2908399
  have hstable : (prefixWord ++ tailWord_2908399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908399).length < 2 ^ (prefixWord ++ tailWord_2908399).sum := by decide
  have hdescent : baseEnd_2908399 < baseStart_2908399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908521 : List Nat := [1, 2, 1, 1, 1, 3, 5, 4, 1, 3]
def baseStart_2908521 : Nat := 118140960795 + 2908521 * 2 ^ 59
def prefixEnd_2908521 : Nat := 4983230072969 + 3 ^ 40 * 2908521 * 2
def baseEnd_2908521 : Nat := 995646177797146754607641

theorem tailTrace_2908521 : CollatzResearch.WordTrace tailWord_2908521 prefixEnd_2908521 995646177797146754607641 := by
  unfold tailWord_2908521
  simp only [CollatzResearch.WordTrace]
  refine ⟨106082475895932627684749417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70721650597288418456499611 106082475895932627684749417)
  ·
    refine ⟨79561856921949470763562063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106082475895932627684749417 79561856921949470763562063)
    ·
      refine ⟨119342785382924206145343095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79561856921949470763562063 119342785382924206145343095)
      ·
        refine ⟨179014178074386309218014643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119342785382924206145343095 179014178074386309218014643)
        ·
          refine ⟨268521267111579463827021965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179014178074386309218014643 268521267111579463827021965)
          ·
            refine ⟨100695475166842298935133237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268521267111579463827021965 100695475166842298935133237)
            ·
              refine ⟨9440200796891465525168741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100695475166842298935133237 9440200796891465525168741)
              ·
                refine ⟨1770037649417149785969139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9440200796891465525168741 1770037649417149785969139)
                ·
                  refine ⟨2655056474125724678953709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770037649417149785969139 2655056474125724678953709)
                  ·
                    refine ⟨995646177797146754607641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2655056474125724678953709 995646177797146754607641)
                    ·
                      rfl

theorem cell22_2908521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 1, 3].length) (baseStart_2908521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908521 prefixEnd_2908521 := by exact prefixLift 2908521
  have htrace : WordTrace (prefixWord ++ tailWord_2908521) baseStart_2908521 baseEnd_2908521 := by
    simpa [prefixWord, tailWord_2908521, baseEnd_2908521] using wordTrace_append hprefix tailTrace_2908521
  have hstable : (prefixWord ++ tailWord_2908521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908521).length < 2 ^ (prefixWord ++ tailWord_2908521).sum := by decide
  have hdescent : baseEnd_2908521 < baseStart_2908521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908579 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 6]
def baseStart_2908579 : Nat := 118140960795 + 2908579 * 2 ^ 59
def prefixEnd_2908579 : Nat := 4983230072969 + 3 ^ 40 * 2908579 * 2
def baseEnd_2908579 : Nat := 331888677460817978885821

theorem tailTrace_2908579 : CollatzResearch.WordTrace tailWord_2908579 prefixEnd_2908579 331888677460817978885821 := by
  unfold tailWord_2908579
  simp only [CollatzResearch.WordTrace]
  refine ⟨106084591329722503590360791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70723060886481669060240527 106084591329722503590360791)
  ·
    refine ⟨159126886994583755385541187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106084591329722503590360791 159126886994583755385541187)
    ·
      refine ⟨238690330491875633078311781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159126886994583755385541187 238690330491875633078311781)
      ·
        refine ⟨44754436967226681202183459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238690330491875633078311781 44754436967226681202183459)
        ·
          refine ⟨67131655450840021803275189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44754436967226681202183459 67131655450840021803275189)
          ·
            refine ⟨6293592698516252044057049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67131655450840021803275189 6293592698516252044057049)
            ·
              refine ⟨4720194523887189033042787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6293592698516252044057049 4720194523887189033042787)
              ·
                refine ⟨7080291785830783549564181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4720194523887189033042787 7080291785830783549564181)
                ·
                  refine ⟨331888677460817978885821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7080291785830783549564181 331888677460817978885821)
                  ·
                    rfl

theorem cell22_2908579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 6].length) (baseStart_2908579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908579 prefixEnd_2908579 := by exact prefixLift 2908579
  have htrace : WordTrace (prefixWord ++ tailWord_2908579) baseStart_2908579 baseEnd_2908579 := by
    simpa [prefixWord, tailWord_2908579, baseEnd_2908579] using wordTrace_append hprefix tailTrace_2908579
  have hstable : (prefixWord ++ tailWord_2908579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908579).length < 2 ^ (prefixWord ++ tailWord_2908579).sum := by decide
  have hdescent : baseEnd_2908579 < baseStart_2908579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908630 : List Nat := [5, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2908630 : Nat := 118140960795 + 2908630 * 2 ^ 59
def prefixEnd_2908630 : Nat := 4983230072969 + 3 ^ 40 * 2908630 * 2
def baseEnd_2908630 : Nat := 331894496908235601210769

theorem tailTrace_2908630 : CollatzResearch.WordTrace tailWord_2908630 prefixEnd_2908630 331894496908235601210769 := by
  unfold tailWord_2908630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6630403215783608706279209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70724300968358492866978229 6630403215783608706279209)
  ·
    refine ⟨4972802411837706529709407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6630403215783608706279209 4972802411837706529709407)
    ·
      refine ⟨7459203617756559794564111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4972802411837706529709407 7459203617756559794564111)
      ·
        refine ⟨11188805426634839691846167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7459203617756559794564111 11188805426634839691846167)
        ·
          refine ⟨16783208139952259537769251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11188805426634839691846167 16783208139952259537769251)
          ·
            refine ⟨25174812209928389306653877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16783208139952259537769251 25174812209928389306653877)
            ·
              refine ⟨2360138644680786497498801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25174812209928389306653877 2360138644680786497498801)
              ·
                refine ⟨1770103983510589873124101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2360138644680786497498801 1770103983510589873124101)
                ·
                  refine ⟨331894496908235601210769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1770103983510589873124101 331894496908235601210769)
                  ·
                    rfl

theorem cell22_2908630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2908630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908630 prefixEnd_2908630 := by exact prefixLift 2908630
  have htrace : WordTrace (prefixWord ++ tailWord_2908630) baseStart_2908630 baseEnd_2908630 := by
    simpa [prefixWord, tailWord_2908630, baseEnd_2908630] using wordTrace_append hprefix tailTrace_2908630
  have hstable : (prefixWord ++ tailWord_2908630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908630).length < 2 ^ (prefixWord ++ tailWord_2908630).sum := by decide
  have hdescent : baseEnd_2908630 < baseStart_2908630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908686 : List Nat := [4, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_2908686 : Nat := 118140960795 + 2908686 * 2 ^ 59
def prefixEnd_2908686 : Nat := 4983230072969 + 3 ^ 40 * 2908686 * 2
def baseEnd_2908686 : Nat := 331900886889713774744045

theorem tailTrace_2908686 : CollatzResearch.WordTrace tailWord_2908686 prefixEnd_2908686 331900886889713774744045 := by
  unfold tailWord_2908686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13261061742541857608063239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70725662626889907243003941 13261061742541857608063239)
  ·
    refine ⟨19891592613812786412094859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13261061742541857608063239 19891592613812786412094859)
    ·
      refine ⟨29837388920719179618142289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19891592613812786412094859 29837388920719179618142289)
      ·
        refine ⟨22378041690539384713606717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29837388920719179618142289 22378041690539384713606717)
        ·
          refine ⟨8391765633952269267602519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22378041690539384713606717 8391765633952269267602519)
          ·
            refine ⟨12587648450928403901403779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8391765633952269267602519 12587648450928403901403779)
            ·
              refine ⟨18881472676392605852105669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12587648450928403901403779 18881472676392605852105669)
              ·
                refine ⟨3540276126823613597269813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18881472676392605852105669 3540276126823613597269813)
                ·
                  refine ⟨331900886889713774744045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3540276126823613597269813 331900886889713774744045)
                  ·
                    rfl

theorem cell22_2908686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_2908686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908686 prefixEnd_2908686 := by exact prefixLift 2908686
  have htrace : WordTrace (prefixWord ++ tailWord_2908686) baseStart_2908686 baseEnd_2908686 := by
    simpa [prefixWord, tailWord_2908686, baseEnd_2908686] using wordTrace_append hprefix tailTrace_2908686
  have hstable : (prefixWord ++ tailWord_2908686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908686).length < 2 ^ (prefixWord ++ tailWord_2908686).sum := by decide
  have hdescent : baseEnd_2908686 < baseStart_2908686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908701 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2908701 : Nat := 118140960795 + 2908701 * 2 ^ 59
def prefixEnd_2908701 : Nat := 4983230072969 + 3 ^ 40 * 2908701 * 2
def baseEnd_2908701 : Nat := 995707795475686285107089

theorem tailTrace_2908701 : CollatzResearch.WordTrace tailWord_2908701 prefixEnd_2908701 995707795475686285107089 := by
  unfold tailWord_2908701
  simp only [CollatzResearch.WordTrace]
  refine ⟨106089041035280518426301957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70726027356853678950867971 106089041035280518426301957)
  ·
    refine ⟨19891695194115097204931617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106089041035280518426301957 19891695194115097204931617)
    ·
      refine ⟨14918771395586322903698713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19891695194115097204931617 14918771395586322903698713)
      ·
        refine ⟨11189078546689742177774035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14918771395586322903698713 11189078546689742177774035)
        ·
          refine ⟨16783617820034613266661053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11189078546689742177774035 16783617820034613266661053)
          ·
            refine ⟨6293856682512979974997895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16783617820034613266661053 6293856682512979974997895)
            ·
              refine ⟨9440785023769469962496843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6293856682512979974997895 9440785023769469962496843)
              ·
                refine ⟨14161177535654204943745265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9440785023769469962496843 14161177535654204943745265)
                ·
                  refine ⟨10620883151740653707808949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14161177535654204943745265 10620883151740653707808949)
                  ·
                    refine ⟨995707795475686285107089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10620883151740653707808949 995707795475686285107089)
                    ·
                      rfl

theorem cell22_2908701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2908701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908701 prefixEnd_2908701 := by exact prefixLift 2908701
  have htrace : WordTrace (prefixWord ++ tailWord_2908701) baseStart_2908701 baseEnd_2908701 := by
    simpa [prefixWord, tailWord_2908701, baseEnd_2908701] using wordTrace_append hprefix tailTrace_2908701
  have hstable : (prefixWord ++ tailWord_2908701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908701).length < 2 ^ (prefixWord ++ tailWord_2908701).sum := by decide
  have hdescent : baseEnd_2908701 < baseStart_2908701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908724 : List Nat := [2, 5, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_2908724 : Nat := 118140960795 + 2908724 * 2 ^ 59
def prefixEnd_2908724 : Nat := 4983230072969 + 3 ^ 40 * 2908724 * 2
def baseEnd_2908724 : Nat := 995715668845721891782019

theorem tailTrace_2908724 : CollatzResearch.WordTrace tailWord_2908724 prefixEnd_2908724 995715668845721891782019 := by
  unfold tailWord_2908724
  simp only [CollatzResearch.WordTrace]
  refine ⟨53044939957098596677194613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70726586609464795569592817 53044939957098596677194613)
  ·
    refine ⟨4972963120977993438486995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53044939957098596677194613 4972963120977993438486995)
    ·
      refine ⟨7459444681466990157730493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4972963120977993438486995 7459444681466990157730493)
      ·
        refine ⟨2797291755550121309148935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7459444681466990157730493 2797291755550121309148935)
        ·
          refine ⟨4195937633325181963723403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2797291755550121309148935 4195937633325181963723403)
          ·
            refine ⟨6293906449987772945585105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4195937633325181963723403 6293906449987772945585105)
            ·
              refine ⟨4720429837490829709188829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6293906449987772945585105 4720429837490829709188829)
              ·
                refine ⟨1770161189059061140945811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4720429837490829709188829 1770161189059061140945811)
                ·
                  refine ⟨2655241783588591711418717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770161189059061140945811 2655241783588591711418717)
                  ·
                    refine ⟨995715668845721891782019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2655241783588591711418717 995715668845721891782019)
                    ·
                      rfl

theorem cell22_2908724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_2908724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908724 prefixEnd_2908724 := by exact prefixLift 2908724
  have htrace : WordTrace (prefixWord ++ tailWord_2908724) baseStart_2908724 baseEnd_2908724 := by
    simpa [prefixWord, tailWord_2908724, baseEnd_2908724] using wordTrace_append hprefix tailTrace_2908724
  have hstable : (prefixWord ++ tailWord_2908724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908724).length < 2 ^ (prefixWord ++ tailWord_2908724).sum := by decide
  have hdescent : baseEnd_2908724 < baseStart_2908724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908733 : List Nat := [1, 4, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_2908733 : Nat := 118140960795 + 2908733 * 2 ^ 59
def prefixEnd_2908733 : Nat := 4983230072969 + 3 ^ 40 * 2908733 * 2
def baseEnd_2908733 : Nat := 995718749729648868306991

theorem tailTrace_2908733 : CollatzResearch.WordTrace tailWord_2908733 prefixEnd_2908733 995718749729648868306991 := by
  unfold tailWord_2908733
  simp only [CollatzResearch.WordTrace]
  refine ⟨106090208171164587891466853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70726805447443058594311235 106090208171164587891466853)
  ·
    refine ⟨19891914032093360229650035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106090208171164587891466853 19891914032093360229650035)
    ·
      refine ⟨29837871048140040344475053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19891914032093360229650035 29837871048140040344475053)
      ·
        refine ⟨11189201643052515129178145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29837871048140040344475053 11189201643052515129178145)
        ·
          refine ⟨8391901232289386346883609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11189201643052515129178145 8391901232289386346883609)
          ·
            refine ⟨6293925924217039760162707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8391901232289386346883609 6293925924217039760162707)
            ·
              refine ⟨9440888886325559640244061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6293925924217039760162707 9440888886325559640244061)
              ·
                refine ⟨3540333332372084865091523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9440888886325559640244061 3540333332372084865091523)
                ·
                  refine ⟨5310499998558127297637285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3540333332372084865091523 5310499998558127297637285)
                  ·
                    refine ⟨995718749729648868306991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5310499998558127297637285 995718749729648868306991)
                    ·
                      rfl

theorem cell22_2908733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_2908733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908733 prefixEnd_2908733 := by exact prefixLift 2908733
  have htrace : WordTrace (prefixWord ++ tailWord_2908733) baseStart_2908733 baseEnd_2908733 := by
    simpa [prefixWord, tailWord_2908733, baseEnd_2908733] using wordTrace_append hprefix tailTrace_2908733
  have hstable : (prefixWord ++ tailWord_2908733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908733).length < 2 ^ (prefixWord ++ tailWord_2908733).sum := by decide
  have hdescent : baseEnd_2908733 < baseStart_2908733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908759 : List Nat := [1, 1, 3, 2, 2, 2, 2, 9]
def baseStart_2908759 : Nat := 118140960795 + 2908759 * 2 ^ 59
def prefixEnd_2908759 : Nat := 4983230072969 + 3 ^ 40 * 2908759 * 2
def baseEnd_2908759 : Nat := 110636405562332607461879

theorem tailTrace_2908759 : CollatzResearch.WordTrace tailWord_2908759 prefixEnd_2908759 110636405562332607461879 := by
  unfold tailWord_2908759
  simp only [CollatzResearch.WordTrace]
  refine ⟨106091156469070394331913331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70727437646046929554608887 106091156469070394331913331)
  ·
    refine ⟨159136734703605591497869997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106091156469070394331913331 159136734703605591497869997)
    ·
      refine ⟨59676275513852096811701249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159136734703605591497869997 59676275513852096811701249)
      ·
        refine ⟨44757206635389072608775937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59676275513852096811701249 44757206635389072608775937)
        ·
          refine ⟨33567904976541804456581953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44757206635389072608775937 33567904976541804456581953)
          ·
            refine ⟨25175928732406353342436465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33567904976541804456581953 25175928732406353342436465)
            ·
              refine ⟨18881946549304765006827349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25175928732406353342436465 18881946549304765006827349)
              ·
                refine ⟨110636405562332607461879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18881946549304765006827349 110636405562332607461879)
                ·
                  rfl

theorem cell22_2908759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 9].length) (baseStart_2908759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908759 prefixEnd_2908759 := by exact prefixLift 2908759
  have htrace : WordTrace (prefixWord ++ tailWord_2908759) baseStart_2908759 baseEnd_2908759 := by
    simpa [prefixWord, tailWord_2908759, baseEnd_2908759] using wordTrace_append hprefix tailTrace_2908759
  have hstable : (prefixWord ++ tailWord_2908759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908759).length < 2 ^ (prefixWord ++ tailWord_2908759).sum := by decide
  have hdescent : baseEnd_2908759 < baseStart_2908759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908791 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 5, 3]
def baseStart_2908791 : Nat := 118140960795 + 2908791 * 2 ^ 59
def prefixEnd_2908791 : Nat := 4983230072969 + 3 ^ 40 * 2908791 * 2
def baseEnd_2908791 : Nat := 995738604314956050356813

theorem tailTrace_2908791 : CollatzResearch.WordTrace tailWord_2908791 prefixEnd_2908791 995738604314956050356813 := by
  unfold tailWord_2908791
  simp only [CollatzResearch.WordTrace]
  refine ⟨106092323604954463797078227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70728215736636309198052151 106092323604954463797078227)
  ·
    refine ⟨159138485407431695695617341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106092323604954463797078227 159138485407431695695617341)
    ·
      refine ⟨59676932027786885885856503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159138485407431695695617341 59676932027786885885856503)
      ·
        refine ⟨89515398041680328828784755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59676932027786885885856503 89515398041680328828784755)
        ·
          refine ⟨134273097062520493243177133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89515398041680328828784755 134273097062520493243177133)
          ·
            refine ⟨50352411398445184966191425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134273097062520493243177133 50352411398445184966191425)
            ·
              refine ⟨37764308548833888724643569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50352411398445184966191425 37764308548833888724643569)
              ·
                refine ⟨28323231411625416543482677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37764308548833888724643569 28323231411625416543482677)
                ·
                  refine ⟨2655302944839882800951501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28323231411625416543482677 2655302944839882800951501)
                  ·
                    refine ⟨995738604314956050356813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2655302944839882800951501 995738604314956050356813)
                    ·
                      rfl

theorem cell22_2908791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_2908791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908791 prefixEnd_2908791 := by exact prefixLift 2908791
  have htrace : WordTrace (prefixWord ++ tailWord_2908791) baseStart_2908791 baseEnd_2908791 := by
    simpa [prefixWord, tailWord_2908791, baseEnd_2908791] using wordTrace_append hprefix tailTrace_2908791
  have hstable : (prefixWord ++ tailWord_2908791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908791).length < 2 ^ (prefixWord ++ tailWord_2908791).sum := by decide
  have hdescent : baseEnd_2908791 < baseStart_2908791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908868 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2908868 : Nat := 118140960795 + 2908868 * 2 ^ 59
def prefixEnd_2908868 : Nat := 4983230072969 + 3 ^ 40 * 2908868 * 2
def baseEnd_2908868 : Nat := 995764962988553516181577

theorem tailTrace_2908868 : CollatzResearch.WordTrace tailWord_2908868 prefixEnd_2908868 995764962988553516181577 := by
  unfold tailWord_2908868
  simp only [CollatzResearch.WordTrace]
  refine ⟨53047566012837752973815629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70730088017117003965087505 53047566012837752973815629)
  ·
    refine ⟨19892837254814157365180861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53047566012837752973815629 19892837254814157365180861)
    ·
      refine ⟨7459813970555309011942823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19892837254814157365180861 7459813970555309011942823)
      ·
        refine ⟨11189720955832963517914235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7459813970555309011942823 11189720955832963517914235)
        ·
          refine ⟨16784581433749445276871353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11189720955832963517914235 16784581433749445276871353)
          ·
            refine ⟨12588436075312083957653515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16784581433749445276871353 12588436075312083957653515)
            ·
              refine ⟨18882654112968125936480273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12588436075312083957653515 18882654112968125936480273)
              ·
                refine ⟨14161990584726094452360205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18882654112968125936480273 14161990584726094452360205)
                ·
                  refine ⟨5310746469272285419635077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14161990584726094452360205 5310746469272285419635077)
                  ·
                    refine ⟨995764962988553516181577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5310746469272285419635077 995764962988553516181577)
                    ·
                      rfl

theorem cell22_2908868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2908868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908868 prefixEnd_2908868 := by exact prefixLift 2908868
  have htrace : WordTrace (prefixWord ++ tailWord_2908868) baseStart_2908868 baseEnd_2908868 := by
    simpa [prefixWord, tailWord_2908868, baseEnd_2908868] using wordTrace_append hprefix tailTrace_2908868
  have hstable : (prefixWord ++ tailWord_2908868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908868).length < 2 ^ (prefixWord ++ tailWord_2908868).sum := by decide
  have hdescent : baseEnd_2908868 < baseStart_2908868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
