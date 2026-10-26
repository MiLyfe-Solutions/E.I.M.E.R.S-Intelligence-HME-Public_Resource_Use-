import V185TrunkScan23Chunk0064

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_384736 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 6]
def baseStart_384736 : Nat := 118140960795 + 384736 * 2 ^ 59
def prefixEnd_384736 : Nat := 4983230072969 + 3 ^ 40 * 384736 * 2
def baseEnd_384736 : Nat := 197554493088311952330637

theorem tailTrace_384736 : CollatzResearch.WordTrace tailWord_384736 prefixEnd_384736 197554493088311952330637 := by
  unfold tailWord_384736
  simp only [CollatzResearch.WordTrace]
  refine ⟨7016237367087327261327031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9354983156116436348436041 7016237367087327261327031)
  ·
    refine ⟨10524356050630990891990547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7016237367087327261327031 10524356050630990891990547)
    ·
      refine ⟨15786534075946486337985821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10524356050630990891990547 15786534075946486337985821)
      ·
        refine ⟨5919950278479932376744683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15786534075946486337985821 5919950278479932376744683)
        ·
          refine ⟨8879925417719898565117025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5919950278479932376744683 8879925417719898565117025)
          ·
            refine ⟨6659944063289923923837769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8879925417719898565117025 6659944063289923923837769)
            ·
              refine ⟨4994958047467442942878327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6659944063289923923837769 4994958047467442942878327)
              ·
                refine ⟨7492437071201164414317491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4994958047467442942878327 7492437071201164414317491)
                ·
                  refine ⟨11238655606801746621476237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7492437071201164414317491 11238655606801746621476237)
                  ·
                    refine ⟨4214495852550654983053589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11238655606801746621476237 4214495852550654983053589)
                    ·
                      refine ⟨197554493088311952330637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4214495852550654983053589 197554493088311952330637)
                      ·
                        rfl

theorem cell23_384736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_384736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384736 prefixEnd_384736 := by exact prefixLift 384736
  have htrace : WordTrace (prefixWord ++ tailWord_384736) baseStart_384736 baseEnd_384736 := by
    simpa [prefixWord, tailWord_384736, baseEnd_384736] using wordTrace_append hprefix tailTrace_384736
  have hstable : (prefixWord ++ tailWord_384736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384736).length < 2 ^ (prefixWord ++ tailWord_384736).sum := by decide
  have hdescent : baseEnd_384736 < baseStart_384736 := by decide
  rcases family_descends (prefixWord ++ tailWord_384736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384844 : List Nat := [2, 2, 1, 3, 4, 2, 2, 1, 1, 5]
def baseStart_384844 : Nat := 118140960795 + 384844 * 2 ^ 59
def prefixEnd_384844 : Nat := 4983230072969 + 3 ^ 40 * 384844 * 2
def baseEnd_384844 : Nat := 65869982999665843260047

theorem tailTrace_384844 : CollatzResearch.WordTrace tailWord_384844 prefixEnd_384844 65869982999665843260047 := by
  unfold tailWord_384844
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018206908891694483792793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9357609211855592645057057 7018206908891694483792793)
  ·
    refine ⟨5263655181668770862844595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7018206908891694483792793 5263655181668770862844595)
    ·
      refine ⟨7895482772503156294266893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5263655181668770862844595 7895482772503156294266893)
      ·
        refine ⟨2960806039688683610350085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7895482772503156294266893 2960806039688683610350085)
        ·
          refine ⟨555151132441628176940641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2960806039688683610350085 555151132441628176940641)
          ·
            refine ⟨416363349331221132705481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555151132441628176940641 416363349331221132705481)
            ·
              refine ⟨312272511998415849529111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416363349331221132705481 312272511998415849529111)
              ·
                refine ⟨468408767997623774293667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312272511998415849529111 468408767997623774293667)
                ·
                  refine ⟨702613151996435661440501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468408767997623774293667 702613151996435661440501)
                  ·
                    refine ⟨65869982999665843260047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 702613151996435661440501 65869982999665843260047)
                    ·
                      rfl

theorem cell23_384844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_384844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384844 prefixEnd_384844 := by exact prefixLift 384844
  have htrace : WordTrace (prefixWord ++ tailWord_384844) baseStart_384844 baseEnd_384844 := by
    simpa [prefixWord, tailWord_384844, baseEnd_384844] using wordTrace_append hprefix tailTrace_384844
  have hstable : (prefixWord ++ tailWord_384844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384844).length < 2 ^ (prefixWord ++ tailWord_384844).sum := by decide
  have hdescent : baseEnd_384844 < baseStart_384844 := by decide
  rcases family_descends (prefixWord ++ tailWord_384844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384853 : List Nat := [1, 3, 2, 2, 2, 3, 10]
def baseStart_384853 : Nat := 118140960795 + 384853 * 2 ^ 59
def prefixEnd_384853 : Nat := 4983230072969 + 3 ^ 40 * 384853 * 2
def baseEnd_384853 : Nat := 2439686053393678945279

theorem tailTrace_384853 : CollatzResearch.WordTrace tailWord_384853 prefixEnd_384853 2439686053393678945279 := by
  unfold tailWord_384853
  simp only [CollatzResearch.WordTrace]
  refine ⟨14036742074750783504663213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9357828049833855669775475 14036742074750783504663213)
  ·
    refine ⟨5263778278031543814248705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14036742074750783504663213 5263778278031543814248705)
    ·
      refine ⟨3947833708523657860686529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5263778278031543814248705 3947833708523657860686529)
      ·
        refine ⟨2960875281392743395514897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3947833708523657860686529 2960875281392743395514897)
        ·
          refine ⟨2220656461044557546636173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2960875281392743395514897 2220656461044557546636173)
          ·
            refine ⟨832746172891709079988565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2220656461044557546636173 832746172891709079988565)
            ·
              refine ⟨2439686053393678945279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 832746172891709079988565 2439686053393678945279)
              ·
                rfl

theorem cell23_384853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 10].length) (baseStart_384853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384853 prefixEnd_384853 := by exact prefixLift 384853
  have htrace : WordTrace (prefixWord ++ tailWord_384853) baseStart_384853 baseEnd_384853 := by
    simpa [prefixWord, tailWord_384853, baseEnd_384853] using wordTrace_append hprefix tailTrace_384853
  have hstable : (prefixWord ++ tailWord_384853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384853).length < 2 ^ (prefixWord ++ tailWord_384853).sum := by decide
  have hdescent : baseEnd_384853 < baseStart_384853 := by decide
  rcases family_descends (prefixWord ++ tailWord_384853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384864 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 3, 2, 2]
def baseStart_384864 : Nat := 118140960795 + 384864 * 2 ^ 59
def prefixEnd_384864 : Nat := 4983230072969 + 3 ^ 40 * 384864 * 2
def baseEnd_384864 : Nat := 197620218612087451530049

theorem tailTrace_384864 : CollatzResearch.WordTrace tailWord_384864 prefixEnd_384864 197620218612087451530049 := by
  unfold tailWord_384864
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018571638855466191656823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9358095518473954922209097 7018571638855466191656823)
  ·
    refine ⟨10527857458283199287485235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7018571638855466191656823 10527857458283199287485235)
    ·
      refine ⟨15791786187424798931227853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10527857458283199287485235 15791786187424798931227853)
      ·
        refine ⟨5921919820284299599210445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15791786187424798931227853 5921919820284299599210445)
        ·
          refine ⟨2220719932606612349703917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5921919820284299599210445 2220719932606612349703917)
          ·
            refine ⟨832769974727479631138969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2220719932606612349703917 832769974727479631138969)
            ·
              refine ⟨624577481045609723354227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 832769974727479631138969 624577481045609723354227)
              ·
                refine ⟨936866221568414585031341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624577481045609723354227 936866221568414585031341)
                ·
                  refine ⟨351324833088155469386753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936866221568414585031341 351324833088155469386753)
                  ·
                    refine ⟨263493624816116602040065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 351324833088155469386753 263493624816116602040065)
                    ·
                      refine ⟨197620218612087451530049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263493624816116602040065 197620218612087451530049)
                      ·
                        rfl

theorem cell23_384864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_384864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384864 prefixEnd_384864 := by exact prefixLift 384864
  have htrace : WordTrace (prefixWord ++ tailWord_384864) baseStart_384864 baseEnd_384864 := by
    simpa [prefixWord, tailWord_384864, baseEnd_384864] using wordTrace_append hprefix tailTrace_384864
  have hstable : (prefixWord ++ tailWord_384864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384864).length < 2 ^ (prefixWord ++ tailWord_384864).sum := by decide
  have hdescent : baseEnd_384864 < baseStart_384864 := by decide
  rcases family_descends (prefixWord ++ tailWord_384864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384874 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 1, 6]
def baseStart_384874 : Nat := 118140960795 + 384874 * 2 ^ 59
def prefixEnd_384874 : Nat := 4983230072969 + 3 ^ 40 * 384874 * 2
def baseEnd_384874 : Nat := 65875117806210804135001

theorem tailTrace_384874 : CollatzResearch.WordTrace tailWord_384874 prefixEnd_384874 65875117806210804135001 := by
  unfold tailWord_384874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509377001918676022794419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9358338671783136060785117 3509377001918676022794419)
  ·
    refine ⟨5264065502878014034191629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3509377001918676022794419 5264065502878014034191629)
    ·
      refine ⟨1974024563579255262821861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5264065502878014034191629 1974024563579255262821861)
      ·
        refine ⟨370129605671110361779099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1974024563579255262821861 370129605671110361779099)
        ·
          refine ⟨555194408506665542668649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370129605671110361779099 555194408506665542668649)
          ·
            refine ⟨416395806379999157001487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555194408506665542668649 416395806379999157001487)
            ·
              refine ⟨624593709569998735502231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416395806379999157001487 624593709569998735502231)
              ·
                refine ⟨936890564354998103253347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624593709569998735502231 936890564354998103253347)
                ·
                  refine ⟨1405335846532497154880021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 936890564354998103253347 1405335846532497154880021)
                  ·
                    refine ⟨65875117806210804135001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1405335846532497154880021 65875117806210804135001)
                    ·
                      rfl

theorem cell23_384874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_384874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384874 prefixEnd_384874 := by exact prefixLift 384874
  have htrace : WordTrace (prefixWord ++ tailWord_384874) baseStart_384874 baseEnd_384874 := by
    simpa [prefixWord, tailWord_384874, baseEnd_384874] using wordTrace_append hprefix tailTrace_384874
  have hstable : (prefixWord ++ tailWord_384874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384874).length < 2 ^ (prefixWord ++ tailWord_384874).sum := by decide
  have hdescent : baseEnd_384874 < baseStart_384874 := by decide
  rcases family_descends (prefixWord ++ tailWord_384874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384913 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 4, 6]
def baseStart_384913 : Nat := 118140960795 + 384913 * 2 ^ 59
def prefixEnd_384913 : Nat := 4983230072969 + 3 ^ 40 * 384913 * 2
def baseEnd_384913 : Nat := 65881793054719253272441

theorem tailTrace_384913 : CollatzResearch.WordTrace tailWord_384913 prefixEnd_384913 65881793054719253272441 := by
  unfold tailWord_384913
  simp only [CollatzResearch.WordTrace]
  refine ⟨14038930454533413751847393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9359286969688942501231595 14038930454533413751847393)
  ·
    refine ⟨10529197840900060313885545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14038930454533413751847393 10529197840900060313885545)
    ·
      refine ⟨7896898380675045235414159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10529197840900060313885545 7896898380675045235414159)
      ·
        refine ⟨11845347571012567853121239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7896898380675045235414159 11845347571012567853121239)
        ·
          refine ⟨17768021356518851779681859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11845347571012567853121239 17768021356518851779681859)
          ·
            refine ⟨26652032034778277669522789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17768021356518851779681859 26652032034778277669522789)
            ·
              refine ⟨4997256006520927063035523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26652032034778277669522789 4997256006520927063035523)
              ·
                refine ⟨7495884009781390594553285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997256006520927063035523 7495884009781390594553285)
                ·
                  refine ⟨1405478251834010736478741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7495884009781390594553285 1405478251834010736478741)
                  ·
                    refine ⟨65881793054719253272441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1405478251834010736478741 65881793054719253272441)
                    ·
                      rfl

theorem cell23_384913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_384913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384913 prefixEnd_384913 := by exact prefixLift 384913
  have htrace : WordTrace (prefixWord ++ tailWord_384913) baseStart_384913 baseEnd_384913 := by
    simpa [prefixWord, tailWord_384913, baseEnd_384913] using wordTrace_append hprefix tailTrace_384913
  have hstable : (prefixWord ++ tailWord_384913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384913).length < 2 ^ (prefixWord ++ tailWord_384913).sum := by decide
  have hdescent : baseEnd_384913 < baseStart_384913 := by decide
  rcases family_descends (prefixWord ++ tailWord_384913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384914 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_384914 : Nat := 118140960795 + 384914 * 2 ^ 59
def prefixEnd_384914 : Nat := 4983230072969 + 3 ^ 40 * 384914 * 2
def baseEnd_384914 : Nat := 197645892644812255904819

theorem tailTrace_384914 : CollatzResearch.WordTrace tailWord_384914 prefixEnd_384914 197645892644812255904819 := by
  unfold tailWord_384914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509741731882447730658449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9359311285019860615089197 3509741731882447730658449)
  ·
    refine ⟨2632306298911835797993837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3509741731882447730658449 2632306298911835797993837)
    ·
      refine ⟨987114862091938424247689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2632306298911835797993837 987114862091938424247689)
      ·
        refine ⟨740336146568953818185767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 987114862091938424247689 740336146568953818185767)
        ·
          refine ⟨1110504219853430727278651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740336146568953818185767 1110504219853430727278651)
          ·
            refine ⟨1665756329780146090917977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110504219853430727278651 1665756329780146090917977)
            ·
              refine ⟨1249317247335109568188483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1665756329780146090917977 1249317247335109568188483)
              ·
                refine ⟨1873975871002664352282725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249317247335109568188483 1873975871002664352282725)
                ·
                  refine ⟨351370475812999566053011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1873975871002664352282725 351370475812999566053011)
                  ·
                    refine ⟨527055713719499349079517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 351370475812999566053011 527055713719499349079517)
                    ·
                      refine ⟨197645892644812255904819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 527055713719499349079517 197645892644812255904819)
                      ·
                        rfl

theorem cell23_384914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_384914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384914 prefixEnd_384914 := by exact prefixLift 384914
  have htrace : WordTrace (prefixWord ++ tailWord_384914) baseStart_384914 baseEnd_384914 := by
    simpa [prefixWord, tailWord_384914, baseEnd_384914] using wordTrace_append hprefix tailTrace_384914
  have hstable : (prefixWord ++ tailWord_384914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384914).length < 2 ^ (prefixWord ++ tailWord_384914).sum := by decide
  have hdescent : baseEnd_384914 < baseStart_384914 := by decide
  rcases family_descends (prefixWord ++ tailWord_384914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384933 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_384933 : Nat := 118140960795 + 384933 * 2 ^ 59
def prefixEnd_384933 : Nat := 4983230072969 + 3 ^ 40 * 384933 * 2
def baseEnd_384933 : Nat := 197655648777247681567231

theorem tailTrace_384933 : CollatzResearch.WordTrace tailWord_384933 prefixEnd_384933 197655648777247681567231 := by
  unfold tailWord_384933
  simp only [CollatzResearch.WordTrace]
  refine ⟨14039659914460957167575453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9359773276307304778383635 14039659914460957167575453)
  ·
    refine ⟨5264872467922858937840795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14039659914460957167575453 5264872467922858937840795)
    ·
      refine ⟨7897308701884288406761193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5264872467922858937840795 7897308701884288406761193)
      ·
        refine ⟨5922981526413216305070895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7897308701884288406761193 5922981526413216305070895)
        ·
          refine ⟨8884472289619824457606343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5922981526413216305070895 8884472289619824457606343)
          ·
            refine ⟨13326708434429736686409515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8884472289619824457606343 13326708434429736686409515)
            ·
              refine ⟨19990062651644605029614273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13326708434429736686409515 19990062651644605029614273)
              ·
                refine ⟨14992546988733453772210705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19990062651644605029614273 14992546988733453772210705)
                ·
                  refine ⟨11244410241550090329158029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14992546988733453772210705 11244410241550090329158029)
                  ·
                    refine ⟨4216653840581283873434261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11244410241550090329158029 4216653840581283873434261)
                    ·
                      refine ⟨197655648777247681567231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4216653840581283873434261 197655648777247681567231)
                      ·
                        rfl

theorem cell23_384933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_384933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384933 prefixEnd_384933 := by exact prefixLift 384933
  have htrace : WordTrace (prefixWord ++ tailWord_384933) baseStart_384933 baseEnd_384933 := by
    simpa [prefixWord, tailWord_384933, baseEnd_384933] using wordTrace_append hprefix tailTrace_384933
  have hstable : (prefixWord ++ tailWord_384933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384933).length < 2 ^ (prefixWord ++ tailWord_384933).sum := by decide
  have hdescent : baseEnd_384933 < baseStart_384933 := by decide
  rcases family_descends (prefixWord ++ tailWord_384933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384937 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 6, 2, 2]
def baseStart_384937 : Nat := 118140960795 + 384937 * 2 ^ 59
def prefixEnd_384937 : Nat := 4983230072969 + 3 ^ 40 * 384937 * 2
def baseEnd_384937 : Nat := 197657702699865665917213

theorem tailTrace_384937 : CollatzResearch.WordTrace tailWord_384937 prefixEnd_384937 197657702699865665917213 := by
  unfold tailWord_384937
  simp only [CollatzResearch.WordTrace]
  refine ⟨14039805806446465850721065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9359870537630977233814043 14039805806446465850721065)
  ·
    refine ⟨10529854354834849388040799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14039805806446465850721065 10529854354834849388040799)
    ·
      refine ⟨15794781532252274082061199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10529854354834849388040799 15794781532252274082061199)
      ·
        refine ⟨23692172298378411123091799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15794781532252274082061199 23692172298378411123091799)
        ·
          refine ⟨35538258447567616684637699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23692172298378411123091799 35538258447567616684637699)
          ·
            refine ⟨53307387671351425026956549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35538258447567616684637699 53307387671351425026956549)
            ·
              refine ⟨9995135188378392192554353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53307387671351425026956549 9995135188378392192554353)
              ·
                refine ⟨7496351391283794144415765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9995135188378392192554353 7496351391283794144415765)
                ·
                  refine ⟨351391471466427850519489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7496351391283794144415765 351391471466427850519489)
                  ·
                    refine ⟨263543603599820887889617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 351391471466427850519489 263543603599820887889617)
                    ·
                      refine ⟨197657702699865665917213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263543603599820887889617 197657702699865665917213)
                      ·
                        rfl

theorem cell23_384937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 2, 2].length) (baseStart_384937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384937 prefixEnd_384937 := by exact prefixLift 384937
  have htrace : WordTrace (prefixWord ++ tailWord_384937) baseStart_384937 baseEnd_384937 := by
    simpa [prefixWord, tailWord_384937, baseEnd_384937] using wordTrace_append hprefix tailTrace_384937
  have hstable : (prefixWord ++ tailWord_384937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384937).length < 2 ^ (prefixWord ++ tailWord_384937).sum := by decide
  have hdescent : baseEnd_384937 < baseStart_384937 := by decide
  rcases family_descends (prefixWord ++ tailWord_384937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384943 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 9]
def baseStart_384943 : Nat := 118140960795 + 384943 * 2 ^ 59
def prefixEnd_384943 : Nat := 4983230072969 + 3 ^ 40 * 384943 * 2
def baseEnd_384943 : Nat := 21962309287088071382465

theorem tailTrace_384943 : CollatzResearch.WordTrace tailWord_384943 prefixEnd_384943 21962309287088071382465 := by
  unfold tailWord_384943
  simp only [CollatzResearch.WordTrace]
  refine ⟨14040024644424728875439483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9360016429616485916959655 14040024644424728875439483)
  ·
    refine ⟨21060036966637093313159225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14040024644424728875439483 21060036966637093313159225)
    ·
      refine ⟨15795027724977819984869419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21060036966637093313159225 15795027724977819984869419)
      ·
        refine ⟨23692541587466729977304129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15795027724977819984869419 23692541587466729977304129)
        ·
          refine ⟨17769406190600047482978097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23692541587466729977304129 17769406190600047482978097)
          ·
            refine ⟨13327054642950035612233573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17769406190600047482978097 13327054642950035612233573)
            ·
              refine ⟨2498822745553131677293795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13327054642950035612233573 2498822745553131677293795)
              ·
                refine ⟨3748234118329697515940693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498822745553131677293795 3748234118329697515940693)
                ·
                  refine ⟨21962309287088071382465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3748234118329697515940693 21962309287088071382465)
                  ·
                    rfl

theorem cell23_384943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 9].length) (baseStart_384943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384943 prefixEnd_384943 := by exact prefixLift 384943
  have htrace : WordTrace (prefixWord ++ tailWord_384943) baseStart_384943 baseEnd_384943 := by
    simpa [prefixWord, tailWord_384943, baseEnd_384943] using wordTrace_append hprefix tailTrace_384943
  have hstable : (prefixWord ++ tailWord_384943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384943).length < 2 ^ (prefixWord ++ tailWord_384943).sum := by decide
  have hdescent : baseEnd_384943 < baseStart_384943 := by decide
  rcases family_descends (prefixWord ++ tailWord_384943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384963 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 6]
def baseStart_384963 : Nat := 118140960795 + 384963 * 2 ^ 59
def prefixEnd_384963 : Nat := 4983230072969 + 3 ^ 40 * 384963 * 2
def baseEnd_384963 : Nat := 197671053196882564192093

theorem tailTrace_384963 : CollatzResearch.WordTrace tailWord_384963 prefixEnd_384963 197671053196882564192093 := by
  unfold tailWord_384963
  simp only [CollatzResearch.WordTrace]
  refine ⟨14040754104352272291167543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9360502736234848194111695 14040754104352272291167543)
  ·
    refine ⟨21061131156528408436751315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14040754104352272291167543 21061131156528408436751315)
    ·
      refine ⟨31591696734792612655126973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21061131156528408436751315 31591696734792612655126973)
      ·
        refine ⟨11846886275547229745672615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31591696734792612655126973 11846886275547229745672615)
        ·
          refine ⟨17770329413320844618508923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11846886275547229745672615 17770329413320844618508923)
          ·
            refine ⟨26655494119981266927763385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17770329413320844618508923 26655494119981266927763385)
            ·
              refine ⟨19991620589985950195822539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26655494119981266927763385 19991620589985950195822539)
              ·
                refine ⟨29987430884978925293733809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19991620589985950195822539 29987430884978925293733809)
                ·
                  refine ⟨22490573163734193970300357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29987430884978925293733809 22490573163734193970300357)
                  ·
                    refine ⟨4216982468200161369431317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22490573163734193970300357 4216982468200161369431317)
                    ·
                      refine ⟨197671053196882564192093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4216982468200161369431317 197671053196882564192093)
                      ·
                        rfl

theorem cell23_384963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_384963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384963 prefixEnd_384963 := by exact prefixLift 384963
  have htrace : WordTrace (prefixWord ++ tailWord_384963) baseStart_384963 baseEnd_384963 := by
    simpa [prefixWord, tailWord_384963, baseEnd_384963] using wordTrace_append hprefix tailTrace_384963
  have hstable : (prefixWord ++ tailWord_384963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384963).length < 2 ^ (prefixWord ++ tailWord_384963).sum := by decide
  have hdescent : baseEnd_384963 < baseStart_384963 := by decide
  rcases family_descends (prefixWord ++ tailWord_384963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384994 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 7]
def baseStart_384994 : Nat := 118140960795 + 384994 * 2 ^ 59
def prefixEnd_384994 : Nat := 4983230072969 + 3 ^ 40 * 384994 * 2
def baseEnd_384994 : Nat := 21965219010796882544939

theorem tailTrace_384994 : CollatzResearch.WordTrace tailWord_384994 prefixEnd_384994 21965219010796882544939 := by
  unfold tailWord_384994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3510471191809991146386509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9361256511493309723697357 3510471191809991146386509)
  ·
    refine ⟨1316426696928746679894941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3510471191809991146386509 1316426696928746679894941)
    ·
      refine ⟨493660011348280004960603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1316426696928746679894941 493660011348280004960603)
      ·
        refine ⟨740490017022420007440905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493660011348280004960603 740490017022420007440905)
        ·
          refine ⟨555367512766815005580679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 740490017022420007440905 555367512766815005580679)
          ·
            refine ⟨833051269150222508371019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555367512766815005580679 833051269150222508371019)
            ·
              refine ⟨1249576903725333762556529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833051269150222508371019 1249576903725333762556529)
              ·
                refine ⟨937182677794000321917397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1249576903725333762556529 937182677794000321917397)
                ·
                  refine ⟨21965219010796882544939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 937182677794000321917397 21965219010796882544939)
                  ·
                    rfl

theorem cell23_384994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_384994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384994 prefixEnd_384994 := by exact prefixLift 384994
  have htrace : WordTrace (prefixWord ++ tailWord_384994) baseStart_384994 baseEnd_384994 := by
    simpa [prefixWord, tailWord_384994, baseEnd_384994] using wordTrace_append hprefix tailTrace_384994
  have hstable : (prefixWord ++ tailWord_384994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384994).length < 2 ^ (prefixWord ++ tailWord_384994).sum := by decide
  have hdescent : baseEnd_384994 < baseStart_384994 := by decide
  rcases family_descends (prefixWord ++ tailWord_384994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385127 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 1, 6]
def baseStart_385127 : Nat := 118140960795 + 385127 * 2 ^ 59
def prefixEnd_385127 : Nat := 4983230072969 + 3 ^ 40 * 385127 * 2
def baseEnd_385127 : Nat := 65918421341406640847113

theorem tailTrace_385127 : CollatzResearch.WordTrace tailWord_385127 prefixEnd_385127 65918421341406640847113 := by
  unfold tailWord_385127
  simp only [CollatzResearch.WordTrace]
  refine ⟨14046735675758128300137635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9364490450505418866758423 14046735675758128300137635)
  ·
    refine ⟨21070103513637192450206453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14046735675758128300137635 21070103513637192450206453)
    ·
      refine ⟨1975322204403486792206855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21070103513637192450206453 1975322204403486792206855)
      ·
        refine ⟨2962983306605230188310283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975322204403486792206855 2962983306605230188310283)
        ·
          refine ⟨4444474959907845282465425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2962983306605230188310283 4444474959907845282465425)
          ·
            refine ⟨3333356219930883961849069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4444474959907845282465425 3333356219930883961849069)
            ·
              refine ⟨1250008582474081485693401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3333356219930883961849069 1250008582474081485693401)
              ·
                refine ⟨937506436855561114270051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250008582474081485693401 937506436855561114270051)
                ·
                  refine ⟨1406259655283341671405077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937506436855561114270051 1406259655283341671405077)
                  ·
                    refine ⟨65918421341406640847113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1406259655283341671405077 65918421341406640847113)
                    ·
                      rfl

theorem cell23_385127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_385127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385127 prefixEnd_385127 := by exact prefixLift 385127
  have htrace : WordTrace (prefixWord ++ tailWord_385127) baseStart_385127 baseEnd_385127 := by
    simpa [prefixWord, tailWord_385127, baseEnd_385127] using wordTrace_append hprefix tailTrace_385127
  have hstable : (prefixWord ++ tailWord_385127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385127).length < 2 ^ (prefixWord ++ tailWord_385127).sum := by decide
  have hdescent : baseEnd_385127 < baseStart_385127 := by decide
  rcases family_descends (prefixWord ++ tailWord_385127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385145 : List Nat := [1, 2, 1, 3, 4, 3, 2, 2, 1, 1, 3]
def baseStart_385145 : Nat := 118140960795 + 385145 * 2 ^ 59
def prefixEnd_385145 : Nat := 4983230072969 + 3 ^ 40 * 385145 * 2
def baseEnd_385145 : Nat := 197764506676000852116257

theorem tailTrace_385145 : CollatzResearch.WordTrace tailWord_385145 prefixEnd_385145 197764506676000852116257 := by
  unfold tailWord_385145
  simp only [CollatzResearch.WordTrace]
  refine ⟨14047392189692917374292889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9364928126461944916195259 14047392189692917374292889)
  ·
    refine ⟨10535544142269688030719667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14047392189692917374292889 10535544142269688030719667)
    ·
      refine ⟨15803316213404532046079501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10535544142269688030719667 15803316213404532046079501)
      ·
        refine ⟨5926243580026699517279813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15803316213404532046079501 5926243580026699517279813)
        ·
          refine ⟨1111170671255006159489965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5926243580026699517279813 1111170671255006159489965)
          ·
            refine ⟨416689001720627309808737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1111170671255006159489965 416689001720627309808737)
            ·
              refine ⟨312516751290470482356553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416689001720627309808737 312516751290470482356553)
              ·
                refine ⟨234387563467852861767415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312516751290470482356553 234387563467852861767415)
                ·
                  refine ⟨351581345201779292651123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234387563467852861767415 351581345201779292651123)
                  ·
                    refine ⟨527372017802668938976685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 351581345201779292651123 527372017802668938976685)
                    ·
                      refine ⟨197764506676000852116257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 527372017802668938976685 197764506676000852116257)
                      ·
                        rfl

theorem cell23_385145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_385145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385145 prefixEnd_385145 := by exact prefixLift 385145
  have htrace : WordTrace (prefixWord ++ tailWord_385145) baseStart_385145 baseEnd_385145 := by
    simpa [prefixWord, tailWord_385145, baseEnd_385145] using wordTrace_append hprefix tailTrace_385145
  have hstable : (prefixWord ++ tailWord_385145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385145).length < 2 ^ (prefixWord ++ tailWord_385145).sum := by decide
  have hdescent : baseEnd_385145 < baseStart_385145 := by decide
  rcases family_descends (prefixWord ++ tailWord_385145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385157 : List Nat := [1, 3, 1, 1, 5, 1, 3, 8]
def baseStart_385157 : Nat := 118140960795 + 385157 * 2 ^ 59
def prefixEnd_385157 : Nat := 4983230072969 + 3 ^ 40 * 385157 * 2
def baseEnd_385157 : Nat := 7324839571994622413563

theorem tailTrace_385157 : CollatzResearch.WordTrace tailWord_385157 prefixEnd_385157 7324839571994622413563 := by
  unfold tailWord_385157
  simp only [CollatzResearch.WordTrace]
  refine ⟨14047829865649443423729725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9365219910432962282486483 14047829865649443423729725)
  ·
    refine ⟨5267936199618541283898647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14047829865649443423729725 5267936199618541283898647)
    ·
      refine ⟨7901904299427811925847971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5267936199618541283898647 7901904299427811925847971)
      ·
        refine ⟨11852856449141717888771957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7901904299427811925847971 11852856449141717888771957)
        ·
          refine ⟨1111205292107036052072371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11852856449141717888771957 1111205292107036052072371)
          ·
            refine ⟨1666807938160554078108557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111205292107036052072371 1666807938160554078108557)
            ·
              refine ⟨625052976810207779290709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1666807938160554078108557 625052976810207779290709)
              ·
                refine ⟨7324839571994622413563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 625052976810207779290709 7324839571994622413563)
                ·
                  rfl

theorem cell23_385157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 8].length) (baseStart_385157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385157 prefixEnd_385157 := by exact prefixLift 385157
  have htrace : WordTrace (prefixWord ++ tailWord_385157) baseStart_385157 baseEnd_385157 := by
    simpa [prefixWord, tailWord_385157, baseEnd_385157] using wordTrace_append hprefix tailTrace_385157
  have hstable : (prefixWord ++ tailWord_385157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385157).length < 2 ^ (prefixWord ++ tailWord_385157).sum := by decide
  have hdescent : baseEnd_385157 < baseStart_385157 := by decide
  rcases family_descends (prefixWord ++ tailWord_385157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385172 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_385172 : Nat := 118140960795 + 385172 * 2 ^ 59
def prefixEnd_385172 : Nat := 4983230072969 + 3 ^ 40 * 385172 * 2
def baseEnd_385172 : Nat := 197778370653672246478633

theorem tailTrace_385172 : CollatzResearch.WordTrace tailWord_385172 prefixEnd_385172 197778370653672246478633 := by
  unfold tailWord_385172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7024188480297550492762885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9365584640396733990350513 7024188480297550492762885)
  ·
    refine ⟨1317035340055790717393041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7024188480297550492762885 1317035340055790717393041)
    ·
      refine ⟨987776505041843038044781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1317035340055790717393041 987776505041843038044781)
      ·
        refine ⟨370416189390691139266793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 987776505041843038044781 370416189390691139266793)
        ·
          refine ⟨277812142043018354450095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370416189390691139266793 277812142043018354450095)
          ·
            refine ⟨416718213064527531675143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277812142043018354450095 416718213064527531675143)
            ·
              refine ⟨625077319596791297512715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416718213064527531675143 625077319596791297512715)
              ·
                refine ⟨937615979395186946269073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625077319596791297512715 937615979395186946269073)
                ·
                  refine ⟨703211984546390209701805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 937615979395186946269073 703211984546390209701805)
                  ·
                    refine ⟨263704494204896328638177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 703211984546390209701805 263704494204896328638177)
                    ·
                      refine ⟨197778370653672246478633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263704494204896328638177 197778370653672246478633)
                      ·
                        rfl

theorem cell23_385172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_385172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385172 prefixEnd_385172 := by exact prefixLift 385172
  have htrace : WordTrace (prefixWord ++ tailWord_385172) baseStart_385172 baseEnd_385172 := by
    simpa [prefixWord, tailWord_385172, baseEnd_385172] using wordTrace_append hprefix tailTrace_385172
  have hstable : (prefixWord ++ tailWord_385172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385172).length < 2 ^ (prefixWord ++ tailWord_385172).sum := by decide
  have hdescent : baseEnd_385172 < baseStart_385172 := by decide
  rcases family_descends (prefixWord ++ tailWord_385172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385184 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 3]
def baseStart_385184 : Nat := 118140960795 + 385184 * 2 ^ 59
def prefixEnd_385184 : Nat := 4983230072969 + 3 ^ 40 * 385184 * 2
def baseEnd_385184 : Nat := 197784532421526199528577

theorem tailTrace_385184 : CollatzResearch.WordTrace tailWord_385184 prefixEnd_385184 197784532421526199528577 := by
  unfold tailWord_385184
  simp only [CollatzResearch.WordTrace]
  refine ⟨7024407318275813517481303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9365876424367751356641737 7024407318275813517481303)
  ·
    refine ⟨10536610977413720276221955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7024407318275813517481303 10536610977413720276221955)
    ·
      refine ⟨15804916466120580414332933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10536610977413720276221955 15804916466120580414332933)
      ·
        refine ⟨2963421837397608827687425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15804916466120580414332933 2963421837397608827687425)
        ·
          refine ⟨2222566378048206620765569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2963421837397608827687425 2222566378048206620765569)
          ·
            refine ⟨1666924783536154965574177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2222566378048206620765569 1666924783536154965574177)
            ·
              refine ⟨1250193587652116224180633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1666924783536154965574177 1250193587652116224180633)
              ·
                refine ⟨937645190739087168135475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250193587652116224180633 937645190739087168135475)
                ·
                  refine ⟨1406467786108630752203213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937645190739087168135475 1406467786108630752203213)
                  ·
                    refine ⟨527425419790736532076205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1406467786108630752203213 527425419790736532076205)
                    ·
                      refine ⟨197784532421526199528577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 527425419790736532076205 197784532421526199528577)
                      ·
                        rfl

theorem cell23_385184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_385184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385184 prefixEnd_385184 := by exact prefixLift 385184
  have htrace : WordTrace (prefixWord ++ tailWord_385184) baseStart_385184 baseEnd_385184 := by
    simpa [prefixWord, tailWord_385184, baseEnd_385184] using wordTrace_append hprefix tailTrace_385184
  have hstable : (prefixWord ++ tailWord_385184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385184).length < 2 ^ (prefixWord ++ tailWord_385184).sum := by decide
  have hdescent : baseEnd_385184 < baseStart_385184 := by decide
  rcases family_descends (prefixWord ++ tailWord_385184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385185 : List Nat := [1, 2, 3, 3, 1, 3, 2, 3, 1, 2, 2]
def baseStart_385185 : Nat := 118140960795 + 385185 * 2 ^ 59
def prefixEnd_385185 : Nat := 4983230072969 + 3 ^ 40 * 385185 * 2
def baseEnd_385185 : Nat := 197785045902180695616073

theorem tailTrace_385185 : CollatzResearch.WordTrace tailWord_385185 prefixEnd_385185 197785045902180695616073 := by
  unfold tailWord_385185
  simp only [CollatzResearch.WordTrace]
  refine ⟨14048851109548004205749009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9365900739698669470499339 14048851109548004205749009)
  ·
    refine ⟨10536638332161003154311757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14048851109548004205749009 10536638332161003154311757)
    ·
      refine ⟨3951239374560376182866909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10536638332161003154311757 3951239374560376182866909)
      ·
        refine ⟨1481714765460141068575091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3951239374560376182866909 1481714765460141068575091)
        ·
          refine ⟨2222572148190211602862637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481714765460141068575091 2222572148190211602862637)
          ·
            refine ⟨833464555571329351073489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2222572148190211602862637 833464555571329351073489)
            ·
              refine ⟨625098416678497013305117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 833464555571329351073489 625098416678497013305117)
              ·
                refine ⟨234411906254436379989419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 625098416678497013305117 234411906254436379989419)
                ·
                  refine ⟨351617859381654569984129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234411906254436379989419 351617859381654569984129)
                  ·
                    refine ⟨263713394536240927488097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 351617859381654569984129 263713394536240927488097)
                    ·
                      refine ⟨197785045902180695616073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263713394536240927488097 197785045902180695616073)
                      ·
                        rfl

theorem cell23_385185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_385185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385185 prefixEnd_385185 := by exact prefixLift 385185
  have htrace : WordTrace (prefixWord ++ tailWord_385185) baseStart_385185 baseEnd_385185 := by
    simpa [prefixWord, tailWord_385185, baseEnd_385185] using wordTrace_append hprefix tailTrace_385185
  have hstable : (prefixWord ++ tailWord_385185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385185).length < 2 ^ (prefixWord ++ tailWord_385185).sum := by decide
  have hdescent : baseEnd_385185 < baseStart_385185 := by decide
  rcases family_descends (prefixWord ++ tailWord_385185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385227 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 5]
def baseStart_385227 : Nat := 118140960795 + 385227 * 2 ^ 59
def prefixEnd_385227 : Nat := 4983230072969 + 3 ^ 40 * 385227 * 2
def baseEnd_385227 : Nat := 197806612089669531290879

theorem tailTrace_385227 : CollatzResearch.WordTrace tailWord_385227 prefixEnd_385227 197806612089669531290879 := by
  unfold tailWord_385227
  simp only [CollatzResearch.WordTrace]
  refine ⟨14050382975395845378777935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9366921983597230252518623 14050382975395845378777935)
  ·
    refine ⟨21075574463093768068166903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14050382975395845378777935 21075574463093768068166903)
    ·
      refine ⟨31613361694640652102250355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21075574463093768068166903 31613361694640652102250355)
      ·
        refine ⟨47420042541960978153375533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31613361694640652102250355 47420042541960978153375533)
        ·
          refine ⟨17782515953235366807515825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47420042541960978153375533 17782515953235366807515825)
          ·
            refine ⟨13336886964926525105636869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17782515953235366807515825 13336886964926525105636869)
            ·
              refine ⟨2500666305923723457306913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13336886964926525105636869 2500666305923723457306913)
              ·
                refine ⟨1875499729442792592980185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2500666305923723457306913 1875499729442792592980185)
                ·
                  refine ⟨1406624797082094444735139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1875499729442792592980185 1406624797082094444735139)
                  ·
                    refine ⟨2109937195623141667102709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1406624797082094444735139 2109937195623141667102709)
                    ·
                      refine ⟨197806612089669531290879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2109937195623141667102709 197806612089669531290879)
                      ·
                        rfl

theorem cell23_385227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 5].length) (baseStart_385227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385227 prefixEnd_385227 := by exact prefixLift 385227
  have htrace : WordTrace (prefixWord ++ tailWord_385227) baseStart_385227 baseEnd_385227 := by
    simpa [prefixWord, tailWord_385227, baseEnd_385227] using wordTrace_append hprefix tailTrace_385227
  have hstable : (prefixWord ++ tailWord_385227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385227).length < 2 ^ (prefixWord ++ tailWord_385227).sum := by decide
  have hdescent : baseEnd_385227 < baseStart_385227 := by decide
  rcases family_descends (prefixWord ++ tailWord_385227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385241 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 4, 2, 2]
def baseStart_385241 : Nat := 118140960795 + 385241 * 2 ^ 59
def prefixEnd_385241 : Nat := 4983230072969 + 3 ^ 40 * 385241 * 2
def baseEnd_385241 : Nat := 197813800818832476515815

theorem tailTrace_385241 : CollatzResearch.WordTrace tailWord_385241 prefixEnd_385241 197813800818832476515815 := by
  unfold tailWord_385241
  simp only [CollatzResearch.WordTrace]
  refine ⟨14050893597345125769787577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9367262398230083846525051 14050893597345125769787577)
  ·
    refine ⟨10538170198008844327340683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14050893597345125769787577 10538170198008844327340683)
    ·
      refine ⟨15807255297013266491011025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10538170198008844327340683 15807255297013266491011025)
      ·
        refine ⟨11855441472759949868258269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15807255297013266491011025 11855441472759949868258269)
        ·
          refine ⟨4445790552284981200596851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11855441472759949868258269 4445790552284981200596851)
          ·
            refine ⟨6668685828427471800895277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445790552284981200596851 6668685828427471800895277)
            ·
              refine ⟨2500757185660301925335729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6668685828427471800895277 2500757185660301925335729)
              ·
                refine ⟨1875567889245226444001797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2500757185660301925335729 1875567889245226444001797)
                ·
                  refine ⟨351668979233479958250337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1875567889245226444001797 351668979233479958250337)
                  ·
                    refine ⟨263751734425109968687753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 351668979233479958250337 263751734425109968687753)
                    ·
                      refine ⟨197813800818832476515815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263751734425109968687753 197813800818832476515815)
                      ·
                        rfl

theorem cell23_385241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 2, 2].length) (baseStart_385241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385241 prefixEnd_385241 := by exact prefixLift 385241
  have htrace : WordTrace (prefixWord ++ tailWord_385241) baseStart_385241 baseEnd_385241 := by
    simpa [prefixWord, tailWord_385241, baseEnd_385241] using wordTrace_append hprefix tailTrace_385241
  have hstable : (prefixWord ++ tailWord_385241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385241).length < 2 ^ (prefixWord ++ tailWord_385241).sum := by decide
  have hdescent : baseEnd_385241 < baseStart_385241 := by decide
  rcases family_descends (prefixWord ++ tailWord_385241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385258 : List Nat := [3, 1, 3, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_385258 : Nat := 118140960795 + 385258 * 2 ^ 59
def prefixEnd_385258 : Nat := 4983230072969 + 3 ^ 40 * 385258 * 2
def baseEnd_385258 : Nat := 197822529989958910003237

theorem tailTrace_385258 : CollatzResearch.WordTrace tailWord_385258 prefixEnd_385258 197822529989958910003237 := by
  unfold tailWord_385258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3512878409570884418289107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9367675758855691782104285 3512878409570884418289107)
  ·
    refine ⟨5269317614356326627433661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3512878409570884418289107 5269317614356326627433661)
    ·
      refine ⟨1975994105383622485287623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5269317614356326627433661 1975994105383622485287623)
      ·
        refine ⟨2963991158075433727931435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975994105383622485287623 2963991158075433727931435)
        ·
          refine ⟨4445986737113150591897153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2963991158075433727931435 4445986737113150591897153)
          ·
            refine ⟨3334490052834862943922865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4445986737113150591897153 3334490052834862943922865)
            ·
              refine ⟨2500867539626147207942149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3334490052834862943922865 2500867539626147207942149)
              ·
                refine ⟨468912663679902601489153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2500867539626147207942149 468912663679902601489153)
                ·
                  refine ⟨351684497759926951116865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468912663679902601489153 351684497759926951116865)
                  ·
                    refine ⟨263763373319945213337649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 351684497759926951116865 263763373319945213337649)
                    ·
                      refine ⟨197822529989958910003237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263763373319945213337649 197822529989958910003237)
                      ·
                        rfl

theorem cell23_385258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_385258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385258 prefixEnd_385258 := by exact prefixLift 385258
  have htrace : WordTrace (prefixWord ++ tailWord_385258) baseStart_385258 baseEnd_385258 := by
    simpa [prefixWord, tailWord_385258, baseEnd_385258] using wordTrace_append hprefix tailTrace_385258
  have hstable : (prefixWord ++ tailWord_385258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385258).length < 2 ^ (prefixWord ++ tailWord_385258).sum := by decide
  have hdescent : baseEnd_385258 < baseStart_385258 := by decide
  rcases family_descends (prefixWord ++ tailWord_385258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385264 : List Nat := [2, 1, 1, 1, 3, 1, 1, 8, 5]
def baseStart_385264 : Nat := 118140960795 + 385264 * 2 ^ 59
def prefixEnd_385264 : Nat := 4983230072969 + 3 ^ 40 * 385264 * 2
def baseEnd_385264 : Nat := 21980623430431765169801

theorem tailTrace_385264 : CollatzResearch.WordTrace tailWord_385264 prefixEnd_385264 21980623430431765169801 := by
  unfold tailWord_385264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7025866238130900348937423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9367821650841200465249897 7025866238130900348937423)
  ·
    refine ⟨10538799357196350523406135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7025866238130900348937423 10538799357196350523406135)
    ·
      refine ⟨15808199035794525785109203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10538799357196350523406135 15808199035794525785109203)
      ·
        refine ⟨23712298553691788677663805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15808199035794525785109203 23712298553691788677663805)
        ·
          refine ⟨8892111957634420754123927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23712298553691788677663805 8892111957634420754123927)
          ·
            refine ⟨13338167936451631131185891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8892111957634420754123927 13338167936451631131185891)
            ·
              refine ⟨20007251904677446696778837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13338167936451631131185891 20007251904677446696778837)
              ·
                refine ⟨234459983257938828477877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 20007251904677446696778837 234459983257938828477877)
                ·
                  refine ⟨21980623430431765169801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 234459983257938828477877 21980623430431765169801)
                  ·
                    rfl

theorem cell23_385264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 5].length) (baseStart_385264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385264 prefixEnd_385264 := by exact prefixLift 385264
  have htrace : WordTrace (prefixWord ++ tailWord_385264) baseStart_385264 baseEnd_385264 := by
    simpa [prefixWord, tailWord_385264, baseEnd_385264] using wordTrace_append hprefix tailTrace_385264
  have hstable : (prefixWord ++ tailWord_385264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385264).length < 2 ^ (prefixWord ++ tailWord_385264).sum := by decide
  have hdescent : baseEnd_385264 < baseStart_385264 := by decide
  rcases family_descends (prefixWord ++ tailWord_385264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385277 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_385277 : Nat := 118140960795 + 385277 * 2 ^ 59
def prefixEnd_385277 : Nat := 4983230072969 + 3 ^ 40 * 385277 * 2
def baseEnd_385277 : Nat := 65944095374131445221883

theorem tailTrace_385277 : CollatzResearch.WordTrace tailWord_385277 prefixEnd_385277 65944095374131445221883 := by
  unfold tailWord_385277
  simp only [CollatzResearch.WordTrace]
  refine ⟨14052206625214703918098085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9368137750143135945398723 14052206625214703918098085)
  ·
    refine ⟨2634788742227756984643391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14052206625214703918098085 2634788742227756984643391)
    ·
      refine ⟨3952183113341635476965087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2634788742227756984643391 3952183113341635476965087)
      ·
        refine ⟨5928274670012453215447631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3952183113341635476965087 5928274670012453215447631)
        ·
          refine ⟨8892412005018679823171447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5928274670012453215447631 8892412005018679823171447)
          ·
            refine ⟨13338618007528019734757171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8892412005018679823171447 13338618007528019734757171)
            ·
              refine ⟨20007927011292029602135757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13338618007528019734757171 20007927011292029602135757)
              ·
                refine ⟨7502972629234511100800909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20007927011292029602135757 7502972629234511100800909)
                ·
                  refine ⟨2813614735962941662800341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7502972629234511100800909 2813614735962941662800341)
                  ·
                    refine ⟨65944095374131445221883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2813614735962941662800341 65944095374131445221883)
                    ·
                      rfl

theorem cell23_385277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_385277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385277 prefixEnd_385277 := by exact prefixLift 385277
  have htrace : WordTrace (prefixWord ++ tailWord_385277) baseStart_385277 baseEnd_385277 := by
    simpa [prefixWord, tailWord_385277, baseEnd_385277] using wordTrace_append hprefix tailTrace_385277
  have hstable : (prefixWord ++ tailWord_385277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385277).length < 2 ^ (prefixWord ++ tailWord_385277).sum := by decide
  have hdescent : baseEnd_385277 < baseStart_385277 := by decide
  rcases family_descends (prefixWord ++ tailWord_385277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385331 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 2, 4, 2]
def baseStart_385331 : Nat := 118140960795 + 385331 * 2 ^ 59
def prefixEnd_385331 : Nat := 4983230072969 + 3 ^ 40 * 385331 * 2
def baseEnd_385331 : Nat := 197860014077737124390401

theorem tailTrace_385331 : CollatzResearch.WordTrace tailWord_385331 prefixEnd_385331 197860014077737124390401 := by
  unfold tailWord_385331
  simp only [CollatzResearch.WordTrace]
  refine ⟨14054176167019071140563847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9369450778012714093709231 14054176167019071140563847)
  ·
    refine ⟨21081264250528606710845771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14054176167019071140563847 21081264250528606710845771)
    ·
      refine ⟨31621896375792910066268657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21081264250528606710845771 31621896375792910066268657)
      ·
        refine ⟨23716422281844682549701493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31621896375792910066268657 23716422281844682549701493)
        ·
          refine ⟨2223414588922938989034515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23716422281844682549701493 2223414588922938989034515)
          ·
            refine ⟨3335121883384408483551773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223414588922938989034515 3335121883384408483551773)
            ·
              refine ⟨1250670706269153181331915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3335121883384408483551773 1250670706269153181331915)
              ·
                refine ⟨1876006059403729771997873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250670706269153181331915 1876006059403729771997873)
                ·
                  refine ⟨1407004544552797328998405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1876006059403729771997873 1407004544552797328998405)
                  ·
                    refine ⟨263813352103649499187201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1407004544552797328998405 263813352103649499187201)
                    ·
                      refine ⟨197860014077737124390401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263813352103649499187201 197860014077737124390401)
                      ·
                        rfl

theorem cell23_385331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 4, 2].length) (baseStart_385331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385331 prefixEnd_385331 := by exact prefixLift 385331
  have htrace : WordTrace (prefixWord ++ tailWord_385331) baseStart_385331 baseEnd_385331 := by
    simpa [prefixWord, tailWord_385331, baseEnd_385331] using wordTrace_append hprefix tailTrace_385331
  have hstable : (prefixWord ++ tailWord_385331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385331).length < 2 ^ (prefixWord ++ tailWord_385331).sum := by decide
  have hdescent : baseEnd_385331 < baseStart_385331 := by decide
  rcases family_descends (prefixWord ++ tailWord_385331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385345 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 2, 5]
def baseStart_385345 : Nat := 118140960795 + 385345 * 2 ^ 59
def prefixEnd_385345 : Nat := 4983230072969 + 3 ^ 40 * 385345 * 2
def baseEnd_385345 : Nat := 65955734268966689871779

theorem tailTrace_385345 : CollatzResearch.WordTrace tailWord_385345 prefixEnd_385345 65955734268966689871779 := by
  unfold tailWord_385345
  simp only [CollatzResearch.WordTrace]
  refine ⟨14054686788968351531573489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9369791192645567687715659 14054686788968351531573489)
  ·
    refine ⟨10541015091726263648680117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14054686788968351531573489 10541015091726263648680117)
    ·
      refine ⟨988220164849337217063761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10541015091726263648680117 988220164849337217063761)
      ·
        refine ⟨741165123637002912797821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 988220164849337217063761 741165123637002912797821)
        ·
          refine ⟨277936921363876092299183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 741165123637002912797821 277936921363876092299183)
          ·
            refine ⟨416905382045814138448775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277936921363876092299183 416905382045814138448775)
            ·
              refine ⟨625358073068721207673163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416905382045814138448775 625358073068721207673163)
              ·
                refine ⟨938037109603081811509745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625358073068721207673163 938037109603081811509745)
                ·
                  refine ⟨703527832202311358632309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 938037109603081811509745 703527832202311358632309)
                  ·
                    refine ⟨65955734268966689871779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 703527832202311358632309 65955734268966689871779)
                    ·
                      rfl

theorem cell23_385345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_385345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385345 prefixEnd_385345 := by exact prefixLift 385345
  have htrace : WordTrace (prefixWord ++ tailWord_385345) baseStart_385345 baseEnd_385345 := by
    simpa [prefixWord, tailWord_385345, baseEnd_385345] using wordTrace_append hprefix tailTrace_385345
  have hstable : (prefixWord ++ tailWord_385345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385345).length < 2 ^ (prefixWord ++ tailWord_385345).sum := by decide
  have hdescent : baseEnd_385345 < baseStart_385345 := by decide
  rcases family_descends (prefixWord ++ tailWord_385345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385348 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_385348 : Nat := 118140960795 + 385348 * 2 ^ 59
def prefixEnd_385348 : Nat := 4983230072969 + 3 ^ 40 * 385348 * 2
def baseEnd_385348 : Nat := 197868743248863557877823

theorem tailTrace_385348 : CollatzResearch.WordTrace tailWord_385348 prefixEnd_385348 197868743248863557877823 := by
  unfold tailWord_385348
  simp only [CollatzResearch.WordTrace]
  refine ⟨7027398103978741521966349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9369864138638322029288465 7027398103978741521966349)
  ·
    refine ⟨2635274288992028070737381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7027398103978741521966349 2635274288992028070737381)
    ·
      refine ⟨494113929186005263263259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2635274288992028070737381 494113929186005263263259)
      ·
        refine ⟨741170893779007894894889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494113929186005263263259 741170893779007894894889)
        ·
          refine ⟨555878170334255921171167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 741170893779007894894889 555878170334255921171167)
          ·
            refine ⟨833817255501383881756751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555878170334255921171167 833817255501383881756751)
            ·
              refine ⟨1250725883252075822635127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833817255501383881756751 1250725883252075822635127)
              ·
                refine ⟨1876088824878113733952691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250725883252075822635127 1876088824878113733952691)
                ·
                  refine ⟨2814133237317170600929037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876088824878113733952691 2814133237317170600929037)
                  ·
                    refine ⟨1055299963993938975348389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2814133237317170600929037 1055299963993938975348389)
                    ·
                      refine ⟨197868743248863557877823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1055299963993938975348389 197868743248863557877823)
                      ·
                        rfl

theorem cell23_385348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_385348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385348 prefixEnd_385348 := by exact prefixLift 385348
  have htrace : WordTrace (prefixWord ++ tailWord_385348) baseStart_385348 baseEnd_385348 := by
    simpa [prefixWord, tailWord_385348, baseEnd_385348] using wordTrace_append hprefix tailTrace_385348
  have hstable : (prefixWord ++ tailWord_385348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385348).length < 2 ^ (prefixWord ++ tailWord_385348).sum := by decide
  have hdescent : baseEnd_385348 < baseStart_385348 := by decide
  rcases family_descends (prefixWord ++ tailWord_385348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385388 : List Nat := [2, 2, 1, 1, 6, 1, 3, 1, 6]
def baseStart_385388 : Nat := 118140960795 + 385388 * 2 ^ 59
def prefixEnd_385388 : Nat := 4983230072969 + 3 ^ 40 * 385388 * 2
def baseEnd_385388 : Nat := 21987698052782600153071

theorem tailTrace_385388 : CollatzResearch.WordTrace tailWord_385388 prefixEnd_385388 21987698052782600153071 := by
  unfold tailWord_385388
  simp only [CollatzResearch.WordTrace]
  refine ⟨7028127563906284937694409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9370836751875046583592545 7028127563906284937694409)
  ·
    refine ⟨5271095672929713703270807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7028127563906284937694409 5271095672929713703270807)
    ·
      refine ⟨7906643509394570554906211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5271095672929713703270807 7906643509394570554906211)
      ·
        refine ⟨11859965264091855832359317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7906643509394570554906211 11859965264091855832359317)
        ·
          refine ⟨555935871754305742141843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11859965264091855832359317 555935871754305742141843)
          ·
            refine ⟨833903807631458613212765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555935871754305742141843 833903807631458613212765)
            ·
              refine ⟨312713927861796979954787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 833903807631458613212765 312713927861796979954787)
              ·
                refine ⟨469070891792695469932181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312713927861796979954787 469070891792695469932181)
                ·
                  refine ⟨21987698052782600153071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 469070891792695469932181 21987698052782600153071)
                  ·
                    rfl

theorem cell23_385388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 6].length) (baseStart_385388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385388 prefixEnd_385388 := by exact prefixLift 385388
  have htrace : WordTrace (prefixWord ++ tailWord_385388) baseStart_385388 baseEnd_385388 := by
    simpa [prefixWord, tailWord_385388, baseEnd_385388] using wordTrace_append hprefix tailTrace_385388
  have hstable : (prefixWord ++ tailWord_385388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385388).length < 2 ^ (prefixWord ++ tailWord_385388).sum := by decide
  have hdescent : baseEnd_385388 < baseStart_385388 := by decide
  rcases family_descends (prefixWord ++ tailWord_385388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385391 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 6, 3, 2]
def baseStart_385391 : Nat := 118140960795 + 385391 * 2 ^ 59
def prefixEnd_385391 : Nat := 4983230072969 + 3 ^ 40 * 385391 * 2
def baseEnd_385391 : Nat := 197890822917006889640125

theorem tailTrace_385391 : CollatzResearch.WordTrace tailWord_385391 prefixEnd_385391 197890822917006889640125 := by
  unfold tailWord_385391
  simp only [CollatzResearch.WordTrace]
  refine ⟨14056364546801701387748027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9370909697867800925165351 14056364546801701387748027)
  ·
    refine ⟨21084546820202552081622041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14056364546801701387748027 21084546820202552081622041)
    ·
      refine ⟨15813410115151914061216531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21084546820202552081622041 15813410115151914061216531)
      ·
        refine ⟨23720115172727871091824797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15813410115151914061216531 23720115172727871091824797)
        ·
          refine ⟨8895043189772951659434299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23720115172727871091824797 8895043189772951659434299)
          ·
            refine ⟨13342564784659427489151449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8895043189772951659434299 13342564784659427489151449)
            ·
              refine ⟨10006923588494570616863587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13342564784659427489151449 10006923588494570616863587)
              ·
                refine ⟨15010385382741855925295381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10006923588494570616863587 15010385382741855925295381)
                ·
                  refine ⟨703611814816024496498221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15010385382741855925295381 703611814816024496498221)
                  ·
                    refine ⟨263854430556009186186833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 703611814816024496498221 263854430556009186186833)
                    ·
                      refine ⟨197890822917006889640125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263854430556009186186833 197890822917006889640125)
                      ·
                        rfl

theorem cell23_385391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 3, 2].length) (baseStart_385391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385391 prefixEnd_385391 := by exact prefixLift 385391
  have htrace : WordTrace (prefixWord ++ tailWord_385391) baseStart_385391 baseEnd_385391 := by
    simpa [prefixWord, tailWord_385391, baseEnd_385391] using wordTrace_append hprefix tailTrace_385391
  have hstable : (prefixWord ++ tailWord_385391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385391).length < 2 ^ (prefixWord ++ tailWord_385391).sum := by decide
  have hdescent : baseEnd_385391 < baseStart_385391 := by decide
  rcases family_descends (prefixWord ++ tailWord_385391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385431 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 4, 4]
def baseStart_385431 : Nat := 118140960795 + 385431 * 2 ^ 59
def prefixEnd_385431 : Nat := 4983230072969 + 3 ^ 40 * 385431 * 2
def baseEnd_385431 : Nat := 65970454047728911046647

theorem tailTrace_385431 : CollatzResearch.WordTrace tailWord_385431 prefixEnd_385431 65970454047728911046647 := by
  unfold tailWord_385431
  simp only [CollatzResearch.WordTrace]
  refine ⟨14057823466656788219204147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9371882311104525479469431 14057823466656788219204147)
  ·
    refine ⟨21086735199985182328806221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14057823466656788219204147 21086735199985182328806221)
    ·
      refine ⟨7907525699994443373302333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21086735199985182328806221 7907525699994443373302333)
      ·
        refine ⟨2965322137497916264988375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7907525699994443373302333 2965322137497916264988375)
        ·
          refine ⟨4447983206246874397482563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2965322137497916264988375 4447983206246874397482563)
          ·
            refine ⟨6671974809370311596223845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4447983206246874397482563 6671974809370311596223845)
            ·
              refine ⟨1250995276756933424291971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6671974809370311596223845 1250995276756933424291971)
              ·
                refine ⟨1876492915135400136437957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250995276756933424291971 1876492915135400136437957)
                ·
                  refine ⟨351842421587887525582117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1876492915135400136437957 351842421587887525582117)
                  ·
                    refine ⟨65970454047728911046647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 351842421587887525582117 65970454047728911046647)
                    ·
                      rfl

theorem cell23_385431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_385431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385431 prefixEnd_385431 := by exact prefixLift 385431
  have htrace : WordTrace (prefixWord ++ tailWord_385431) baseStart_385431 baseEnd_385431 := by
    simpa [prefixWord, tailWord_385431, baseEnd_385431] using wordTrace_append hprefix tailTrace_385431
  have hstable : (prefixWord ++ tailWord_385431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385431).length < 2 ^ (prefixWord ++ tailWord_385431).sum := by decide
  have hdescent : baseEnd_385431 < baseStart_385431 := by decide
  rcases family_descends (prefixWord ++ tailWord_385431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385444 : List Nat := [2, 3, 1, 2, 1, 1, 3, 10]
def baseStart_385444 : Nat := 118140960795 + 385444 * 2 ^ 59
def prefixEnd_385444 : Nat := 4983230072969 + 3 ^ 40 * 385444 * 2
def baseEnd_385444 : Nat := 7330297681173895639903

theorem tailTrace_385444 : CollatzResearch.WordTrace tailWord_385444 prefixEnd_385444 7330297681173895639903 := by
  unfold tailWord_385444
  simp only [CollatzResearch.WordTrace]
  refine ⟨7029148807804845719713693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9372198410406460959618257 7029148807804845719713693)
  ·
    refine ⟨2635930802926817144892635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7029148807804845719713693 2635930802926817144892635)
    ·
      refine ⟨3953896204390225717338953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2635930802926817144892635 3953896204390225717338953)
      ·
        refine ⟨2965422153292669288004215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3953896204390225717338953 2965422153292669288004215)
        ·
          refine ⟨4448133229939003932006323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2965422153292669288004215 4448133229939003932006323)
          ·
            refine ⟨6672199844908505898009485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4448133229939003932006323 6672199844908505898009485)
            ·
              refine ⟨2502074941840689711753557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6672199844908505898009485 2502074941840689711753557)
              ·
                refine ⟨7330297681173895639903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2502074941840689711753557 7330297681173895639903)
                ·
                  rfl

theorem cell23_385444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 10].length) (baseStart_385444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385444 prefixEnd_385444 := by exact prefixLift 385444
  have htrace : WordTrace (prefixWord ++ tailWord_385444) baseStart_385444 baseEnd_385444 := by
    simpa [prefixWord, tailWord_385444, baseEnd_385444] using wordTrace_append hprefix tailTrace_385444
  have hstable : (prefixWord ++ tailWord_385444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385444).length < 2 ^ (prefixWord ++ tailWord_385444).sum := by decide
  have hdescent : baseEnd_385444 < baseStart_385444 := by decide
  rcases family_descends (prefixWord ++ tailWord_385444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385468 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_385468 : Nat := 118140960795 + 385468 * 2 ^ 59
def prefixEnd_385468 : Nat := 4983230072969 + 3 ^ 40 * 385468 * 2
def baseEnd_385468 : Nat := 197930360927403088377271

theorem tailTrace_385468 : CollatzResearch.WordTrace tailWord_385468 prefixEnd_385468 197930360927403088377271 := by
  unfold tailWord_385468
  simp only [CollatzResearch.WordTrace]
  refine ⟨7029586483761371769150529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9372781978348495692200705 7029586483761371769150529)
  ·
    refine ⟨5272189862821028826862897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7029586483761371769150529 5272189862821028826862897)
    ·
      refine ⟨3954142397115771620147173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5272189862821028826862897 3954142397115771620147173)
      ·
        refine ⟨741401699459207178777595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3954142397115771620147173 741401699459207178777595)
        ·
          refine ⟨1112102549188810768166393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741401699459207178777595 1112102549188810768166393)
          ·
            refine ⟨834076911891608076124795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1112102549188810768166393 834076911891608076124795)
            ·
              refine ⟨1251115367837412114187193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834076911891608076124795 1251115367837412114187193)
              ·
                refine ⟨938336525878059085640395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251115367837412114187193 938336525878059085640395)
                ·
                  refine ⟨1407504788817088628460593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938336525878059085640395 1407504788817088628460593)
                  ·
                    refine ⟨1055628591612816471345445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1407504788817088628460593 1055628591612816471345445)
                    ·
                      refine ⟨197930360927403088377271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1055628591612816471345445 197930360927403088377271)
                      ·
                        rfl

theorem cell23_385468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_385468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385468 prefixEnd_385468 := by exact prefixLift 385468
  have htrace : WordTrace (prefixWord ++ tailWord_385468) baseStart_385468 baseEnd_385468 := by
    simpa [prefixWord, tailWord_385468, baseEnd_385468] using wordTrace_append hprefix tailTrace_385468
  have hstable : (prefixWord ++ tailWord_385468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385468).length < 2 ^ (prefixWord ++ tailWord_385468).sum := by decide
  have hdescent : baseEnd_385468 < baseStart_385468 := by decide
  rcases family_descends (prefixWord ++ tailWord_385468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385498 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2]
def baseStart_385498 : Nat := 118140960795 + 385498 * 2 ^ 59
def prefixEnd_385498 : Nat := 4983230072969 + 3 ^ 40 * 385498 * 2
def baseEnd_385498 : Nat := 197945765347037971002133

theorem tailTrace_385498 : CollatzResearch.WordTrace tailWord_385498 prefixEnd_385498 197945765347037971002133 := by
  unfold tailWord_385498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515066789353514665473287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9373511438276039107928765 3515066789353514665473287)
  ·
    refine ⟨5272600184030271998209931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3515066789353514665473287 5272600184030271998209931)
    ·
      refine ⟨7908900276045407997314897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5272600184030271998209931 7908900276045407997314897)
      ·
        refine ⟨5931675207034055997986173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7908900276045407997314897 5931675207034055997986173)
        ·
          refine ⟨2224378202637770999244815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5931675207034055997986173 2224378202637770999244815)
          ·
            refine ⟨3336567303956656498867223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224378202637770999244815 3336567303956656498867223)
            ·
              refine ⟨5004850955934984748300835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336567303956656498867223 5004850955934984748300835)
              ·
                refine ⟨7507276433902477122451253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5004850955934984748300835 7507276433902477122451253)
                ·
                  refine ⟨703807165678357230229805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7507276433902477122451253 703807165678357230229805)
                  ·
                    refine ⟨263927687129383961336177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 703807165678357230229805 263927687129383961336177)
                    ·
                      refine ⟨197945765347037971002133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263927687129383961336177 197945765347037971002133)
                      ·
                        rfl

theorem cell23_385498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_385498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385498 prefixEnd_385498 := by exact prefixLift 385498
  have htrace : WordTrace (prefixWord ++ tailWord_385498) baseStart_385498 baseEnd_385498 := by
    simpa [prefixWord, tailWord_385498, baseEnd_385498] using wordTrace_append hprefix tailTrace_385498
  have hstable : (prefixWord ++ tailWord_385498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385498).length < 2 ^ (prefixWord ++ tailWord_385498).sum := by decide
  have hdescent : baseEnd_385498 < baseStart_385498 := by decide
  rcases family_descends (prefixWord ++ tailWord_385498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385511 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_385511 : Nat := 118140960795 + 385511 * 2 ^ 59
def prefixEnd_385511 : Nat := 4983230072969 + 3 ^ 40 * 385511 * 2
def baseEnd_385511 : Nat := 197952440595546420139573

theorem tailTrace_385511 : CollatzResearch.WordTrace tailWord_385511 prefixEnd_385511 197952440595546420139573 := by
  unfold tailWord_385511
  simp only [CollatzResearch.WordTrace]
  refine ⟨14060741306366961882116387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9373827537577974588077591 14060741306366961882116387)
  ·
    refine ⟨21091111959550442823174581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14060741306366961882116387 21091111959550442823174581)
    ·
      refine ⟨1977291746207854014672617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21091111959550442823174581 1977291746207854014672617)
      ·
        refine ⟨1482968809655890511004463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1977291746207854014672617 1482968809655890511004463)
        ·
          refine ⟨2224453214483835766506695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482968809655890511004463 2224453214483835766506695)
          ·
            refine ⟨3336679821725753649760043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224453214483835766506695 3336679821725753649760043)
            ·
              refine ⟨5005019732588630474640065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336679821725753649760043 5005019732588630474640065)
              ·
                refine ⟨3753764799441472855980049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5005019732588630474640065 3753764799441472855980049)
                ·
                  refine ⟨2815323599581104641985037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3753764799441472855980049 2815323599581104641985037)
                  ·
                    refine ⟨1055746349842914240744389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2815323599581104641985037 1055746349842914240744389)
                    ·
                      refine ⟨197952440595546420139573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1055746349842914240744389 197952440595546420139573)
                      ·
                        rfl

theorem cell23_385511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_385511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385511 prefixEnd_385511 := by exact prefixLift 385511
  have htrace : WordTrace (prefixWord ++ tailWord_385511) baseStart_385511 baseEnd_385511 := by
    simpa [prefixWord, tailWord_385511, baseEnd_385511] using wordTrace_append hprefix tailTrace_385511
  have hstable : (prefixWord ++ tailWord_385511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385511).length < 2 ^ (prefixWord ++ tailWord_385511).sum := by decide
  have hdescent : baseEnd_385511 < baseStart_385511 := by decide
  rcases family_descends (prefixWord ++ tailWord_385511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385528 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 1, 4, 2]
def baseStart_385528 : Nat := 118140960795 + 385528 * 2 ^ 59
def prefixEnd_385528 : Nat := 4983230072969 + 3 ^ 40 * 385528 * 2
def baseEnd_385528 : Nat := 197961169766672853626995

theorem tailTrace_385528 : CollatzResearch.WordTrace tailWord_385528 prefixEnd_385528 197961169766672853626995 := by
  unfold tailWord_385528
  simp only [CollatzResearch.WordTrace]
  refine ⟨7030680673652686892742619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9374240898203582523656825 7030680673652686892742619)
  ·
    refine ⟨10546021010479030339113929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7030680673652686892742619 10546021010479030339113929)
    ·
      refine ⟨7909515757859272754335447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10546021010479030339113929 7909515757859272754335447)
      ·
        refine ⟨11864273636788909131503171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7909515757859272754335447 11864273636788909131503171)
        ·
          refine ⟨17796410455183363697254757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11864273636788909131503171 17796410455183363697254757)
          ·
            refine ⟨3336826960346880693235267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17796410455183363697254757 3336826960346880693235267)
            ·
              refine ⟨5005240440520321039852901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336826960346880693235267 5005240440520321039852901)
              ·
                refine ⟨938482582597560194972419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5005240440520321039852901 938482582597560194972419)
                ·
                  refine ⟨1407723873896340292458629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938482582597560194972419 1407723873896340292458629)
                  ·
                    refine ⟨263948226355563804835993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1407723873896340292458629 263948226355563804835993)
                    ·
                      refine ⟨197961169766672853626995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263948226355563804835993 197961169766672853626995)
                      ·
                        rfl

theorem cell23_385528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 4, 2].length) (baseStart_385528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385528 prefixEnd_385528 := by exact prefixLift 385528
  have htrace : WordTrace (prefixWord ++ tailWord_385528) baseStart_385528 baseEnd_385528 := by
    simpa [prefixWord, tailWord_385528, baseEnd_385528] using wordTrace_append hprefix tailTrace_385528
  have hstable : (prefixWord ++ tailWord_385528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385528).length < 2 ^ (prefixWord ++ tailWord_385528).sum := by decide
  have hdescent : baseEnd_385528 < baseStart_385528 := by decide
  rcases family_descends (prefixWord ++ tailWord_385528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385541 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_385541 : Nat := 118140960795 + 385541 * 2 ^ 59
def prefixEnd_385541 : Nat := 4983230072969 + 3 ^ 40 * 385541 * 2
def baseEnd_385541 : Nat := 197967845015181302764435

theorem tailTrace_385541 : CollatzResearch.WordTrace tailWord_385541 prefixEnd_385541 197967845015181302764435 := by
  unfold tailWord_385541
  simp only [CollatzResearch.WordTrace]
  refine ⟨14061835496258277005708477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9374556997505518003805651 14061835496258277005708477)
  ·
    refine ⟨5273188311096853877140679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14061835496258277005708477 5273188311096853877140679)
    ·
      refine ⟨7909782466645280815711019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5273188311096853877140679 7909782466645280815711019)
      ·
        refine ⟨11864673699967921223566529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7909782466645280815711019 11864673699967921223566529)
        ·
          refine ⟨8898505274975940917674897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11864673699967921223566529 8898505274975940917674897)
          ·
            refine ⟨6673878956231955688256173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8898505274975940917674897 6673878956231955688256173)
            ·
              refine ⟨2502704608586983383096065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6673878956231955688256173 2502704608586983383096065)
              ·
                refine ⟨1877028456440237537322049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502704608586983383096065 1877028456440237537322049)
                ·
                  refine ⟨1407771342330178152991537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1877028456440237537322049 1407771342330178152991537)
                  ·
                    refine ⟨1055828506747633614743653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1407771342330178152991537 1055828506747633614743653)
                    ·
                      refine ⟨197967845015181302764435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1055828506747633614743653 197967845015181302764435)
                      ·
                        rfl

theorem cell23_385541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_385541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385541 prefixEnd_385541 := by exact prefixLift 385541
  have htrace : WordTrace (prefixWord ++ tailWord_385541) baseStart_385541 baseEnd_385541 := by
    simpa [prefixWord, tailWord_385541, baseEnd_385541] using wordTrace_append hprefix tailTrace_385541
  have hstable : (prefixWord ++ tailWord_385541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385541).length < 2 ^ (prefixWord ++ tailWord_385541).sum := by decide
  have hdescent : baseEnd_385541 < baseStart_385541 := by decide
  rcases family_descends (prefixWord ++ tailWord_385541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385545 : List Nat := [1, 2, 1, 1, 3, 1, 2, 6, 2, 2, 2]
def baseStart_385545 : Nat := 118140960795 + 385545 * 2 ^ 59
def prefixEnd_385545 : Nat := 4983230072969 + 3 ^ 40 * 385545 * 2
def baseEnd_385545 : Nat := 197969898937799287114417

theorem tailTrace_385545 : CollatzResearch.WordTrace tailWord_385545 prefixEnd_385545 197969898937799287114417 := by
  unfold tailWord_385545
  simp only [CollatzResearch.WordTrace]
  refine ⟨14061981388243785688854089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9374654258829190459236059 14061981388243785688854089)
  ·
    refine ⟨10546486041182839266640567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14061981388243785688854089 10546486041182839266640567)
    ·
      refine ⟨15819729061774258899960851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10546486041182839266640567 15819729061774258899960851)
      ·
        refine ⟨23729593592661388349941277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15819729061774258899960851 23729593592661388349941277)
        ·
          refine ⟨8898597597248020631227979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23729593592661388349941277 8898597597248020631227979)
          ·
            refine ⟨13347896395872030946841969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8898597597248020631227979 13347896395872030946841969)
            ·
              refine ⟨10010922296904023210131477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13347896395872030946841969 10010922296904023210131477)
              ·
                refine ⟨469261982667376087974913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10010922296904023210131477 469261982667376087974913)
                ·
                  refine ⟨351946487000532065981185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469261982667376087974913 351946487000532065981185)
                  ·
                    refine ⟨263959865250399049485889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 351946487000532065981185 263959865250399049485889)
                    ·
                      refine ⟨197969898937799287114417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263959865250399049485889 197969898937799287114417)
                      ·
                        rfl

theorem cell23_385545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 2, 2].length) (baseStart_385545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385545 prefixEnd_385545 := by exact prefixLift 385545
  have htrace : WordTrace (prefixWord ++ tailWord_385545) baseStart_385545 baseEnd_385545 := by
    simpa [prefixWord, tailWord_385545, baseEnd_385545] using wordTrace_append hprefix tailTrace_385545
  have hstable : (prefixWord ++ tailWord_385545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385545).length < 2 ^ (prefixWord ++ tailWord_385545).sum := by decide
  have hdescent : baseEnd_385545 < baseStart_385545 := by decide
  rcases family_descends (prefixWord ++ tailWord_385545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385591 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_385591 : Nat := 118140960795 + 385591 * 2 ^ 59
def prefixEnd_385591 : Nat := 4983230072969 + 3 ^ 40 * 385591 * 2
def baseEnd_385591 : Nat := 197993519047906107139205

theorem tailTrace_385591 : CollatzResearch.WordTrace tailWord_385591 prefixEnd_385591 197993519047906107139205 := by
  unfold tailWord_385591
  simp only [CollatzResearch.WordTrace]
  refine ⟨14063659146077135545028627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9375772764051423696685751 14063659146077135545028627)
  ·
    refine ⟨21095488719115703317542941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14063659146077135545028627 21095488719115703317542941)
    ·
      refine ⟨7910808269668388744078603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21095488719115703317542941 7910808269668388744078603)
      ·
        refine ⟨11866212404502583116117905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7910808269668388744078603 11866212404502583116117905)
        ·
          refine ⟨8899659303376937337088429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11866212404502583116117905 8899659303376937337088429)
          ·
            refine ⟨3337372238766351501408161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8899659303376937337088429 3337372238766351501408161)
            ·
              refine ⟨2503029179074763626056121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3337372238766351501408161 2503029179074763626056121)
              ·
                refine ⟨1877271884306072719542091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503029179074763626056121 1877271884306072719542091)
                ·
                  refine ⟨2815907826459109079313137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877271884306072719542091 2815907826459109079313137)
                  ·
                    refine ⟨2111930869844331809484853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2815907826459109079313137 2111930869844331809484853)
                    ·
                      refine ⟨197993519047906107139205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2111930869844331809484853 197993519047906107139205)
                      ·
                        rfl

theorem cell23_385591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_385591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385591 prefixEnd_385591 := by exact prefixLift 385591
  have htrace : WordTrace (prefixWord ++ tailWord_385591) baseStart_385591 baseEnd_385591 := by
    simpa [prefixWord, tailWord_385591, baseEnd_385591] using wordTrace_append hprefix tailTrace_385591
  have hstable : (prefixWord ++ tailWord_385591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385591).length < 2 ^ (prefixWord ++ tailWord_385591).sum := by decide
  have hdescent : baseEnd_385591 < baseStart_385591 := by decide
  rcases family_descends (prefixWord ++ tailWord_385591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385618 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_385618 : Nat := 118140960795 + 385618 * 2 ^ 59
def prefixEnd_385618 : Nat := 4983230072969 + 3 ^ 40 * 385618 * 2
def baseEnd_385618 : Nat := 198007383025577501501581

theorem tailTrace_385618 : CollatzResearch.WordTrace tailWord_385618 prefixEnd_385618 198007383025577501501581 := by
  unfold tailWord_385618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3516160979244829789065377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9376429277986212770841005 3516160979244829789065377)
  ·
    refine ⟨2637120734433622341799033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3516160979244829789065377 2637120734433622341799033)
    ·
      refine ⟨1977840550825216756349275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2637120734433622341799033 1977840550825216756349275)
      ·
        refine ⟨2966760826237825134523913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1977840550825216756349275 2966760826237825134523913)
        ·
          refine ⟨2225070619678368850892935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2966760826237825134523913 2225070619678368850892935)
          ·
            refine ⟨3337605929517553276339403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225070619678368850892935 3337605929517553276339403)
            ·
              refine ⟨5006408894276329914509105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3337605929517553276339403 5006408894276329914509105)
              ·
                refine ⟨3754806670707247435881829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5006408894276329914509105 3754806670707247435881829)
                ·
                  refine ⟨704026250757608894227843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3754806670707247435881829 704026250757608894227843)
                  ·
                    refine ⟨1056039376136413341341765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 704026250757608894227843 1056039376136413341341765)
                    ·
                      refine ⟨198007383025577501501581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1056039376136413341341765 198007383025577501501581)
                      ·
                        rfl

theorem cell23_385618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_385618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385618 prefixEnd_385618 := by exact prefixLift 385618
  have htrace : WordTrace (prefixWord ++ tailWord_385618) baseStart_385618 baseEnd_385618 := by
    simpa [prefixWord, tailWord_385618, baseEnd_385618] using wordTrace_append hprefix tailTrace_385618
  have hstable : (prefixWord ++ tailWord_385618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385618).length < 2 ^ (prefixWord ++ tailWord_385618).sum := by decide
  have hdescent : baseEnd_385618 < baseStart_385618 := by decide
  rcases family_descends (prefixWord ++ tailWord_385618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385631 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 4]
def baseStart_385631 : Nat := 118140960795 + 385631 * 2 ^ 59
def prefixEnd_385631 : Nat := 4983230072969 + 3 ^ 40 * 385631 * 2
def baseEnd_385631 : Nat := 198014058274085950639021

theorem tailTrace_385631 : CollatzResearch.WordTrace tailWord_385631 prefixEnd_385631 198014058274085950639021 := by
  unfold tailWord_385631
  simp only [CollatzResearch.WordTrace]
  refine ⟨14065118065932222376484747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9376745377288148250989831 14065118065932222376484747)
  ·
    refine ⟨21097677098898333564727121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14065118065932222376484747 21097677098898333564727121)
    ·
      refine ⟨15823257824173750173545341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21097677098898333564727121 15823257824173750173545341)
      ·
        refine ⟨5933721684065156315079503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15823257824173750173545341 5933721684065156315079503)
        ·
          refine ⟨8900582526097734472619255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5933721684065156315079503 8900582526097734472619255)
          ·
            refine ⟨13350873789146601708928883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8900582526097734472619255 13350873789146601708928883)
            ·
              refine ⟨20026310683719902563393325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13350873789146601708928883 20026310683719902563393325)
              ·
                refine ⟨7509866506394963461272497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20026310683719902563393325 7509866506394963461272497)
                ·
                  refine ⟨5632399879796222595954373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7509866506394963461272497 5632399879796222595954373)
                  ·
                    refine ⟨1056074977461791736741445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5632399879796222595954373 1056074977461791736741445)
                    ·
                      refine ⟨198014058274085950639021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1056074977461791736741445 198014058274085950639021)
                      ·
                        rfl

theorem cell23_385631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_385631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385631 prefixEnd_385631 := by exact prefixLift 385631
  have htrace : WordTrace (prefixWord ++ tailWord_385631) baseStart_385631 baseEnd_385631 := by
    simpa [prefixWord, tailWord_385631, baseEnd_385631] using wordTrace_append hprefix tailTrace_385631
  have hstable : (prefixWord ++ tailWord_385631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385631).length < 2 ^ (prefixWord ++ tailWord_385631).sum := by decide
  have hdescent : baseEnd_385631 < baseStart_385631 := by decide
  rcases family_descends (prefixWord ++ tailWord_385631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385681 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_385681 : Nat := 118140960795 + 385681 * 2 ^ 59
def prefixEnd_385681 : Nat := 4983230072969 + 3 ^ 40 * 385681 * 2
def baseEnd_385681 : Nat := 198039732306810755013791

theorem tailTrace_385681 : CollatzResearch.WordTrace tailWord_385681 prefixEnd_385681 198039732306810755013791 := by
  unfold tailWord_385681
  simp only [CollatzResearch.WordTrace]
  refine ⟨14066941715751080915804897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9377961143834053943869931 14066941715751080915804897)
  ·
    refine ⟨10550206286813310686853673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14066941715751080915804897 10550206286813310686853673)
    ·
      refine ⟨7912654715109983015140255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10550206286813310686853673 7912654715109983015140255)
      ·
        refine ⟨11868982072664974522710383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7912654715109983015140255 11868982072664974522710383)
        ·
          refine ⟨17803473108997461784065575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11868982072664974522710383 17803473108997461784065575)
          ·
            refine ⟨26705209663496192676098363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17803473108997461784065575 26705209663496192676098363)
            ·
              refine ⟨40057814495244289014147545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26705209663496192676098363 40057814495244289014147545)
              ·
                refine ⟨30043360871433216760610659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40057814495244289014147545 30043360871433216760610659)
                ·
                  refine ⟨45065041307149825140915989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30043360871433216760610659 45065041307149825140915989)
                  ·
                    refine ⟨2112423811272648053480437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45065041307149825140915989 2112423811272648053480437)
                    ·
                      refine ⟨198039732306810755013791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2112423811272648053480437 198039732306810755013791)
                      ·
                        rfl

theorem cell23_385681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_385681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385681 prefixEnd_385681 := by exact prefixLift 385681
  have htrace : WordTrace (prefixWord ++ tailWord_385681) baseStart_385681 baseEnd_385681 := by
    simpa [prefixWord, tailWord_385681, baseEnd_385681] using wordTrace_append hprefix tailTrace_385681
  have hstable : (prefixWord ++ tailWord_385681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385681).length < 2 ^ (prefixWord ++ tailWord_385681).sum := by decide
  have hdescent : baseEnd_385681 < baseStart_385681 := by decide
  rcases family_descends (prefixWord ++ tailWord_385681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385688 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 3, 5]
def baseStart_385688 : Nat := 118140960795 + 385688 * 2 ^ 59
def prefixEnd_385688 : Nat := 4983230072969 + 3 ^ 40 * 385688 * 2
def baseEnd_385688 : Nat := 66014442223797409208753

theorem tailTrace_385688 : CollatzResearch.WordTrace tailWord_385688 prefixEnd_385688 66014442223797409208753 := by
  unfold tailWord_385688
  simp only [CollatzResearch.WordTrace]
  refine ⟨7033598513362860555654859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9378131351150480740873145 7033598513362860555654859)
  ·
    refine ⟨10550397770044290833482289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7033598513362860555654859 10550397770044290833482289)
    ·
      refine ⟨7912798327533218125111717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10550397770044290833482289 7912798327533218125111717)
      ·
        refine ⟨1483649686412478398458447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7912798327533218125111717 1483649686412478398458447)
        ·
          refine ⟨2225474529618717597687671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483649686412478398458447 2225474529618717597687671)
          ·
            refine ⟨3338211794428076396531507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225474529618717597687671 3338211794428076396531507)
            ·
              refine ⟨5007317691642114594797261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338211794428076396531507 5007317691642114594797261)
              ·
                refine ⟨1877744134365792973048973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5007317691642114594797261 1877744134365792973048973)
                ·
                  refine ⟨704154050387172364893365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1877744134365792973048973 704154050387172364893365)
                  ·
                    refine ⟨66014442223797409208753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 704154050387172364893365 66014442223797409208753)
                    ·
                      rfl

theorem cell23_385688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_385688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385688 prefixEnd_385688 := by exact prefixLift 385688
  have htrace : WordTrace (prefixWord ++ tailWord_385688) baseStart_385688 baseEnd_385688 := by
    simpa [prefixWord, tailWord_385688, baseEnd_385688] using wordTrace_append hprefix tailTrace_385688
  have hstable : (prefixWord ++ tailWord_385688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385688).length < 2 ^ (prefixWord ++ tailWord_385688).sum := by decide
  have hdescent : baseEnd_385688 < baseStart_385688 := by decide
  rcases family_descends (prefixWord ++ tailWord_385688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385728 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 5]
def baseStart_385728 : Nat := 118140960795 + 385728 * 2 ^ 59
def prefixEnd_385728 : Nat := 4983230072969 + 3 ^ 40 * 385728 * 2
def baseEnd_385728 : Nat := 198063865897572071126075

theorem tailTrace_385728 : CollatzResearch.WordTrace tailWord_385728 prefixEnd_385728 198063865897572071126075 := by
  unfold tailWord_385728
  simp only [CollatzResearch.WordTrace]
  refine ⟨7034327973290403971382919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9379103964387205295177225 7034327973290403971382919)
  ·
    refine ⟨10551491959935605957074379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7034327973290403971382919 10551491959935605957074379)
    ·
      refine ⟨15827237939903408935611569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10551491959935605957074379 15827237939903408935611569)
      ·
        refine ⟨11870428454927556701708677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15827237939903408935611569 11870428454927556701708677)
        ·
          refine ⟨2225705335298916881570377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11870428454927556701708677 2225705335298916881570377)
          ·
            refine ⟨1669279001474187661177783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2225705335298916881570377 1669279001474187661177783)
            ·
              refine ⟨2503918502211281491766675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1669279001474187661177783 2503918502211281491766675)
              ·
                refine ⟨3755877753316922237650013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2503918502211281491766675 3755877753316922237650013)
                ·
                  refine ⟨1408454157493845839118755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3755877753316922237650013 1408454157493845839118755)
                  ·
                    refine ⟨2112681236240768758678133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1408454157493845839118755 2112681236240768758678133)
                    ·
                      refine ⟨198063865897572071126075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2112681236240768758678133 198063865897572071126075)
                      ·
                        rfl

theorem cell23_385728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_385728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385728 prefixEnd_385728 := by exact prefixLift 385728
  have htrace : WordTrace (prefixWord ++ tailWord_385728) baseStart_385728 baseEnd_385728 := by
    simpa [prefixWord, tailWord_385728, baseEnd_385728] using wordTrace_append hprefix tailTrace_385728
  have hstable : (prefixWord ++ tailWord_385728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385728).length < 2 ^ (prefixWord ++ tailWord_385728).sum := by decide
  have hdescent : baseEnd_385728 < baseStart_385728 := by decide
  rcases family_descends (prefixWord ++ tailWord_385728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385742 : List Nat := [4, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_385742 : Nat := 118140960795 + 385742 * 2 ^ 59
def prefixEnd_385742 : Nat := 4983230072969 + 3 ^ 40 * 385742 * 2
def baseEnd_385742 : Nat := 198071054626735016351011

theorem tailTrace_385742 : CollatzResearch.WordTrace tailWord_385742 prefixEnd_385742 198071054626735016351011 := by
  unfold tailWord_385742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1758645821066261041721935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9379444379020058889183653 1758645821066261041721935)
  ·
    refine ⟨2637968731599391562582903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1758645821066261041721935 2637968731599391562582903)
    ·
      refine ⟨3956953097399087343874355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2637968731599391562582903 3956953097399087343874355)
      ·
        refine ⟨5935429646098631015811533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3956953097399087343874355 5935429646098631015811533)
        ·
          refine ⟨2225786117286986630929325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5935429646098631015811533 2225786117286986630929325)
          ·
            refine ⟨834669793982619986598497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2225786117286986630929325 834669793982619986598497)
            ·
              refine ⟨626002345486964989948873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834669793982619986598497 626002345486964989948873)
              ·
                refine ⟨469501759115223742461655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626002345486964989948873 469501759115223742461655)
                ·
                  refine ⟨704252638672835613692483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469501759115223742461655 704252638672835613692483)
                  ·
                    refine ⟨1056378958009253420538725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 704252638672835613692483 1056378958009253420538725)
                    ·
                      refine ⟨198071054626735016351011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1056378958009253420538725 198071054626735016351011)
                      ·
                        rfl

theorem cell23_385742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_385742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385742 prefixEnd_385742 := by exact prefixLift 385742
  have htrace : WordTrace (prefixWord ++ tailWord_385742) baseStart_385742 baseEnd_385742 := by
    simpa [prefixWord, tailWord_385742, baseEnd_385742] using wordTrace_append hprefix tailTrace_385742
  have hstable : (prefixWord ++ tailWord_385742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385742).length < 2 ^ (prefixWord ++ tailWord_385742).sum := by decide
  have hdescent : baseEnd_385742 < baseStart_385742 := by decide
  rcases family_descends (prefixWord ++ tailWord_385742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385776 : List Nat := [2, 1, 1, 1, 3, 1, 7, 2, 1, 2, 2]
def baseStart_385776 : Nat := 118140960795 + 385776 * 2 ^ 59
def prefixEnd_385776 : Nat := 4983230072969 + 3 ^ 40 * 385776 * 2
def baseEnd_385776 : Nat := 198088512968987883325855

theorem tailTrace_385776 : CollatzResearch.WordTrace tailWord_385776 prefixEnd_385776 198088512968987883325855 := by
  unfold tailWord_385776
  simp only [CollatzResearch.WordTrace]
  refine ⟨7035203325203456070256591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9380271100271274760342121 7035203325203456070256591)
  ·
    refine ⟨10552804987805184105384887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7035203325203456070256591 10552804987805184105384887)
    ·
      refine ⟨15829207481707776158077331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10552804987805184105384887 15829207481707776158077331)
      ·
        refine ⟨23743811222561664237115997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15829207481707776158077331 23743811222561664237115997)
        ·
          refine ⟨8903929208460624088918499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23743811222561664237115997 8903929208460624088918499)
          ·
            refine ⟨13355893812690936133377749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8903929208460624088918499 13355893812690936133377749)
            ·
              refine ⟨313028761234943815626041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 13355893812690936133377749 313028761234943815626041)
              ·
                refine ⟨234771570926207861719531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313028761234943815626041 234771570926207861719531)
                ·
                  refine ⟨352157356389311792579297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234771570926207861719531 352157356389311792579297)
                  ·
                    refine ⟨264118017291983844434473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 352157356389311792579297 264118017291983844434473)
                    ·
                      refine ⟨198088512968987883325855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 264118017291983844434473 198088512968987883325855)
                      ·
                        rfl

theorem cell23_385776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 1, 2, 2].length) (baseStart_385776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385776 prefixEnd_385776 := by exact prefixLift 385776
  have htrace : WordTrace (prefixWord ++ tailWord_385776) baseStart_385776 baseEnd_385776 := by
    simpa [prefixWord, tailWord_385776, baseEnd_385776] using wordTrace_append hprefix tailTrace_385776
  have hstable : (prefixWord ++ tailWord_385776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385776).length < 2 ^ (prefixWord ++ tailWord_385776).sum := by decide
  have hdescent : baseEnd_385776 < baseStart_385776 := by decide
  rcases family_descends (prefixWord ++ tailWord_385776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385802 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 3, 3, 2]
def baseStart_385802 : Nat := 118140960795 + 385802 * 2 ^ 59
def prefixEnd_385802 : Nat := 4983230072969 + 3 ^ 40 * 385802 * 2
def baseEnd_385802 : Nat := 198101863466004781600735

theorem tailTrace_385802 : CollatzResearch.WordTrace tailWord_385802 prefixEnd_385802 198101863466004781600735 := by
  unfold tailWord_385802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517838737078179645239915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9380903298875145720639773 3517838737078179645239915)
  ·
    refine ⟨5276758105617269467859873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3517838737078179645239915 5276758105617269467859873)
    ·
      refine ⟨3957568579212952100894905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5276758105617269467859873 3957568579212952100894905)
      ·
        refine ⟨2968176434409714075671179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3957568579212952100894905 2968176434409714075671179)
        ·
          refine ⟨4452264651614571113506769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2968176434409714075671179 4452264651614571113506769)
          ·
            refine ⟨3339198488710928335130077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4452264651614571113506769 3339198488710928335130077)
            ·
              refine ⟨1252199433266598125673779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3339198488710928335130077 1252199433266598125673779)
              ·
                refine ⟨1878299149899897188510669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1252199433266598125673779 1878299149899897188510669)
                ·
                  refine ⟨704362181212461445691501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1878299149899897188510669 704362181212461445691501)
                  ·
                    refine ⟨264135817954673042134313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 704362181212461445691501 264135817954673042134313)
                    ·
                      refine ⟨198101863466004781600735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 264135817954673042134313 198101863466004781600735)
                      ·
                        rfl

theorem cell23_385802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_385802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385802 prefixEnd_385802 := by exact prefixLift 385802
  have htrace : WordTrace (prefixWord ++ tailWord_385802) baseStart_385802 baseEnd_385802 := by
    simpa [prefixWord, tailWord_385802, baseEnd_385802] using wordTrace_append hprefix tailTrace_385802
  have hstable : (prefixWord ++ tailWord_385802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385802).length < 2 ^ (prefixWord ++ tailWord_385802).sum := by decide
  have hdescent : baseEnd_385802 < baseStart_385802 := by decide
  rcases family_descends (prefixWord ++ tailWord_385802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385832 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_385832 : Nat := 118140960795 + 385832 * 2 ^ 59
def prefixEnd_385832 : Nat := 4983230072969 + 3 ^ 40 * 385832 * 2
def baseEnd_385832 : Nat := 198117267885639664225597

theorem tailTrace_385832 : CollatzResearch.WordTrace tailWord_385832 prefixEnd_385832 198117267885639664225597 := by
  unfold tailWord_385832
  simp only [CollatzResearch.WordTrace]
  refine ⟨7036224569102016852275875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9381632758802689136367833 7036224569102016852275875)
  ·
    refine ⟨10554336853653025278413813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7036224569102016852275875 10554336853653025278413813)
    ·
      refine ⟨989469080029971119851295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10554336853653025278413813 989469080029971119851295)
      ·
        refine ⟨1484203620044956679776943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989469080029971119851295 1484203620044956679776943)
        ·
          refine ⟨2226305430067435019665415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1484203620044956679776943 2226305430067435019665415)
          ·
            refine ⟨3339458145101152529498123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226305430067435019665415 3339458145101152529498123)
            ·
              refine ⟨5009187217651728794247185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339458145101152529498123 5009187217651728794247185)
              ·
                refine ⟨3756890413238796595685389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5009187217651728794247185 3756890413238796595685389)
                ·
                  refine ⟨1408833904964548723382021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3756890413238796595685389 1408833904964548723382021)
                  ·
                    refine ⟨264156357180852885634129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1408833904964548723382021 264156357180852885634129)
                    ·
                      refine ⟨198117267885639664225597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 264156357180852885634129 198117267885639664225597)
                      ·
                        rfl

theorem cell23_385832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_385832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385832 prefixEnd_385832 := by exact prefixLift 385832
  have htrace : WordTrace (prefixWord ++ tailWord_385832) baseStart_385832 baseEnd_385832 := by
    simpa [prefixWord, tailWord_385832, baseEnd_385832] using wordTrace_append hprefix tailTrace_385832
  have hstable : (prefixWord ++ tailWord_385832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385832).length < 2 ^ (prefixWord ++ tailWord_385832).sum := by decide
  have hdescent : baseEnd_385832 < baseStart_385832 := by decide
  rcases family_descends (prefixWord ++ tailWord_385832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385845 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_385845 : Nat := 118140960795 + 385845 * 2 ^ 59
def prefixEnd_385845 : Nat := 4983230072969 + 3 ^ 40 * 385845 * 2
def baseEnd_385845 : Nat := 198123943134148113363037

theorem tailTrace_385845 : CollatzResearch.WordTrace tailWord_385845 prefixEnd_385845 198123943134148113363037 := by
  unfold tailWord_385845
  simp only [CollatzResearch.WordTrace]
  refine ⟨14072923287156936924774989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9381948858104624616516659 14072923287156936924774989)
  ·
    refine ⟨5277346232683851346790621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14072923287156936924774989 5277346232683851346790621)
    ·
      refine ⟨1979004837256444255046483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5277346232683851346790621 1979004837256444255046483)
      ·
        refine ⟨2968507255884666382569725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1979004837256444255046483 2968507255884666382569725)
        ·
          refine ⟨1113190220956749893463647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2968507255884666382569725 1113190220956749893463647)
          ·
            refine ⟨1669785331435124840195471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113190220956749893463647 1669785331435124840195471)
            ·
              refine ⟨2504677997152687260293207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1669785331435124840195471 2504677997152687260293207)
              ·
                refine ⟨3757016995729030890439811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504677997152687260293207 3757016995729030890439811)
                ·
                  refine ⟨5635525493593546335659717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757016995729030890439811 5635525493593546335659717)
                  ·
                    refine ⟨1056661030048789937936197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5635525493593546335659717 1056661030048789937936197)
                    ·
                      refine ⟨198123943134148113363037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1056661030048789937936197 198123943134148113363037)
                      ·
                        rfl

theorem cell23_385845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_385845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385845 prefixEnd_385845 := by exact prefixLift 385845
  have htrace : WordTrace (prefixWord ++ tailWord_385845) baseStart_385845 baseEnd_385845 := by
    simpa [prefixWord, tailWord_385845, baseEnd_385845] using wordTrace_append hprefix tailTrace_385845
  have hstable : (prefixWord ++ tailWord_385845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385845).length < 2 ^ (prefixWord ++ tailWord_385845).sum := by decide
  have hdescent : baseEnd_385845 < baseStart_385845 := by decide
  rcases family_descends (prefixWord ++ tailWord_385845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385855 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 7]
def baseStart_385855 : Nat := 118140960795 + 385855 * 2 ^ 59
def prefixEnd_385855 : Nat := 4983230072969 + 3 ^ 40 * 385855 * 2
def baseEnd_385855 : Nat := 22014341993410341581999

theorem tailTrace_385855 : CollatzResearch.WordTrace tailWord_385855 prefixEnd_385855 22014341993410341581999 := by
  unfold tailWord_385855
  simp only [CollatzResearch.WordTrace]
  refine ⟨14073288017120708632639019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9382192011413805755092679 14073288017120708632639019)
  ·
    refine ⟨21109932025681062948958529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14073288017120708632639019 21109932025681062948958529)
    ·
      refine ⟨15832449019260797211718897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21109932025681062948958529 15832449019260797211718897)
      ·
        refine ⟨11874336764445597908789173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15832449019260797211718897 11874336764445597908789173)
        ·
          refine ⟨1113219071666774803948985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11874336764445597908789173 1113219071666774803948985)
          ·
            refine ⟨834914303750081102961739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1113219071666774803948985 834914303750081102961739)
            ·
              refine ⟨1252371455625121654442609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834914303750081102961739 1252371455625121654442609)
              ·
                refine ⟨939278591718841240831957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252371455625121654442609 939278591718841240831957)
                ·
                  refine ⟨22014341993410341581999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 939278591718841240831957 22014341993410341581999)
                  ·
                    rfl

theorem cell23_385855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 7].length) (baseStart_385855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385855 prefixEnd_385855 := by exact prefixLift 385855
  have htrace : WordTrace (prefixWord ++ tailWord_385855) baseStart_385855 baseEnd_385855 := by
    simpa [prefixWord, tailWord_385855, baseEnd_385855] using wordTrace_append hprefix tailTrace_385855
  have hstable : (prefixWord ++ tailWord_385855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385855).length < 2 ^ (prefixWord ++ tailWord_385855).sum := by decide
  have hdescent : baseEnd_385855 < baseStart_385855 := by decide
  rcases family_descends (prefixWord ++ tailWord_385855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385905 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_385905 : Nat := 118140960795 + 385905 * 2 ^ 59
def prefixEnd_385905 : Nat := 4983230072969 + 3 ^ 40 * 385905 * 2
def baseEnd_385905 : Nat := 198154751973417878612761

theorem tailTrace_385905 : CollatzResearch.WordTrace tailWord_385905 prefixEnd_385905 198154751973417878612761 := by
  unfold tailWord_385905
  simp only [CollatzResearch.WordTrace]
  refine ⟨14075111666939567171959169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9383407777959711447972779 14075111666939567171959169)
  ·
    refine ⟨10556333750204675378969377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14075111666939567171959169 10556333750204675378969377)
    ·
      refine ⟨7917250312653506534227033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10556333750204675378969377 7917250312653506534227033)
      ·
        refine ⟨5937937734490129900670275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7917250312653506534227033 5937937734490129900670275)
        ·
          refine ⟨8906906601735194851005413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5937937734490129900670275 8906906601735194851005413)
          ·
            refine ⟨1670044987825349034563515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8906906601735194851005413 1670044987825349034563515)
            ·
              refine ⟨2505067481738023551845273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670044987825349034563515 2505067481738023551845273)
              ·
                refine ⟨1878800611303517663883955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2505067481738023551845273 1878800611303517663883955)
                ·
                  refine ⟨2818200916955276495825933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1878800611303517663883955 2818200916955276495825933)
                  ·
                    refine ⟨1056825343858228685934725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818200916955276495825933 1056825343858228685934725)
                    ·
                      refine ⟨198154751973417878612761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1056825343858228685934725 198154751973417878612761)
                      ·
                        rfl

theorem cell23_385905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_385905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385905 prefixEnd_385905 := by exact prefixLift 385905
  have htrace : WordTrace (prefixWord ++ tailWord_385905) baseStart_385905 baseEnd_385905 := by
    simpa [prefixWord, tailWord_385905, baseEnd_385905] using wordTrace_append hprefix tailTrace_385905
  have hstable : (prefixWord ++ tailWord_385905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385905).length < 2 ^ (prefixWord ++ tailWord_385905).sum := by decide
  have hdescent : baseEnd_385905 < baseStart_385905 := by decide
  rcases family_descends (prefixWord ++ tailWord_385905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385945 : List Nat := [1, 2, 1, 2, 1, 3, 1, 6, 6]
def baseStart_385945 : Nat := 118140960795 + 385945 * 2 ^ 59
def prefixEnd_385945 : Nat := 4983230072969 + 3 ^ 40 * 385945 * 2
def baseEnd_385945 : Nat := 22019476799955302456953

theorem tailTrace_385945 : CollatzResearch.WordTrace tailWord_385945 prefixEnd_385945 22019476799955302456953 := by
  unfold tailWord_385945
  simp only [CollatzResearch.WordTrace]
  refine ⟨14076570586794654003415289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9384380391196436002276859 14076570586794654003415289)
  ·
    refine ⟨10557427940095990502561467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14076570586794654003415289 10557427940095990502561467)
    ·
      refine ⟨15836141910143985753842201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10557427940095990502561467 15836141910143985753842201)
      ·
        refine ⟨11877106432607989315381651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15836141910143985753842201 11877106432607989315381651)
        ·
          refine ⟨17815659648911983973072477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11877106432607989315381651 17815659648911983973072477)
          ·
            refine ⟨6680872368341993989902179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17815659648911983973072477 6680872368341993989902179)
            ·
              refine ⟨10021308552512990984853269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6680872368341993989902179 10021308552512990984853269)
              ·
                refine ⟨469748838399046452414997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10021308552512990984853269 469748838399046452414997)
                ·
                  refine ⟨22019476799955302456953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 469748838399046452414997 22019476799955302456953)
                  ·
                    rfl

theorem cell23_385945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 6].length) (baseStart_385945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385945 prefixEnd_385945 := by exact prefixLift 385945
  have htrace : WordTrace (prefixWord ++ tailWord_385945) baseStart_385945 baseEnd_385945 := by
    simpa [prefixWord, tailWord_385945, baseEnd_385945] using wordTrace_append hprefix tailTrace_385945
  have hstable : (prefixWord ++ tailWord_385945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385945).length < 2 ^ (prefixWord ++ tailWord_385945).sum := by decide
  have hdescent : baseEnd_385945 < baseStart_385945 := by decide
  rcases family_descends (prefixWord ++ tailWord_385945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385999 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 2, 3, 2]
def baseStart_385999 : Nat := 118140960795 + 385999 * 2 ^ 59
def prefixEnd_385999 : Nat := 4983230072969 + 3 ^ 40 * 385999 * 2
def baseEnd_385999 : Nat := 198203019154940510837329

theorem tailTrace_385999 : CollatzResearch.WordTrace tailWord_385999 prefixEnd_385999 198203019154940510837329 := by
  unfold tailWord_385999
  simp only [CollatzResearch.WordTrace]
  refine ⟨14078540128599021225881051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9385693419066014150587367 14078540128599021225881051)
  ·
    refine ⟨21117810192898531838821577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14078540128599021225881051 21117810192898531838821577)
    ·
      refine ⟨15838357644673898879116183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21117810192898531838821577 15838357644673898879116183)
      ·
        refine ⟨23757536467010848318674275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15838357644673898879116183 23757536467010848318674275)
        ·
          refine ⟨35636304700516272478011413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23757536467010848318674275 35636304700516272478011413)
          ·
            refine ⟨1670451782836700272406785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35636304700516272478011413 1670451782836700272406785)
            ·
              refine ⟨1252838837127525204305089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1670451782836700272406785 1252838837127525204305089)
              ·
                refine ⟨939629127845643903228817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252838837127525204305089 939629127845643903228817)
                ·
                  refine ⟨704721845884232927421613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 939629127845643903228817 704721845884232927421613)
                  ·
                    refine ⟨264270692206587347783105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 704721845884232927421613 264270692206587347783105)
                    ·
                      refine ⟨198203019154940510837329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 264270692206587347783105 198203019154940510837329)
                      ·
                        rfl

theorem cell23_385999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 3, 2].length) (baseStart_385999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_385999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_385999 prefixEnd_385999 := by exact prefixLift 385999
  have htrace : WordTrace (prefixWord ++ tailWord_385999) baseStart_385999 baseEnd_385999 := by
    simpa [prefixWord, tailWord_385999, baseEnd_385999] using wordTrace_append hprefix tailTrace_385999
  have hstable : (prefixWord ++ tailWord_385999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385999).length < 2 ^ (prefixWord ++ tailWord_385999).sum := by decide
  have hdescent : baseEnd_385999 < baseStart_385999 := by decide
  rcases family_descends (prefixWord ++ tailWord_385999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386056 : List Nat := [2, 1, 3, 2, 1, 5, 1, 2, 2, 4]
def baseStart_386056 : Nat := 118140960795 + 386056 * 2 ^ 59
def prefixEnd_386056 : Nat := 4983230072969 + 3 ^ 40 * 386056 * 2
def baseEnd_386056 : Nat := 66077429184082262608189

theorem tailTrace_386056 : CollatzResearch.WordTrace tailWord_386056 prefixEnd_386056 66077429184082262608189 := by
  unfold tailWord_386056
  simp only [CollatzResearch.WordTrace]
  refine ⟨7040309544696259980353011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9387079392928346640470681 7040309544696259980353011)
  ·
    refine ⟨10560464317044389970529517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7040309544696259980353011 10560464317044389970529517)
    ·
      refine ⟨3960174118891646238948569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10560464317044389970529517 3960174118891646238948569)
      ·
        refine ⟨2970130589168734679211427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3960174118891646238948569 2970130589168734679211427)
        ·
          refine ⟨4455195883753102018817141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970130589168734679211427 4455195883753102018817141)
          ·
            refine ⟨417674614101853314264107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4455195883753102018817141 417674614101853314264107)
            ·
              refine ⟨626511921152779971396161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417674614101853314264107 626511921152779971396161)
              ·
                refine ⟨469883940864584978547121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626511921152779971396161 469883940864584978547121)
                ·
                  refine ⟨352412955648438733910341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469883940864584978547121 352412955648438733910341)
                  ·
                    refine ⟨66077429184082262608189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 352412955648438733910341 66077429184082262608189)
                    ·
                      rfl

theorem cell23_386056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_386056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386056 prefixEnd_386056 := by exact prefixLift 386056
  have htrace : WordTrace (prefixWord ++ tailWord_386056) baseStart_386056 baseEnd_386056 := by
    simpa [prefixWord, tailWord_386056, baseEnd_386056] using wordTrace_append hprefix tailTrace_386056
  have hstable : (prefixWord ++ tailWord_386056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386056).length < 2 ^ (prefixWord ++ tailWord_386056).sum := by decide
  have hdescent : baseEnd_386056 < baseStart_386056 := by decide
  rcases family_descends (prefixWord ++ tailWord_386056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386065 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 1, 9]
def baseStart_386065 : Nat := 118140960795 + 386065 * 2 ^ 59
def prefixEnd_386065 : Nat := 4983230072969 + 3 ^ 40 * 386065 * 2
def baseEnd_386065 : Nat := 66078969626045750870675

theorem tailTrace_386065 : CollatzResearch.WordTrace tailWord_386065 prefixEnd_386065 66078969626045750870675 := by
  unfold tailWord_386065
  simp only [CollatzResearch.WordTrace]
  refine ⟨14080947346359914497783649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9387298230906609665189099 14080947346359914497783649)
  ·
    refine ⟨10560710509769935873337737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14080947346359914497783649 10560710509769935873337737)
    ·
      refine ⟨7920532882327451905003303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10560710509769935873337737 7920532882327451905003303)
      ·
        refine ⟨11880799323491177857504955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7920532882327451905003303 11880799323491177857504955)
        ·
          refine ⟨17821198985236766786257433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11880799323491177857504955 17821198985236766786257433)
          ·
            refine ⟨13365899238927575089693075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17821198985236766786257433 13365899238927575089693075)
            ·
              refine ⟨20048848858391362634539613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13365899238927575089693075 20048848858391362634539613)
              ·
                refine ⟨7518318321896760987952355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20048848858391362634539613 7518318321896760987952355)
                ·
                  refine ⟨11277477482845141481928533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7518318321896760987952355 11277477482845141481928533)
                  ·
                    refine ⟨66078969626045750870675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 11277477482845141481928533 66078969626045750870675)
                    ·
                      rfl

theorem cell23_386065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_386065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386065 prefixEnd_386065 := by exact prefixLift 386065
  have htrace : WordTrace (prefixWord ++ tailWord_386065) baseStart_386065 baseEnd_386065 := by
    simpa [prefixWord, tailWord_386065, baseEnd_386065] using wordTrace_append hprefix tailTrace_386065
  have hstable : (prefixWord ++ tailWord_386065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386065).length < 2 ^ (prefixWord ++ tailWord_386065).sum := by decide
  have hdescent : baseEnd_386065 < baseStart_386065 := by decide
  rcases family_descends (prefixWord ++ tailWord_386065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386076 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_386076 : Nat := 118140960795 + 386076 * 2 ^ 59
def prefixEnd_386076 : Nat := 4983230072969 + 3 ^ 40 * 386076 * 2
def baseEnd_386076 : Nat := 198242557165336709574475

theorem tailTrace_386076 : CollatzResearch.WordTrace tailWord_386076 prefixEnd_386076 198242557165336709574475 := by
  unfold tailWord_386076
  simp only [CollatzResearch.WordTrace]
  refine ⟨7040674274660031688217041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9387565699546708917622721 7040674274660031688217041)
  ·
    refine ⟨5280505705995023766162781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7040674274660031688217041 5280505705995023766162781)
    ·
      refine ⟨1980189639748133912311043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5280505705995023766162781 1980189639748133912311043)
      ·
        refine ⟨2970284459622200868466565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980189639748133912311043 2970284459622200868466565)
        ·
          refine ⟨556928336179162662837481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2970284459622200868466565 556928336179162662837481)
          ·
            refine ⟨417696252134371997128111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556928336179162662837481 417696252134371997128111)
            ·
              refine ⟨626544378201557995692167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417696252134371997128111 626544378201557995692167)
              ·
                refine ⟨939816567302336993538251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626544378201557995692167 939816567302336993538251)
                ·
                  refine ⟨1409724850953505490307377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 939816567302336993538251 1409724850953505490307377)
                  ·
                    refine ⟨1057293638215129117730533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1409724850953505490307377 1057293638215129117730533)
                    ·
                      refine ⟨198242557165336709574475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1057293638215129117730533 198242557165336709574475)
                      ·
                        rfl

theorem cell23_386076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_386076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386076 prefixEnd_386076 := by exact prefixLift 386076
  have htrace : WordTrace (prefixWord ++ tailWord_386076) baseStart_386076 baseEnd_386076 := by
    simpa [prefixWord, tailWord_386076, baseEnd_386076] using wordTrace_append hprefix tailTrace_386076
  have hstable : (prefixWord ++ tailWord_386076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386076).length < 2 ^ (prefixWord ++ tailWord_386076).sum := by decide
  have hdescent : baseEnd_386076 < baseStart_386076 := by decide
  rcases family_descends (prefixWord ++ tailWord_386076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386079 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 3]
def baseStart_386079 : Nat := 118140960795 + 386079 * 2 ^ 59
def prefixEnd_386079 : Nat := 4983230072969 + 3 ^ 40 * 386079 * 2
def baseEnd_386079 : Nat := 198244097607300197836961

theorem tailTrace_386079 : CollatzResearch.WordTrace tailWord_386079 prefixEnd_386079 198244097607300197836961 := by
  unfold tailWord_386079
  simp only [CollatzResearch.WordTrace]
  refine ⟨14081457968309194888793291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9387638645539463259195527 14081457968309194888793291)
  ·
    refine ⟨21122186952463792333189937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14081457968309194888793291 21122186952463792333189937)
    ·
      refine ⟨15841640214347844249892453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21122186952463792333189937 15841640214347844249892453)
      ·
        refine ⟨2970307540190220796854835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15841640214347844249892453 2970307540190220796854835)
        ·
          refine ⟨4455461310285331195282253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970307540190220796854835 4455461310285331195282253)
          ·
            refine ⟨1670797991356999198230845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4455461310285331195282253 1670797991356999198230845)
            ·
              refine ⟨626549246758874699336567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1670797991356999198230845 626549246758874699336567)
              ·
                refine ⟨939823870138312049004851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626549246758874699336567 939823870138312049004851)
                ·
                  refine ⟨1409735805207468073507277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 939823870138312049004851 1409735805207468073507277)
                  ·
                    refine ⟨528650926952800527565229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1409735805207468073507277 528650926952800527565229)
                    ·
                      refine ⟨198244097607300197836961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 528650926952800527565229 198244097607300197836961)
                      ·
                        rfl

theorem cell23_386079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_386079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386079 prefixEnd_386079 := by exact prefixLift 386079
  have htrace : WordTrace (prefixWord ++ tailWord_386079) baseStart_386079 baseEnd_386079 := by
    simpa [prefixWord, tailWord_386079, baseEnd_386079] using wordTrace_append hprefix tailTrace_386079
  have hstable : (prefixWord ++ tailWord_386079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386079).length < 2 ^ (prefixWord ++ tailWord_386079).sum := by decide
  have hdescent : baseEnd_386079 < baseStart_386079 := by decide
  rcases family_descends (prefixWord ++ tailWord_386079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386106 : List Nat := [3, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2]
def baseStart_386106 : Nat := 118140960795 + 386106 * 2 ^ 59
def prefixEnd_386106 : Nat := 4983230072969 + 3 ^ 40 * 386106 * 2
def baseEnd_386106 : Nat := 198257961584971592199337

theorem tailTrace_386106 : CollatzResearch.WordTrace tailWord_386106 prefixEnd_386106 198257961584971592199337 := by
  unfold tailWord_386106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3520610684802844625006543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9388295159474252333350781 3520610684802844625006543)
  ·
    refine ⟨5280916027204266937509815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3520610684802844625006543 5280916027204266937509815)
    ·
      refine ⟨7921374040806400406264723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5280916027204266937509815 7921374040806400406264723)
      ·
        refine ⟨11882061061209600609397085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7921374040806400406264723 11882061061209600609397085)
        ·
          refine ⟨4455772897953600228523907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11882061061209600609397085 4455772897953600228523907)
          ·
            refine ⟨6683659346930400342785861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455772897953600228523907 6683659346930400342785861)
            ·
              refine ⟨1253186127549450064272349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6683659346930400342785861 1253186127549450064272349)
              ·
                refine ⟨469944797831043774102131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1253186127549450064272349 469944797831043774102131)
                ·
                  refine ⟨704917196746565661153197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469944797831043774102131 704917196746565661153197)
                  ·
                    refine ⟨264343948779962122932449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 704917196746565661153197 264343948779962122932449)
                    ·
                      refine ⟨198257961584971592199337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 264343948779962122932449 198257961584971592199337)
                      ·
                        rfl

theorem cell23_386106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2].length) (baseStart_386106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386106 prefixEnd_386106 := by exact prefixLift 386106
  have htrace : WordTrace (prefixWord ++ tailWord_386106) baseStart_386106 baseEnd_386106 := by
    simpa [prefixWord, tailWord_386106, baseEnd_386106] using wordTrace_append hprefix tailTrace_386106
  have hstable : (prefixWord ++ tailWord_386106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386106).length < 2 ^ (prefixWord ++ tailWord_386106).sum := by decide
  have hdescent : baseEnd_386106 < baseStart_386106 := by decide
  rcases family_descends (prefixWord ++ tailWord_386106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386130 : List Nat := [3, 2, 2, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_386130 : Nat := 118140960795 + 386130 * 2 ^ 59
def prefixEnd_386130 : Nat := 4983230072969 + 3 ^ 40 * 386130 * 2
def baseEnd_386130 : Nat := 198270285120679498299227

theorem tailTrace_386130 : CollatzResearch.WordTrace tailWord_386130 prefixEnd_386130 198270285120679498299227 := by
  unfold tailWord_386130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3520829522781107649724961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9388878727416287065933229 3520829522781107649724961)
  ·
    refine ⟨2640622142085830737293721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3520829522781107649724961 2640622142085830737293721)
    ·
      refine ⟨1980466606564373052970291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2640622142085830737293721 1980466606564373052970291)
      ·
        refine ⟨2970699909846559579455437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980466606564373052970291 2970699909846559579455437)
        ·
          refine ⟨1114012466192459842295789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2970699909846559579455437 1114012466192459842295789)
          ·
            refine ⟨417754674822172440860921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1114012466192459842295789 417754674822172440860921)
            ·
              refine ⟨313316006116629330645691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417754674822172440860921 313316006116629330645691)
              ·
                refine ⟨469974009174943995968537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313316006116629330645691 469974009174943995968537)
                ·
                  refine ⟨352480506881207996976403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469974009174943995968537 352480506881207996976403)
                  ·
                    refine ⟨528720760321811995464605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 352480506881207996976403 528720760321811995464605)
                    ·
                      refine ⟨198270285120679498299227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 528720760321811995464605 198270285120679498299227)
                      ·
                        rfl

theorem cell23_386130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_386130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386130 prefixEnd_386130 := by exact prefixLift 386130
  have htrace : WordTrace (prefixWord ++ tailWord_386130) baseStart_386130 baseEnd_386130 := by
    simpa [prefixWord, tailWord_386130, baseEnd_386130] using wordTrace_append hprefix tailTrace_386130
  have hstable : (prefixWord ++ tailWord_386130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386130).length < 2 ^ (prefixWord ++ tailWord_386130).sum := by decide
  have hdescent : baseEnd_386130 < baseStart_386130 := by decide
  rcases family_descends (prefixWord ++ tailWord_386130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386159 : List Nat := [1, 1, 2, 1, 3, 3, 2, 5, 5]
def baseStart_386159 : Nat := 118140960795 + 386159 * 2 ^ 59
def prefixEnd_386159 : Nat := 4983230072969 + 3 ^ 40 * 386159 * 2
def baseEnd_386159 : Nat := 22031686228851098315177

theorem tailTrace_386159 : CollatzResearch.WordTrace tailWord_386159 prefixEnd_386159 22031686228851098315177 := by
  unfold tailWord_386159
  simp only [CollatzResearch.WordTrace]
  refine ⟨14084375808019368551705531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9389583872012912367803687 14084375808019368551705531)
  ·
    refine ⟨21126563712029052827558297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14084375808019368551705531 21126563712029052827558297)
    ·
      refine ⟨15844922784021789620668723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21126563712029052827558297 15844922784021789620668723)
      ·
        refine ⟨23767384176032684431003085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15844922784021789620668723 23767384176032684431003085)
        ·
          refine ⟨8912769066012256661626157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23767384176032684431003085 8912769066012256661626157)
          ·
            refine ⟨3342288399754596248109809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8912769066012256661626157 3342288399754596248109809)
            ·
              refine ⟨2506716299815947186082357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3342288399754596248109809 2506716299815947186082357)
              ·
                refine ⟨235004653107745048695221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2506716299815947186082357 235004653107745048695221)
                ·
                  refine ⟨22031686228851098315177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 235004653107745048695221 22031686228851098315177)
                  ·
                    rfl

theorem cell23_386159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 5].length) (baseStart_386159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386159 prefixEnd_386159 := by exact prefixLift 386159
  have htrace : WordTrace (prefixWord ++ tailWord_386159) baseStart_386159 baseEnd_386159 := by
    simpa [prefixWord, tailWord_386159, baseEnd_386159] using wordTrace_append hprefix tailTrace_386159
  have hstable : (prefixWord ++ tailWord_386159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386159).length < 2 ^ (prefixWord ++ tailWord_386159).sum := by decide
  have hdescent : baseEnd_386159 < baseStart_386159 := by decide
  rcases family_descends (prefixWord ++ tailWord_386159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386176 : List Nat := [2, 1, 1, 2, 1, 3, 6, 2, 5]
def baseStart_386176 : Nat := 118140960795 + 386176 * 2 ^ 59
def prefixEnd_386176 : Nat := 4983230072969 + 3 ^ 40 * 386176 * 2
def baseEnd_386176 : Nat := 22032656136754035369335

theorem tailTrace_386176 : CollatzResearch.WordTrace tailWord_386176 prefixEnd_386176 22032656136754035369335 := by
  unfold tailWord_386176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7042497924478890227537191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9389997232638520303382921 7042497924478890227537191)
  ·
    refine ⟨10563746886718335341305787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7042497924478890227537191 10563746886718335341305787)
    ·
      refine ⟨15845620330077503011958681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10563746886718335341305787 15845620330077503011958681)
      ·
        refine ⟨11884215247558127258969011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15845620330077503011958681 11884215247558127258969011)
        ·
          refine ⟨17826322871337190888453517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11884215247558127258969011 17826322871337190888453517)
          ·
            refine ⟨6684871076751446583170069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17826322871337190888453517 6684871076751446583170069)
            ·
              refine ⟨313353331722724058586097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6684871076751446583170069 313353331722724058586097)
              ·
                refine ⟨235014998792043043939573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313353331722724058586097 235014998792043043939573)
                ·
                  refine ⟨22032656136754035369335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 235014998792043043939573 22032656136754035369335)
                  ·
                    rfl

theorem cell23_386176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 5].length) (baseStart_386176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386176 prefixEnd_386176 := by exact prefixLift 386176
  have htrace : WordTrace (prefixWord ++ tailWord_386176) baseStart_386176 baseEnd_386176 := by
    simpa [prefixWord, tailWord_386176, baseEnd_386176] using wordTrace_append hprefix tailTrace_386176
  have hstable : (prefixWord ++ tailWord_386176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386176).length < 2 ^ (prefixWord ++ tailWord_386176).sum := by decide
  have hdescent : baseEnd_386176 < baseStart_386176 := by decide
  rcases family_descends (prefixWord ++ tailWord_386176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386179 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 1, 7, 2]
def baseStart_386179 : Nat := 118140960795 + 386179 * 2 ^ 59
def prefixEnd_386179 : Nat := 4983230072969 + 3 ^ 40 * 386179 * 2
def baseEnd_386179 : Nat := 198295445672749806586501

theorem tailTrace_386179 : CollatzResearch.WordTrace tailWord_386179 prefixEnd_386179 198295445672749806586501 := by
  unfold tailWord_386179
  simp only [CollatzResearch.WordTrace]
  refine ⟨14085105267946911967433591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9390070178631274644955727 14085105267946911967433591)
  ·
    refine ⟨21127657901920367951150387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14085105267946911967433591 21127657901920367951150387)
    ·
      refine ⟨31691486852880551926725581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21127657901920367951150387 31691486852880551926725581)
      ·
        refine ⟨11884307569830206972522093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31691486852880551926725581 11884307569830206972522093)
        ·
          refine ⟨4456615338686327614695785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11884307569830206972522093 4456615338686327614695785)
          ·
            refine ⟨3342461504014745711021839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4456615338686327614695785 3342461504014745711021839)
            ·
              refine ⟨5013692256022118566532759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3342461504014745711021839 5013692256022118566532759)
              ·
                refine ⟨7520538384033177849799139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5013692256022118566532759 7520538384033177849799139)
                ·
                  refine ⟨11280807576049766774698709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7520538384033177849799139 11280807576049766774698709)
                  ·
                    refine ⟨264393927563666408782001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11280807576049766774698709 264393927563666408782001)
                    ·
                      refine ⟨198295445672749806586501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 264393927563666408782001 198295445672749806586501)
                      ·
                        rfl

theorem cell23_386179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 7, 2].length) (baseStart_386179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386179 prefixEnd_386179 := by exact prefixLift 386179
  have htrace : WordTrace (prefixWord ++ tailWord_386179) baseStart_386179 baseEnd_386179 := by
    simpa [prefixWord, tailWord_386179, baseEnd_386179] using wordTrace_append hprefix tailTrace_386179
  have hstable : (prefixWord ++ tailWord_386179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386179).length < 2 ^ (prefixWord ++ tailWord_386179).sum := by decide
  have hdescent : baseEnd_386179 < baseStart_386179 := by decide
  rcases family_descends (prefixWord ++ tailWord_386179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386206 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_386206 : Nat := 118140960795 + 386206 * 2 ^ 59
def prefixEnd_386206 : Nat := 4983230072969 + 3 ^ 40 * 386206 * 2
def baseEnd_386206 : Nat := 66103103216807066982959

theorem tailTrace_386206 : CollatzResearch.WordTrace tailWord_386206 prefixEnd_386206 66103103216807066982959 := by
  unfold tailWord_386206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1760761254856136947333309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9390726692566063719110981 1760761254856136947333309)
  ·
    refine ⟨660285470571051355249991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1760761254856136947333309 660285470571051355249991)
    ·
      refine ⟨990428205856577032874987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 660285470571051355249991 990428205856577032874987)
      ·
        refine ⟨1485642308784865549312481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 990428205856577032874987 1485642308784865549312481)
        ·
          refine ⟨1114231731588649161984361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1485642308784865549312481 1114231731588649161984361)
          ·
            refine ⟨835673798691486871488271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1114231731588649161984361 835673798691486871488271)
            ·
              refine ⟨1253510698037230307232407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835673798691486871488271 1253510698037230307232407)
              ·
                refine ⟨1880266047055845460848611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253510698037230307232407 1880266047055845460848611)
                ·
                  refine ⟨2820399070583768191272917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880266047055845460848611 2820399070583768191272917)
                  ·
                    refine ⟨66103103216807066982959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2820399070583768191272917 66103103216807066982959)
                    ·
                      rfl

theorem cell23_386206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_386206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386206 prefixEnd_386206 := by exact prefixLift 386206
  have htrace : WordTrace (prefixWord ++ tailWord_386206) baseStart_386206 baseEnd_386206 := by
    simpa [prefixWord, tailWord_386206, baseEnd_386206] using wordTrace_append hprefix tailTrace_386206
  have hstable : (prefixWord ++ tailWord_386206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386206).length < 2 ^ (prefixWord ++ tailWord_386206).sum := by decide
  have hdescent : baseEnd_386206 < baseStart_386206 := by decide
  rcases family_descends (prefixWord ++ tailWord_386206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386209 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_386209 : Nat := 118140960795 + 386209 * 2 ^ 59
def prefixEnd_386209 : Nat := 4983230072969 + 3 ^ 40 * 386209 * 2
def baseEnd_386209 : Nat := 198310850092384689211363

theorem tailTrace_386209 : CollatzResearch.WordTrace tailWord_386209 prefixEnd_386209 198310850092384689211363 := by
  unfold tailWord_386209
  simp only [CollatzResearch.WordTrace]
  refine ⟨14086199457838227091025681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9390799638558818060683787 14086199457838227091025681)
  ·
    refine ⟨10564649593378670318269261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14086199457838227091025681 10564649593378670318269261)
    ·
      refine ⟨3961743597517001369350973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10564649593378670318269261 3961743597517001369350973)
      ·
        refine ⟨1485653849068875513506615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3961743597517001369350973 1485653849068875513506615)
        ·
          refine ⟨2228480773603313270259923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1485653849068875513506615 2228480773603313270259923)
          ·
            refine ⟨3342721160404969905389885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2228480773603313270259923 3342721160404969905389885)
            ·
              refine ⟨1253520435151863714521207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3342721160404969905389885 1253520435151863714521207)
              ·
                refine ⟨1880280652727795571781811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253520435151863714521207 1880280652727795571781811)
                ·
                  refine ⟨2820420979091693357672717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880280652727795571781811 2820420979091693357672717)
                  ·
                    refine ⟨1057657867159385009127269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2820420979091693357672717 1057657867159385009127269)
                    ·
                      refine ⟨198310850092384689211363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1057657867159385009127269 198310850092384689211363)
                      ·
                        rfl

theorem cell23_386209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_386209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386209 prefixEnd_386209 := by exact prefixLift 386209
  have htrace : WordTrace (prefixWord ++ tailWord_386209) baseStart_386209 baseEnd_386209 := by
    simpa [prefixWord, tailWord_386209, baseEnd_386209] using wordTrace_append hprefix tailTrace_386209
  have hstable : (prefixWord ++ tailWord_386209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386209).length < 2 ^ (prefixWord ++ tailWord_386209).sum := by decide
  have hdescent : baseEnd_386209 < baseStart_386209 := by decide
  rcases family_descends (prefixWord ++ tailWord_386209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386226 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2]
def baseStart_386226 : Nat := 118140960795 + 386226 * 2 ^ 59
def prefixEnd_386226 : Nat := 4983230072969 + 3 ^ 40 * 386226 * 2
def baseEnd_386226 : Nat := 198319579263511122698785

theorem tailTrace_386226 : CollatzResearch.WordTrace tailWord_386226 prefixEnd_386226 198319579263511122698785 := by
  unfold tailWord_386226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3521704874694159748598633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9391212999184425996263021 3521704874694159748598633)
  ·
    refine ⟨2641278656020619811448975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3521704874694159748598633 2641278656020619811448975)
    ·
      refine ⟨3961917984030929717173463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2641278656020619811448975 3961917984030929717173463)
      ·
        refine ⟨5942876976046394575760195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3961917984030929717173463 5942876976046394575760195)
        ·
          refine ⟨8914315464069591863640293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5942876976046394575760195 8914315464069591863640293)
          ·
            refine ⟨1671434149513048474432555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8914315464069591863640293 1671434149513048474432555)
            ·
              refine ⟨2507151224269572711648833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671434149513048474432555 2507151224269572711648833)
              ·
                refine ⟨1880363418202179533736625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2507151224269572711648833 1880363418202179533736625)
                ·
                  refine ⟨1410272563651634650302469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1880363418202179533736625 1410272563651634650302469)
                  ·
                    refine ⟨264426105684681496931713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1410272563651634650302469 264426105684681496931713)
                    ·
                      refine ⟨198319579263511122698785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 264426105684681496931713 198319579263511122698785)
                      ·
                        rfl

theorem cell23_386226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_386226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386226 prefixEnd_386226 := by exact prefixLift 386226
  have htrace : WordTrace (prefixWord ++ tailWord_386226) baseStart_386226 baseEnd_386226 := by
    simpa [prefixWord, tailWord_386226, baseEnd_386226] using wordTrace_append hprefix tailTrace_386226
  have hstable : (prefixWord ++ tailWord_386226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386226).length < 2 ^ (prefixWord ++ tailWord_386226).sum := by decide
  have hdescent : baseEnd_386226 < baseStart_386226 := by decide
  rcases family_descends (prefixWord ++ tailWord_386226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386236 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 3, 4]
def baseStart_386236 : Nat := 118140960795 + 386236 * 2 ^ 59
def prefixEnd_386236 : Nat := 4983230072969 + 3 ^ 40 * 386236 * 2
def baseEnd_386236 : Nat := 66108238023352027857913

theorem tailTrace_386236 : CollatzResearch.WordTrace tailWord_386236 prefixEnd_386236 66108238023352027857913 := by
  unfold tailWord_386236
  simp only [CollatzResearch.WordTrace]
  refine ⟨7043592114370205351129281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9391456152493607134839041 7043592114370205351129281)
  ·
    refine ⟨5282694085777654013346961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7043592114370205351129281 5282694085777654013346961)
    ·
      refine ⟨3962020564333240510010221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5282694085777654013346961 3962020564333240510010221)
      ·
        refine ⟨1485757711624965191253833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3962020564333240510010221 1485757711624965191253833)
        ·
          refine ⟨1114318283718723893440375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1485757711624965191253833 1114318283718723893440375)
          ·
            refine ⟨1671477425578085840160563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114318283718723893440375 1671477425578085840160563)
            ·
              refine ⟨2507216138367128760240845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671477425578085840160563 2507216138367128760240845)
              ·
                refine ⟨940206051887673285090317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2507216138367128760240845 940206051887673285090317)
                ·
                  refine ⟨352577269457877481908869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940206051887673285090317 352577269457877481908869)
                  ·
                    refine ⟨66108238023352027857913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 352577269457877481908869 66108238023352027857913)
                    ·
                      rfl

theorem cell23_386236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_386236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386236 prefixEnd_386236 := by exact prefixLift 386236
  have htrace : WordTrace (prefixWord ++ tailWord_386236) baseStart_386236 baseEnd_386236 := by
    simpa [prefixWord, tailWord_386236, baseEnd_386236] using wordTrace_append hprefix tailTrace_386236
  have hstable : (prefixWord ++ tailWord_386236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386236).length < 2 ^ (prefixWord ++ tailWord_386236).sum := by decide
  have hdescent : baseEnd_386236 < baseStart_386236 := by decide
  rcases family_descends (prefixWord ++ tailWord_386236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386276 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_386276 : Nat := 118140960795 + 386276 * 2 ^ 59
def prefixEnd_386276 : Nat := 4983230072969 + 3 ^ 40 * 386276 * 2
def baseEnd_386276 : Nat := 198345253296235927073555

theorem tailTrace_386276 : CollatzResearch.WordTrace tailWord_386276 prefixEnd_386276 198345253296235927073555 := by
  unfold tailWord_386276
  simp only [CollatzResearch.WordTrace]
  refine ⟨7044321574297748766857341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9392428765730331689143121 7044321574297748766857341)
  ·
    refine ⟨2641620590361655787571503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7044321574297748766857341 2641620590361655787571503)
    ·
      refine ⟨3962430885542483681357255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2641620590361655787571503 3962430885542483681357255)
      ·
        refine ⟨5943646328313725522035883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3962430885542483681357255 5943646328313725522035883)
        ·
          refine ⟨8915469492470588283053825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5943646328313725522035883 8915469492470588283053825)
          ·
            refine ⟨6686602119352941212290369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8915469492470588283053825 6686602119352941212290369)
            ·
              refine ⟨5014951589514705909217777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6686602119352941212290369 5014951589514705909217777)
              ·
                refine ⟨3761213692136029431913333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5014951589514705909217777 3761213692136029431913333)
                ·
                  refine ⟨352613783637752759241875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3761213692136029431913333 352613783637752759241875)
                  ·
                    refine ⟨528920675456629138862813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 352613783637752759241875 528920675456629138862813)
                    ·
                      refine ⟨198345253296235927073555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 528920675456629138862813 198345253296235927073555)
                      ·
                        rfl

theorem cell23_386276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_386276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386276 prefixEnd_386276 := by exact prefixLift 386276
  have htrace : WordTrace (prefixWord ++ tailWord_386276) baseStart_386276 baseEnd_386276 := by
    simpa [prefixWord, tailWord_386276, baseEnd_386276] using wordTrace_append hprefix tailTrace_386276
  have hstable : (prefixWord ++ tailWord_386276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386276).length < 2 ^ (prefixWord ++ tailWord_386276).sum := by decide
  have hdescent : baseEnd_386276 < baseStart_386276 := by decide
  rcases family_descends (prefixWord ++ tailWord_386276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386300 : List Nat := [2, 2, 2, 1, 6, 1, 2, 1, 6]
def baseStart_386300 : Nat := 118140960795 + 386300 * 2 ^ 59
def prefixEnd_386300 : Nat := 4983230072969 + 3 ^ 40 * 386300 * 2
def baseEnd_386300 : Nat := 22039730759104870352605

theorem tailTrace_386300 : CollatzResearch.WordTrace tailWord_386300 prefixEnd_386300 22039730759104870352605 := by
  unfold tailWord_386300
  simp only [CollatzResearch.WordTrace]
  refine ⟨7044759250254274816294177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9393012333672366421725569 7044759250254274816294177)
  ·
    refine ⟨5283569437690706112220633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7044759250254274816294177 5283569437690706112220633)
    ·
      refine ⟨3962677078268029584165475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5283569437690706112220633 3962677078268029584165475)
      ·
        refine ⟨5944015617402044376248213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3962677078268029584165475 5944015617402044376248213)
        ·
          refine ⟨278625732065720830136635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5944015617402044376248213 278625732065720830136635)
          ·
            refine ⟨417938598098581245204953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278625732065720830136635 417938598098581245204953)
            ·
              refine ⟨313453948573935933903715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417938598098581245204953 313453948573935933903715)
              ·
                refine ⟨470180922860903900855573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313453948573935933903715 470180922860903900855573)
                ·
                  refine ⟨22039730759104870352605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 470180922860903900855573 22039730759104870352605)
                  ·
                    rfl

theorem cell23_386300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 6].length) (baseStart_386300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386300 prefixEnd_386300 := by exact prefixLift 386300
  have htrace : WordTrace (prefixWord ++ tailWord_386300) baseStart_386300 baseEnd_386300 := by
    simpa [prefixWord, tailWord_386300, baseEnd_386300] using wordTrace_append hprefix tailTrace_386300
  have hstable : (prefixWord ++ tailWord_386300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386300).length < 2 ^ (prefixWord ++ tailWord_386300).sum := by decide
  have hdescent : baseEnd_386300 < baseStart_386300 := by decide
  rcases family_descends (prefixWord ++ tailWord_386300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386309 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 1, 6]
def baseStart_386309 : Nat := 118140960795 + 386309 * 2 ^ 59
def prefixEnd_386309 : Nat := 4983230072969 + 3 ^ 40 * 386309 * 2
def baseEnd_386309 : Nat := 66120732719278099320301

theorem tailTrace_386309 : CollatzResearch.WordTrace tailWord_386309 prefixEnd_386309 66120732719278099320301 := by
  unfold tailWord_386309
  simp only [CollatzResearch.WordTrace]
  refine ⟨14089846757475944169665981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9393231171650629446443987 14089846757475944169665981)
  ·
    refine ⟨5283692534053479063624743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14089846757475944169665981 5283692534053479063624743)
    ·
      refine ⟨7925538801080218595437115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5283692534053479063624743 7925538801080218595437115)
      ·
        refine ⟨11888308201620327893155673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7925538801080218595437115 11888308201620327893155673)
        ·
          refine ⟨8916231151215245919866755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11888308201620327893155673 8916231151215245919866755)
          ·
            refine ⟨13374346726822868879800133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8916231151215245919866755 13374346726822868879800133)
            ·
              refine ⟨2507690011279287914962525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13374346726822868879800133 2507690011279287914962525)
              ·
                refine ⟨940383754229732968110947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2507690011279287914962525 940383754229732968110947)
                ·
                  refine ⟨1410575631344599452166421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940383754229732968110947 1410575631344599452166421)
                  ·
                    refine ⟨66120732719278099320301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1410575631344599452166421 66120732719278099320301)
                    ·
                      rfl

theorem cell23_386309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_386309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386309 prefixEnd_386309 := by exact prefixLift 386309
  have htrace : WordTrace (prefixWord ++ tailWord_386309) baseStart_386309 baseEnd_386309 := by
    simpa [prefixWord, tailWord_386309, baseEnd_386309] using wordTrace_append hprefix tailTrace_386309
  have hstable : (prefixWord ++ tailWord_386309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386309).length < 2 ^ (prefixWord ++ tailWord_386309).sum := by decide
  have hdescent : baseEnd_386309 < baseStart_386309 := by decide
  rcases family_descends (prefixWord ++ tailWord_386309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386316 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_386316 : Nat := 118140960795 + 386316 * 2 ^ 59
def prefixEnd_386316 : Nat := 4983230072969 + 3 ^ 40 * 386316 * 2
def baseEnd_386316 : Nat := 198365792522415770573371

theorem tailTrace_386316 : CollatzResearch.WordTrace tailWord_386316 prefixEnd_386316 198365792522415770573371 := by
  unfold tailWord_386316
  simp only [CollatzResearch.WordTrace]
  refine ⟨7045051034225292182585401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9393401378967056243447201 7045051034225292182585401)
  ·
    refine ⟨5283788275668969136939051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7045051034225292182585401 5283788275668969136939051)
    ·
      refine ⟨7925682413503453705408577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5283788275668969136939051 7925682413503453705408577)
      ·
        refine ⟨5944261810127590279056433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7925682413503453705408577 5944261810127590279056433)
        ·
          refine ⟨4458196357595692709292325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5944261810127590279056433 4458196357595692709292325)
          ·
            refine ⟨835911817049192382992311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4458196357595692709292325 835911817049192382992311)
            ·
              refine ⟨1253867725573788574488467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835911817049192382992311 1253867725573788574488467)
              ·
                refine ⟨1880801588360682861732701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253867725573788574488467 1880801588360682861732701)
                ·
                  refine ⟨705300595635256073149763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1880801588360682861732701 705300595635256073149763)
                  ·
                    refine ⟨1057950893452884109724645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 705300595635256073149763 1057950893452884109724645)
                    ·
                      refine ⟨198365792522415770573371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1057950893452884109724645 198365792522415770573371)
                      ·
                        rfl

theorem cell23_386316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_386316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386316 prefixEnd_386316 := by exact prefixLift 386316
  have htrace : WordTrace (prefixWord ++ tailWord_386316) baseStart_386316 baseEnd_386316 := by
    simpa [prefixWord, tailWord_386316, baseEnd_386316] using wordTrace_append hprefix tailTrace_386316
  have hstable : (prefixWord ++ tailWord_386316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386316).length < 2 ^ (prefixWord ++ tailWord_386316).sum := by decide
  have hdescent : baseEnd_386316 < baseStart_386316 := by decide
  rcases family_descends (prefixWord ++ tailWord_386316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386344 : List Nat := [2, 1, 5, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_386344 : Nat := 118140960795 + 386344 * 2 ^ 59
def prefixEnd_386344 : Nat := 4983230072969 + 3 ^ 40 * 386344 * 2
def baseEnd_386344 : Nat := 198380169980741661023243

theorem tailTrace_386344 : CollatzResearch.WordTrace tailWord_386344 prefixEnd_386344 198380169980741661023243 := by
  unfold tailWord_386344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7045561656174572573595043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9394082208232763431460057 7045561656174572573595043)
  ·
    refine ⟨10568342484261858860392565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7045561656174572573595043 10568342484261858860392565)
    ·
      refine ⟨990782107899549268161803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10568342484261858860392565 990782107899549268161803)
      ·
        refine ⟨1486173161849323902242705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 990782107899549268161803 1486173161849323902242705)
        ·
          refine ⟨1114629871386992926682029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1486173161849323902242705 1114629871386992926682029)
          ·
            refine ⟨417986201770122347505761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1114629871386992926682029 417986201770122347505761)
            ·
              refine ⟨313489651327591760629321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417986201770122347505761 313489651327591760629321)
              ·
                refine ⟨235117238495693820471991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313489651327591760629321 235117238495693820471991)
                ·
                  refine ⟨352675857743540730707987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235117238495693820471991 352675857743540730707987)
                  ·
                    refine ⟨529013786615311096061981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 352675857743540730707987 529013786615311096061981)
                    ·
                      refine ⟨198380169980741661023243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 529013786615311096061981 198380169980741661023243)
                      ·
                        rfl

theorem cell23_386344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_386344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386344 prefixEnd_386344 := by exact prefixLift 386344
  have htrace : WordTrace (prefixWord ++ tailWord_386344) baseStart_386344 baseEnd_386344 := by
    simpa [prefixWord, tailWord_386344, baseEnd_386344] using wordTrace_append hprefix tailTrace_386344
  have hstable : (prefixWord ++ tailWord_386344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386344).length < 2 ^ (prefixWord ++ tailWord_386344).sum := by decide
  have hdescent : baseEnd_386344 < baseStart_386344 := by decide
  rcases family_descends (prefixWord ++ tailWord_386344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386400 : List Nat := [2, 1, 1, 3, 4, 1, 3, 2, 2, 1, 3]
def baseStart_386400 : Nat := 118140960795 + 386400 * 2 ^ 59
def prefixEnd_386400 : Nat := 4983230072969 + 3 ^ 40 * 386400 * 2
def baseEnd_386400 : Nat := 198408924897393441922985

theorem tailTrace_386400 : CollatzResearch.WordTrace tailWord_386400 prefixEnd_386400 198408924897393441922985 := by
  unfold tailWord_386400
  simp only [CollatzResearch.WordTrace]
  refine ⟨7046582900073133355614327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9395443866764177807485769 7046582900073133355614327)
  ·
    refine ⟨10569874350109700033421491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7046582900073133355614327 10569874350109700033421491)
    ·
      refine ⟨15854811525164550050132237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10569874350109700033421491 15854811525164550050132237)
      ·
        refine ⟨5945554321936706268799589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15854811525164550050132237 5945554321936706268799589)
        ·
          refine ⟨1114791435363132425399923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5945554321936706268799589 1114791435363132425399923)
          ·
            refine ⟨1672187153044698638099885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114791435363132425399923 1672187153044698638099885)
            ·
              refine ⟨627070182391761989287457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1672187153044698638099885 627070182391761989287457)
              ·
                refine ⟨470302636793821491965593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627070182391761989287457 470302636793821491965593)
                ·
                  refine ⟨352726977595366118974195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470302636793821491965593 352726977595366118974195)
                  ·
                    refine ⟨529090466393049178461293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 352726977595366118974195 529090466393049178461293)
                    ·
                      refine ⟨198408924897393441922985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 529090466393049178461293 198408924897393441922985)
                      ·
                        rfl

theorem cell23_386400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_386400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386400 prefixEnd_386400 := by exact prefixLift 386400
  have htrace : WordTrace (prefixWord ++ tailWord_386400) baseStart_386400 baseEnd_386400 := by
    simpa [prefixWord, tailWord_386400, baseEnd_386400] using wordTrace_append hprefix tailTrace_386400
  have hstable : (prefixWord ++ tailWord_386400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386400).length < 2 ^ (prefixWord ++ tailWord_386400).sum := by decide
  have hdescent : baseEnd_386400 < baseStart_386400 := by decide
  rcases family_descends (prefixWord ++ tailWord_386400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386409 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 5]
def baseStart_386409 : Nat := 118140960795 + 386409 * 2 ^ 59
def prefixEnd_386409 : Nat := 4983230072969 + 3 ^ 40 * 386409 * 2
def baseEnd_386409 : Nat := 198413546223283906710443

theorem tailTrace_386409 : CollatzResearch.WordTrace tailWord_386409 prefixEnd_386409 198413546223283906710443 := by
  unfold tailWord_386409
  simp only [CollatzResearch.WordTrace]
  refine ⟨14093494057113661248306281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9395662704742440832204187 14093494057113661248306281)
  ·
    refine ⟨10570120542835245936229711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14093494057113661248306281 10570120542835245936229711)
    ·
      refine ⟨15855180814252868904344567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10570120542835245936229711 15855180814252868904344567)
      ·
        refine ⟨23782771221379303356516851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15855180814252868904344567 23782771221379303356516851)
        ·
          refine ⟨35674156832068955034775277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23782771221379303356516851 35674156832068955034775277)
          ·
            refine ⟨13377808812025858138040729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35674156832068955034775277 13377808812025858138040729)
            ·
              refine ⟨10033356609019393603530547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13377808812025858138040729 10033356609019393603530547)
              ·
                refine ⟨15050034913529090405295821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10033356609019393603530547 15050034913529090405295821)
                ·
                  refine ⟨5643763092573408901985933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15050034913529090405295821 5643763092573408901985933)
                  ·
                    refine ⟨2116411159715028338244725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5643763092573408901985933 2116411159715028338244725)
                    ·
                      refine ⟨198413546223283906710443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2116411159715028338244725 198413546223283906710443)
                      ·
                        rfl

theorem cell23_386409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_386409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386409 prefixEnd_386409 := by exact prefixLift 386409
  have htrace : WordTrace (prefixWord ++ tailWord_386409) baseStart_386409 baseEnd_386409 := by
    simpa [prefixWord, tailWord_386409, baseEnd_386409] using wordTrace_append hprefix tailTrace_386409
  have hstable : (prefixWord ++ tailWord_386409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386409).length < 2 ^ (prefixWord ++ tailWord_386409).sum := by decide
  have hdescent : baseEnd_386409 < baseStart_386409 := by decide
  rcases family_descends (prefixWord ++ tailWord_386409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386440 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 4, 2, 2]
def baseStart_386440 : Nat := 118140960795 + 386440 * 2 ^ 59
def prefixEnd_386440 : Nat := 4983230072969 + 3 ^ 40 * 386440 * 2
def baseEnd_386440 : Nat := 198429464123573285422801

theorem tailTrace_386440 : CollatzResearch.WordTrace tailWord_386440 prefixEnd_386440 198429464123573285422801 := by
  unfold tailWord_386440
  simp only [CollatzResearch.WordTrace]
  refine ⟨7047312360000676771342387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9396416480000902361789849 7047312360000676771342387)
  ·
    refine ⟨10570968540001015157013581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7047312360000676771342387 10570968540001015157013581)
    ·
      refine ⟨3964113202500380683880093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10570968540001015157013581 3964113202500380683880093)
      ·
        refine ⟨1486542450937642756455035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3964113202500380683880093 1486542450937642756455035)
        ·
          refine ⟨2229813676406464134682553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486542450937642756455035 2229813676406464134682553)
          ·
            refine ⟨1672360257304848101011915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2229813676406464134682553 1672360257304848101011915)
            ·
              refine ⟨2508540385957272151517873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1672360257304848101011915 2508540385957272151517873)
              ·
                refine ⟨1881405289467954113638405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2508540385957272151517873 1881405289467954113638405)
                ·
                  refine ⟨352763491775241396307201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881405289467954113638405 352763491775241396307201)
                  ·
                    refine ⟨264572618831431047230401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 352763491775241396307201 264572618831431047230401)
                    ·
                      refine ⟨198429464123573285422801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 264572618831431047230401 198429464123573285422801)
                      ·
                        rfl

theorem cell23_386440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_386440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386440 prefixEnd_386440 := by exact prefixLift 386440
  have htrace : WordTrace (prefixWord ++ tailWord_386440) baseStart_386440 baseEnd_386440 := by
    simpa [prefixWord, tailWord_386440, baseEnd_386440] using wordTrace_append hprefix tailTrace_386440
  have hstable : (prefixWord ++ tailWord_386440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386440).length < 2 ^ (prefixWord ++ tailWord_386440).sum := by decide
  have hdescent : baseEnd_386440 < baseStart_386440 := by decide
  rcases family_descends (prefixWord ++ tailWord_386440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386463 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 7]
def baseStart_386463 : Nat := 118140960795 + 386463 * 2 ^ 59
def prefixEnd_386463 : Nat := 4983230072969 + 3 ^ 40 * 386463 * 2
def baseEnd_386463 : Nat := 22049030464291855048355

theorem tailTrace_386463 : CollatzResearch.WordTrace tailWord_386463 prefixEnd_386463 22049030464291855048355 := by
  unfold tailWord_386463
  simp only [CollatzResearch.WordTrace]
  refine ⟨14095463598918028470772043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9396975732612018980514695 14095463598918028470772043)
  ·
    refine ⟨21143195398377042706158065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14095463598918028470772043 21143195398377042706158065)
    ·
      refine ⟨15857396548782782029618549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21143195398377042706158065 15857396548782782029618549)
      ·
        refine ⟨1486630926448385815276739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15857396548782782029618549 1486630926448385815276739)
        ·
          refine ⟨2229946389672578722915109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486630926448385815276739 2229946389672578722915109)
          ·
            refine ⟨418114948063608510546583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2229946389672578722915109 418114948063608510546583)
            ·
              refine ⟨627172422095412765819875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418114948063608510546583 627172422095412765819875)
              ·
                refine ⟨940758633143119148729813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627172422095412765819875 940758633143119148729813)
                ·
                  refine ⟨22049030464291855048355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 940758633143119148729813 22049030464291855048355)
                  ·
                    rfl

theorem cell23_386463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 7].length) (baseStart_386463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386463 prefixEnd_386463 := by exact prefixLift 386463
  have htrace : WordTrace (prefixWord ++ tailWord_386463) baseStart_386463 baseEnd_386463 := by
    simpa [prefixWord, tailWord_386463, baseEnd_386463] using wordTrace_append hprefix tailTrace_386463
  have hstable : (prefixWord ++ tailWord_386463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386463).length < 2 ^ (prefixWord ++ tailWord_386463).sum := by decide
  have hdescent : baseEnd_386463 < baseStart_386463 := by decide
  rcases family_descends (prefixWord ++ tailWord_386463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386493 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_386493 : Nat := 118140960795 + 386493 * 2 ^ 59
def prefixEnd_386493 : Nat := 4983230072969 + 3 ^ 40 * 386493 * 2
def baseEnd_386493 : Nat := 66152226199420526020019

theorem tailTrace_386493 : CollatzResearch.WordTrace tailWord_386493 prefixEnd_386493 66152226199420526020019 := by
  unfold tailWord_386493
  simp only [CollatzResearch.WordTrace]
  refine ⟨14096557788809343594364133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9397705192539562396242755 14096557788809343594364133)
  ·
    refine ⟨2643104585401751923943275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14096557788809343594364133 2643104585401751923943275)
    ·
      refine ⟨3964656878102627885914913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2643104585401751923943275 3964656878102627885914913)
      ·
        refine ⟨2973492658576970914436185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3964656878102627885914913 2973492658576970914436185)
        ·
          refine ⟨2230119493932728185827139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2973492658576970914436185 2230119493932728185827139)
          ·
            refine ⟨3345179240899092278740709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230119493932728185827139 3345179240899092278740709)
            ·
              refine ⟨627221107668579802263883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3345179240899092278740709 627221107668579802263883)
              ·
                refine ⟨940831661502869703395825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627221107668579802263883 940831661502869703395825)
                ·
                  refine ⟨705623746127152277546869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 940831661502869703395825 705623746127152277546869)
                  ·
                    refine ⟨66152226199420526020019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 705623746127152277546869 66152226199420526020019)
                    ·
                      rfl

theorem cell23_386493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_386493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386493 prefixEnd_386493 := by exact prefixLift 386493
  have htrace : WordTrace (prefixWord ++ tailWord_386493) baseStart_386493 baseEnd_386493 := by
    simpa [prefixWord, tailWord_386493, baseEnd_386493] using wordTrace_append hprefix tailTrace_386493
  have hstable : (prefixWord ++ tailWord_386493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386493).length < 2 ^ (prefixWord ++ tailWord_386493).sum := by decide
  have hdescent : baseEnd_386493 < baseStart_386493 := by decide
  rcases family_descends (prefixWord ++ tailWord_386493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386496 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 4]
def baseStart_386496 : Nat := 118140960795 + 386496 * 2 ^ 59
def prefixEnd_386496 : Nat := 4983230072969 + 3 ^ 40 * 386496 * 2
def baseEnd_386496 : Nat := 198458219040225066322543

theorem tailTrace_386496 : CollatzResearch.WordTrace tailWord_386496 prefixEnd_386496 198458219040225066322543 := by
  unfold tailWord_386496
  simp only [CollatzResearch.WordTrace]
  refine ⟨7048333603899237553361671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9397778138532316737815561 7048333603899237553361671)
  ·
    refine ⟨10572500405848856330042507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7048333603899237553361671 10572500405848856330042507)
    ·
      refine ⟨15858750608773284495063761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10572500405848856330042507 15858750608773284495063761)
      ·
        refine ⟨11894062956579963371297821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15858750608773284495063761 11894062956579963371297821)
        ·
          refine ⟨4460273608717486264236683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11894062956579963371297821 4460273608717486264236683)
          ·
            refine ⟨6690410413076229396355025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460273608717486264236683 6690410413076229396355025)
            ·
              refine ⟨5017807809807172047266269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6690410413076229396355025 5017807809807172047266269)
              ·
                refine ⟨1881677928677689517724851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5017807809807172047266269 1881677928677689517724851)
                ·
                  refine ⟨2822516893016534276587277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881677928677689517724851 2822516893016534276587277)
                  ·
                    refine ⟨1058443834881200353720229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2822516893016534276587277 1058443834881200353720229)
                    ·
                      refine ⟨198458219040225066322543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1058443834881200353720229 198458219040225066322543)
                      ·
                        rfl

theorem cell23_386496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_386496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386496 prefixEnd_386496 := by exact prefixLift 386496
  have htrace : WordTrace (prefixWord ++ tailWord_386496) baseStart_386496 baseEnd_386496 := by
    simpa [prefixWord, tailWord_386496, baseEnd_386496] using wordTrace_append hprefix tailTrace_386496
  have hstable : (prefixWord ++ tailWord_386496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386496).length < 2 ^ (prefixWord ++ tailWord_386496).sum := by decide
  have hdescent : baseEnd_386496 < baseStart_386496 := by decide
  rcases family_descends (prefixWord ++ tailWord_386496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386550 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_386550 : Nat := 118140960795 + 386550 * 2 ^ 59
def prefixEnd_386550 : Nat := 4983230072969 + 3 ^ 40 * 386550 * 2
def baseEnd_386550 : Nat := 198485946995567855047295

theorem tailTrace_386550 : CollatzResearch.WordTrace tailWord_386550 prefixEnd_386550 198485946995567855047295 := by
  unfold tailWord_386550
  simp only [CollatzResearch.WordTrace]
  refine ⟨881164796850177645574319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9399091166401894886126069 881164796850177645574319)
  ·
    refine ⟨1321747195275266468361479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 881164796850177645574319 1321747195275266468361479)
    ·
      refine ⟨1982620792912899702542219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1321747195275266468361479 1982620792912899702542219)
      ·
        refine ⟨2973931189369349553813329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982620792912899702542219 2973931189369349553813329)
        ·
          refine ⟨2230448392027012165359997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2973931189369349553813329 2230448392027012165359997)
          ·
            refine ⟨836418147010129562009999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2230448392027012165359997 836418147010129562009999)
            ·
              refine ⟨1254627220515194343014999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836418147010129562009999 1254627220515194343014999)
              ·
                refine ⟨1881940830772791514522499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254627220515194343014999 1881940830772791514522499)
                ·
                  refine ⟨2822911246159187271783749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881940830772791514522499 2822911246159187271783749)
                  ·
                    refine ⟨529295858654847613459453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2822911246159187271783749 529295858654847613459453)
                    ·
                      refine ⟨198485946995567855047295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 529295858654847613459453 198485946995567855047295)
                      ·
                        rfl

theorem cell23_386550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_386550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386550 prefixEnd_386550 := by exact prefixLift 386550
  have htrace : WordTrace (prefixWord ++ tailWord_386550) baseStart_386550 baseEnd_386550 := by
    simpa [prefixWord, tailWord_386550, baseEnd_386550] using wordTrace_append hprefix tailTrace_386550
  have hstable : (prefixWord ++ tailWord_386550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386550).length < 2 ^ (prefixWord ++ tailWord_386550).sum := by decide
  have hdescent : baseEnd_386550 < baseStart_386550 := by decide
  rcases family_descends (prefixWord ++ tailWord_386550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386557 : List Nat := [1, 4, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_386557 : Nat := 118140960795 + 386557 * 2 ^ 59
def prefixEnd_386557 : Nat := 4983230072969 + 3 ^ 40 * 386557 * 2
def baseEnd_386557 : Nat := 66163180453383109219921

theorem tailTrace_386557 : CollatzResearch.WordTrace tailWord_386557 prefixEnd_386557 66163180453383109219921 := by
  unfold tailWord_386557
  simp only [CollatzResearch.WordTrace]
  refine ⟨14098892060577482524693925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9399261373718321683129283 14098892060577482524693925)
  ·
    refine ⟨2643542261358277973380111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14098892060577482524693925 2643542261358277973380111)
    ·
      refine ⟨3965313392037416960070167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2643542261358277973380111 3965313392037416960070167)
      ·
        refine ⟨5947970088056125440105251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3965313392037416960070167 5947970088056125440105251)
        ·
          refine ⟨8921955132084188160157877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5947970088056125440105251 8921955132084188160157877)
          ·
            refine ⟨836433293632892640014801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8921955132084188160157877 836433293632892640014801)
            ·
              refine ⟨627324970224669480011101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836433293632892640014801 627324970224669480011101)
              ·
                refine ⟨235246863834251055004163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 627324970224669480011101 235246863834251055004163)
                ·
                  refine ⟨352870295751376582506245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235246863834251055004163 352870295751376582506245)
                  ·
                    refine ⟨66163180453383109219921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 352870295751376582506245 66163180453383109219921)
                    ·
                      rfl

theorem cell23_386557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_386557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386557 prefixEnd_386557 := by exact prefixLift 386557
  have htrace : WordTrace (prefixWord ++ tailWord_386557) baseStart_386557 baseEnd_386557 := by
    simpa [prefixWord, tailWord_386557, baseEnd_386557] using wordTrace_append hprefix tailTrace_386557
  have hstable : (prefixWord ++ tailWord_386557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386557).length < 2 ^ (prefixWord ++ tailWord_386557).sum := by decide
  have hdescent : baseEnd_386557 < baseStart_386557 := by decide
  rcases family_descends (prefixWord ++ tailWord_386557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386570 : List Nat := [3, 1, 2, 2, 2, 4, 1, 2, 6]
def baseStart_386570 : Nat := 118140960795 + 386570 * 2 ^ 59
def prefixEnd_386570 : Nat := 4983230072969 + 3 ^ 40 * 386570 * 2
def baseEnd_386570 : Nat := 22055135178739752977467

theorem tailTrace_386570 : CollatzResearch.WordTrace tailWord_386570 prefixEnd_386570 22055135178739752977467 := by
  unfold tailWord_386570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3524841552382596436229291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9399577473020257163278109 3524841552382596436229291)
  ·
    refine ⟨5287262328573894654343937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3524841552382596436229291 5287262328573894654343937)
    ·
      refine ⟨3965446746430420990757953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5287262328573894654343937 3965446746430420990757953)
      ·
        refine ⟨2974085059822815743068465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3965446746430420990757953 2974085059822815743068465)
        ·
          refine ⟨2230563794867111807301349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2974085059822815743068465 2230563794867111807301349)
          ·
            refine ⟨418230711537583463869003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2230563794867111807301349 418230711537583463869003)
            ·
              refine ⟨627346067306375195803505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418230711537583463869003 627346067306375195803505)
              ·
                refine ⟨470509550479781396852629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627346067306375195803505 470509550479781396852629)
                ·
                  refine ⟨22055135178739752977467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 470509550479781396852629 22055135178739752977467)
                  ·
                    rfl

theorem cell23_386570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_386570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386570 prefixEnd_386570 := by exact prefixLift 386570
  have htrace : WordTrace (prefixWord ++ tailWord_386570) baseStart_386570 baseEnd_386570 := by
    simpa [prefixWord, tailWord_386570, baseEnd_386570] using wordTrace_append hprefix tailTrace_386570
  have hstable : (prefixWord ++ tailWord_386570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386570).length < 2 ^ (prefixWord ++ tailWord_386570).sum := by decide
  have hdescent : baseEnd_386570 < baseStart_386570 := by decide
  rcases family_descends (prefixWord ++ tailWord_386570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386623 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 5]
def baseStart_386623 : Nat := 118140960795 + 386623 * 2 ^ 59
def prefixEnd_386623 : Nat := 4983230072969 + 3 ^ 40 * 386623 * 2
def baseEnd_386623 : Nat := 198523431083346069434459

theorem tailTrace_386623 : CollatzResearch.WordTrace tailWord_386623 prefixEnd_386623 198523431083346069434459 := by
  unfold tailWord_386623
  simp only [CollatzResearch.WordTrace]
  refine ⟨14101299278338375796596523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9400866185558917197731015 14101299278338375796596523)
  ·
    refine ⟨21151948917507563694894785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14101299278338375796596523 21151948917507563694894785)
    ·
      refine ⟨15863961688130672771171089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21151948917507563694894785 15863961688130672771171089)
      ·
        refine ⟨11897971266098004578378317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15863961688130672771171089 11897971266098004578378317)
        ·
          refine ⟨4461739224786751716891869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11897971266098004578378317 4461739224786751716891869)
          ·
            refine ⟨1673152209295031893834451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4461739224786751716891869 1673152209295031893834451)
            ·
              refine ⟨2509728313942547840751677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673152209295031893834451 2509728313942547840751677)
              ·
                refine ⟨941148117728455440281879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2509728313942547840751677 941148117728455440281879)
                ·
                  refine ⟨1411722176592683160422819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941148117728455440281879 1411722176592683160422819)
                  ·
                    refine ⟨2117583264889024740634229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1411722176592683160422819 2117583264889024740634229)
                    ·
                      refine ⟨198523431083346069434459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2117583264889024740634229 198523431083346069434459)
                      ·
                        rfl

theorem cell23_386623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_386623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386623 prefixEnd_386623 := by exact prefixLift 386623
  have htrace : WordTrace (prefixWord ++ tailWord_386623) baseStart_386623 baseEnd_386623 := by
    simpa [prefixWord, tailWord_386623, baseEnd_386623] using wordTrace_append hprefix tailTrace_386623
  have hstable : (prefixWord ++ tailWord_386623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386623).length < 2 ^ (prefixWord ++ tailWord_386623).sum := by decide
  have hdescent : baseEnd_386623 < baseStart_386623 := by decide
  rcases family_descends (prefixWord ++ tailWord_386623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386631 : List Nat := [1, 1, 4, 1, 5, 1, 3, 2, 1, 1, 3]
def baseStart_386631 : Nat := 118140960795 + 386631 * 2 ^ 59
def prefixEnd_386631 : Nat := 4983230072969 + 3 ^ 40 * 386631 * 2
def baseEnd_386631 : Nat := 198527538928582038134423

theorem tailTrace_386631 : CollatzResearch.WordTrace tailWord_386631 prefixEnd_386631 198527538928582038134423 := by
  unfold tailWord_386631
  simp only [CollatzResearch.WordTrace]
  refine ⟨14101591062309393162887747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9401060708206262108591831 14101591062309393162887747)
  ·
    refine ⟨21152386593464089744331621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14101591062309393162887747 21152386593464089744331621)
    ·
      refine ⟨3966072486274516827062179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21152386593464089744331621 3966072486274516827062179)
      ·
        refine ⟨5949108729411775240593269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3966072486274516827062179 5949108729411775240593269)
        ·
          refine ⟨557728943382353928805619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5949108729411775240593269 557728943382353928805619)
          ·
            refine ⟨836593415073530893208429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557728943382353928805619 836593415073530893208429)
            ·
              refine ⟨313722530652574084953161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 836593415073530893208429 313722530652574084953161)
              ·
                refine ⟨235291897989430563714871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313722530652574084953161 235291897989430563714871)
                ·
                  refine ⟨352937846984145845572307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235291897989430563714871 352937846984145845572307)
                  ·
                    refine ⟨529406770476218768358461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 352937846984145845572307 529406770476218768358461)
                    ·
                      refine ⟨198527538928582038134423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 529406770476218768358461 198527538928582038134423)
                      ·
                        rfl

theorem cell23_386631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_386631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386631 prefixEnd_386631 := by exact prefixLift 386631
  have htrace : WordTrace (prefixWord ++ tailWord_386631) baseStart_386631 baseEnd_386631 := by
    simpa [prefixWord, tailWord_386631, baseEnd_386631] using wordTrace_append hprefix tailTrace_386631
  have hstable : (prefixWord ++ tailWord_386631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386631).length < 2 ^ (prefixWord ++ tailWord_386631).sum := by decide
  have hdescent : baseEnd_386631 < baseStart_386631 := by decide
  rcases family_descends (prefixWord ++ tailWord_386631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386647 : List Nat := [1, 1, 3, 2, 2, 3, 4, 1, 2, 4]
def baseStart_386647 : Nat := 118140960795 + 386647 * 2 ^ 59
def prefixEnd_386647 : Nat := 4983230072969 + 3 ^ 40 * 386647 * 2
def baseEnd_386647 : Nat := 66178584873017991844783

theorem tailTrace_386647 : CollatzResearch.WordTrace tailWord_386647 prefixEnd_386647 66178584873017991844783 := by
  unfold tailWord_386647
  simp only [CollatzResearch.WordTrace]
  refine ⟨14102174630251427895470195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9401449753500951930313463 14102174630251427895470195)
  ·
    refine ⟨21153261945377141843205293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14102174630251427895470195 21153261945377141843205293)
    ·
      refine ⟨7932473229516428191201985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21153261945377141843205293 7932473229516428191201985)
      ·
        refine ⟨5949354922137321143401489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7932473229516428191201985 5949354922137321143401489)
        ·
          refine ⟨4462016191602990857551117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5949354922137321143401489 4462016191602990857551117)
          ·
            refine ⟨1673256071851121571581669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4462016191602990857551117 1673256071851121571581669)
            ·
              refine ⟨313735513472085294671563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1673256071851121571581669 313735513472085294671563)
              ·
                refine ⟨470603270208127942007345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313735513472085294671563 470603270208127942007345)
                ·
                  refine ⟨352952452656095956505509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470603270208127942007345 352952452656095956505509)
                  ·
                    refine ⟨66178584873017991844783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 352952452656095956505509 66178584873017991844783)
                    ·
                      rfl

theorem cell23_386647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_386647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386647 prefixEnd_386647 := by exact prefixLift 386647
  have htrace : WordTrace (prefixWord ++ tailWord_386647) baseStart_386647 baseEnd_386647 := by
    simpa [prefixWord, tailWord_386647, baseEnd_386647] using wordTrace_append hprefix tailTrace_386647
  have hstable : (prefixWord ++ tailWord_386647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386647).length < 2 ^ (prefixWord ++ tailWord_386647).sum := by decide
  have hdescent : baseEnd_386647 < baseStart_386647 := by decide
  rcases family_descends (prefixWord ++ tailWord_386647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386674 : List Nat := [3, 2, 1, 2, 3, 2, 3, 1, 1, 2, 3]
def baseStart_386674 : Nat := 118140960795 + 386674 * 2 ^ 59
def prefixEnd_386674 : Nat := 4983230072969 + 3 ^ 40 * 386674 * 2
def baseEnd_386674 : Nat := 198549618596725369896725

theorem tailTrace_386674 : CollatzResearch.WordTrace tailWord_386674 prefixEnd_386674 198549618596725369896725 := by
  unfold tailWord_386674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3525789850288402876675769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9402106267435741004468717 3525789850288402876675769)
  ·
    refine ⟨2644342387716302157506827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3525789850288402876675769 2644342387716302157506827)
    ·
      refine ⟨3966513581574453236260241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2644342387716302157506827 3966513581574453236260241)
      ·
        refine ⟨2974885186180839927195181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3966513581574453236260241 2974885186180839927195181)
        ·
          refine ⟨1115581944817814972698193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2974885186180839927195181 1115581944817814972698193)
          ·
            refine ⟨836686458613361229523645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1115581944817814972698193 836686458613361229523645)
            ·
              refine ⟨313757421980010461071367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 836686458613361229523645 313757421980010461071367)
              ·
                refine ⟨470636132970015691607051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313757421980010461071367 470636132970015691607051)
                ·
                  refine ⟨705954199455023537410577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470636132970015691607051 705954199455023537410577)
                  ·
                    refine ⟨529465649591267653057933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 705954199455023537410577 529465649591267653057933)
                    ·
                      refine ⟨198549618596725369896725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 529465649591267653057933 198549618596725369896725)
                      ·
                        rfl

theorem cell23_386674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_386674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386674 prefixEnd_386674 := by exact prefixLift 386674
  have htrace : WordTrace (prefixWord ++ tailWord_386674) baseStart_386674 baseEnd_386674 := by
    simpa [prefixWord, tailWord_386674, baseEnd_386674] using wordTrace_append hprefix tailTrace_386674
  have hstable : (prefixWord ++ tailWord_386674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386674).length < 2 ^ (prefixWord ++ tailWord_386674).sum := by decide
  have hdescent : baseEnd_386674 < baseStart_386674 := by decide
  rcases family_descends (prefixWord ++ tailWord_386674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386680 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 7, 3, 2]
def baseStart_386680 : Nat := 118140960795 + 386680 * 2 ^ 59
def prefixEnd_386680 : Nat := 4983230072969 + 3 ^ 40 * 386680 * 2
def baseEnd_386680 : Nat := 198552699480652346421697

theorem tailTrace_386680 : CollatzResearch.WordTrace tailWord_386680 prefixEnd_386680 198552699480652346421697 := by
  unfold tailWord_386680
  simp only [CollatzResearch.WordTrace]
  refine ⟨7051689119565937265710747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9402252159421249687614329 7051689119565937265710747)
  ·
    refine ⟨10577533679348905898566121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7051689119565937265710747 10577533679348905898566121)
    ·
      refine ⟨7933150259511679423924591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10577533679348905898566121 7933150259511679423924591)
      ·
        refine ⟨11899725389267519135886887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7933150259511679423924591 11899725389267519135886887)
        ·
          refine ⟨17849588083901278703830331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11899725389267519135886887 17849588083901278703830331)
          ·
            refine ⟨26774382125851918055745497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17849588083901278703830331 26774382125851918055745497)
            ·
              refine ⟨20080786594388938541809123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26774382125851918055745497 20080786594388938541809123)
              ·
                refine ⟨30121179891583407812713685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20080786594388938541809123 30121179891583407812713685)
                ·
                  refine ⟨705965153708986120610477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 30121179891583407812713685 705965153708986120610477)
                  ·
                    refine ⟨264736932640869795228929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 705965153708986120610477 264736932640869795228929)
                    ·
                      refine ⟨198552699480652346421697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 264736932640869795228929 198552699480652346421697)
                      ·
                        rfl

theorem cell23_386680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7, 3, 2].length) (baseStart_386680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386680 prefixEnd_386680 := by exact prefixLift 386680
  have htrace : WordTrace (prefixWord ++ tailWord_386680) baseStart_386680 baseEnd_386680 := by
    simpa [prefixWord, tailWord_386680, baseEnd_386680] using wordTrace_append hprefix tailTrace_386680
  have hstable : (prefixWord ++ tailWord_386680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386680).length < 2 ^ (prefixWord ++ tailWord_386680).sum := by decide
  have hdescent : baseEnd_386680 < baseStart_386680 := by decide
  rcases family_descends (prefixWord ++ tailWord_386680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386693 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_386693 : Nat := 118140960795 + 386693 * 2 ^ 59
def prefixEnd_386693 : Nat := 4983230072969 + 3 ^ 40 * 386693 * 2
def baseEnd_386693 : Nat := 198559374729160795559137

theorem tailTrace_386693 : CollatzResearch.WordTrace tailWord_386693 prefixEnd_386693 198559374729160795559137 := by
  unfold tailWord_386693
  simp only [CollatzResearch.WordTrace]
  refine ⟨14103852388084777751644733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9402568258723185167763155 14103852388084777751644733)
  ·
    refine ⟨5288944645531791656866775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14103852388084777751644733 5288944645531791656866775)
    ·
      refine ⟨7933416968297687485300163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5288944645531791656866775 7933416968297687485300163)
      ·
        refine ⟨11900125452446531227950245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7933416968297687485300163 11900125452446531227950245)
        ·
          refine ⟨2231273522333724605240671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11900125452446531227950245 2231273522333724605240671)
          ·
            refine ⟨3346910283500586907861007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2231273522333724605240671 3346910283500586907861007)
            ·
              refine ⟨5020365425250880361791511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3346910283500586907861007 5020365425250880361791511)
              ·
                refine ⟨7530548137876320542687267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5020365425250880361791511 7530548137876320542687267)
                ·
                  refine ⟨11295822206814480814030901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7530548137876320542687267 11295822206814480814030901)
                  ·
                    refine ⟨1058983331888857576315397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11295822206814480814030901 1058983331888857576315397)
                    ·
                      refine ⟨198559374729160795559137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1058983331888857576315397 198559374729160795559137)
                      ·
                        rfl

theorem cell23_386693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_386693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386693 prefixEnd_386693 := by exact prefixLift 386693
  have htrace : WordTrace (prefixWord ++ tailWord_386693) baseStart_386693 baseEnd_386693 := by
    simpa [prefixWord, tailWord_386693, baseEnd_386693] using wordTrace_append hprefix tailTrace_386693
  have hstable : (prefixWord ++ tailWord_386693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386693).length < 2 ^ (prefixWord ++ tailWord_386693).sum := by decide
  have hdescent : baseEnd_386693 < baseStart_386693 := by decide
  rcases family_descends (prefixWord ++ tailWord_386693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386713 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 5]
def baseStart_386713 : Nat := 118140960795 + 386713 * 2 ^ 59
def prefixEnd_386713 : Nat := 4983230072969 + 3 ^ 40 * 386713 * 2
def baseEnd_386713 : Nat := 198569644342250717309045

theorem tailTrace_386713 : CollatzResearch.WordTrace tailWord_386713 prefixEnd_386713 198569644342250717309045 := by
  unfold tailWord_386713
  simp only [CollatzResearch.WordTrace]
  refine ⟨14104581848012321167372793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9403054565341547444915195 14104581848012321167372793)
  ·
    refine ⟨10578436386009240875529595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14104581848012321167372793 10578436386009240875529595)
    ·
      refine ⟨15867654579013861313294393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10578436386009240875529595 15867654579013861313294393)
      ·
        refine ⟨11900740934260395984970795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15867654579013861313294393 11900740934260395984970795)
        ·
          refine ⟨17851111401390593977456193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11900740934260395984970795 17851111401390593977456193)
          ·
            refine ⟨13388333551042945483092145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17851111401390593977456193 13388333551042945483092145)
            ·
              refine ⟨10041250163282209112319109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13388333551042945483092145 10041250163282209112319109)
              ·
                refine ⟨1882734405615414208559833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10041250163282209112319109 1882734405615414208559833)
                ·
                  refine ⟨1412050804211560656419875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1882734405615414208559833 1412050804211560656419875)
                  ·
                    refine ⟨2118076206317340984629813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1412050804211560656419875 2118076206317340984629813)
                    ·
                      refine ⟨198569644342250717309045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2118076206317340984629813 198569644342250717309045)
                      ·
                        rfl

theorem cell23_386713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_386713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386713 prefixEnd_386713 := by exact prefixLift 386713
  have htrace : WordTrace (prefixWord ++ tailWord_386713) baseStart_386713 baseEnd_386713 := by
    simpa [prefixWord, tailWord_386713, baseEnd_386713] using wordTrace_append hprefix tailTrace_386713
  have hstable : (prefixWord ++ tailWord_386713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386713).length < 2 ^ (prefixWord ++ tailWord_386713).sum := by decide
  have hdescent : baseEnd_386713 < baseStart_386713 := by decide
  rcases family_descends (prefixWord ++ tailWord_386713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386723 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 4]
def baseStart_386723 : Nat := 118140960795 + 386723 * 2 ^ 59
def prefixEnd_386723 : Nat := 4983230072969 + 3 ^ 40 * 386723 * 2
def baseEnd_386723 : Nat := 198574779148795678183999

theorem tailTrace_386723 : CollatzResearch.WordTrace tailWord_386723 prefixEnd_386723 198574779148795678183999 := by
  unfold tailWord_386723
  simp only [CollatzResearch.WordTrace]
  refine ⟨14104946577976092875236823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9403297718650728583491215 14104946577976092875236823)
  ·
    refine ⟨21157419866964139312855235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14104946577976092875236823 21157419866964139312855235)
    ·
      refine ⟨31736129800446208969282853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21157419866964139312855235 31736129800446208969282853)
      ·
        refine ⟨5950524337583664181740535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31736129800446208969282853 5950524337583664181740535)
        ·
          refine ⟨8925786506375496272610803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5950524337583664181740535 8925786506375496272610803)
          ·
            refine ⟨13388679759563244408916205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8925786506375496272610803 13388679759563244408916205)
            ·
              refine ⟨5020754909836216653343577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13388679759563244408916205 5020754909836216653343577)
              ·
                refine ⟨3765566182377162490007683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5020754909836216653343577 3765566182377162490007683)
                ·
                  refine ⟨5648349273565743735011525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765566182377162490007683 5648349273565743735011525)
                  ·
                    refine ⟨1059065488793576950314661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5648349273565743735011525 1059065488793576950314661)
                    ·
                      refine ⟨198574779148795678183999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1059065488793576950314661 198574779148795678183999)
                      ·
                        rfl

theorem cell23_386723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_386723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386723 prefixEnd_386723 := by exact prefixLift 386723
  have htrace : WordTrace (prefixWord ++ tailWord_386723) baseStart_386723 baseEnd_386723 := by
    simpa [prefixWord, tailWord_386723, baseEnd_386723] using wordTrace_append hprefix tailTrace_386723
  have hstable : (prefixWord ++ tailWord_386723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386723).length < 2 ^ (prefixWord ++ tailWord_386723).sum := by decide
  have hdescent : baseEnd_386723 < baseStart_386723 := by decide
  rcases family_descends (prefixWord ++ tailWord_386723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386750 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 7]
def baseStart_386750 : Nat := 118140960795 + 386750 * 2 ^ 59
def prefixEnd_386750 : Nat := 4983230072969 + 3 ^ 40 * 386750 * 2
def baseEnd_386750 : Nat := 22065404791829674727375

theorem tailTrace_386750 : CollatzResearch.WordTrace tailWord_386750 prefixEnd_386750 22065404791829674727375 := by
  unfold tailWord_386750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1763241418609784560808713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9403954232585517657646469 1763241418609784560808713)
  ·
    refine ⟨1322431063957338420606535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1763241418609784560808713 1322431063957338420606535)
    ·
      refine ⟨1983646595936007630909803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1322431063957338420606535 1983646595936007630909803)
      ·
        refine ⟨2975469893904011446364705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983646595936007630909803 2975469893904011446364705)
        ·
          refine ⟨2231602420428008584773529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2975469893904011446364705 2231602420428008584773529)
          ·
            refine ⟨1673701815321006438580147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2231602420428008584773529 1673701815321006438580147)
            ·
              refine ⟨2510552722981509657870221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673701815321006438580147 2510552722981509657870221)
              ·
                refine ⟨941457271118066121701333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2510552722981509657870221 941457271118066121701333)
                ·
                  refine ⟨22065404791829674727375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 941457271118066121701333 22065404791829674727375)
                  ·
                    rfl

theorem cell23_386750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_386750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386750 prefixEnd_386750 := by exact prefixLift 386750
  have htrace : WordTrace (prefixWord ++ tailWord_386750) baseStart_386750 baseEnd_386750 := by
    simpa [prefixWord, tailWord_386750, baseEnd_386750] using wordTrace_append hprefix tailTrace_386750
  have hstable : (prefixWord ++ tailWord_386750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386750).length < 2 ^ (prefixWord ++ tailWord_386750).sum := by decide
  have hdescent : baseEnd_386750 < baseStart_386750 := by decide
  rcases family_descends (prefixWord ++ tailWord_386750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386760 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_386760 : Nat := 118140960795 + 386760 * 2 ^ 59
def prefixEnd_386760 : Nat := 4983230072969 + 3 ^ 40 * 386760 * 2
def baseEnd_386760 : Nat := 198593777933012033421329

theorem tailTrace_386760 : CollatzResearch.WordTrace tailWord_386760 prefixEnd_386760 198593777933012033421329 := by
  unfold tailWord_386760
  simp only [CollatzResearch.WordTrace]
  refine ⟨7053148039421024097166867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9404197385894698796222489 7053148039421024097166867)
  ·
    refine ⟨10579722059131536145750301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7053148039421024097166867 10579722059131536145750301)
    ·
      refine ⟨3967395772174326054656363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10579722059131536145750301 3967395772174326054656363)
      ·
        refine ⟨5951093658261489081984545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3967395772174326054656363 5951093658261489081984545)
        ·
          refine ⟨4463320243696116811488409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5951093658261489081984545 4463320243696116811488409)
          ·
            refine ⟨3347490182772087608616307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4463320243696116811488409 3347490182772087608616307)
            ·
              refine ⟨5021235274158131412924461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3347490182772087608616307 5021235274158131412924461)
              ·
                refine ⟨1882963227809299279846673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5021235274158131412924461 1882963227809299279846673)
                ·
                  refine ⟨1412222420856974459885005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1882963227809299279846673 1412222420856974459885005)
                  ·
                    refine ⟨529583407821365422456877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1412222420856974459885005 529583407821365422456877)
                    ·
                      refine ⟨198593777933012033421329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 529583407821365422456877 198593777933012033421329)
                      ·
                        rfl

theorem cell23_386760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_386760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386760 prefixEnd_386760 := by exact prefixLift 386760
  have htrace : WordTrace (prefixWord ++ tailWord_386760) baseStart_386760 baseEnd_386760 := by
    simpa [prefixWord, tailWord_386760, baseEnd_386760] using wordTrace_append hprefix tailTrace_386760
  have hstable : (prefixWord ++ tailWord_386760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386760).length < 2 ^ (prefixWord ++ tailWord_386760).sum := by decide
  have hdescent : baseEnd_386760 < baseStart_386760 := by decide
  rcases family_descends (prefixWord ++ tailWord_386760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386797 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_386797 : Nat := 118140960795 + 386797 * 2 ^ 59
def prefixEnd_386797 : Nat := 4983230072969 + 3 ^ 40 * 386797 * 2
def baseEnd_386797 : Nat := 66204258905742796219553

theorem tailTrace_386797 : CollatzResearch.WordTrace tailWord_386797 prefixEnd_386797 66204258905742796219553 := by
  unfold tailWord_386797
  simp only [CollatzResearch.WordTrace]
  refine ⟨14107645579708003513430645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9405097053138669008953763 14107645579708003513430645)
  ·
    refine ⟨1322591773097625329384123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14107645579708003513430645 1322591773097625329384123)
    ·
      refine ⟨1983887659646437994076185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1322591773097625329384123 1983887659646437994076185)
      ·
        refine ⟨1487915744734828495557139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1983887659646437994076185 1487915744734828495557139)
        ·
          refine ⟨2231873617102242743335709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487915744734828495557139 2231873617102242743335709)
          ·
            refine ⟨836952606413341028750891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2231873617102242743335709 836952606413341028750891)
            ·
              refine ⟨1255428909620011543126337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836952606413341028750891 1255428909620011543126337)
              ·
                refine ⟨941571682215008657344753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255428909620011543126337 941571682215008657344753)
                ·
                  refine ⟨706178761661256493008565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 941571682215008657344753 706178761661256493008565)
                  ·
                    refine ⟨66204258905742796219553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 706178761661256493008565 66204258905742796219553)
                    ·
                      rfl

theorem cell23_386797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_386797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386797 prefixEnd_386797 := by exact prefixLift 386797
  have htrace : WordTrace (prefixWord ++ tailWord_386797) baseStart_386797 baseEnd_386797 := by
    simpa [prefixWord, tailWord_386797, baseEnd_386797] using wordTrace_append hprefix tailTrace_386797
  have hstable : (prefixWord ++ tailWord_386797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386797).length < 2 ^ (prefixWord ++ tailWord_386797).sum := by decide
  have hdescent : baseEnd_386797 < baseStart_386797 := by decide
  rcases family_descends (prefixWord ++ tailWord_386797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386817 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_386817 : Nat := 118140960795 + 386817 * 2 ^ 59
def prefixEnd_386817 : Nat := 4983230072969 + 3 ^ 40 * 386817 * 2
def baseEnd_386817 : Nat := 198623046330318310408567

theorem tailTrace_386817 : CollatzResearch.WordTrace tailWord_386817 prefixEnd_386817 198623046330318310408567 := by
  unfold tailWord_386817
  simp only [CollatzResearch.WordTrace]
  refine ⟨14108375039635546929158705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9405583359757031286105803 14108375039635546929158705)
  ·
    refine ⟨10581281279726660196869029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14108375039635546929158705 10581281279726660196869029)
    ·
      refine ⟨1983990239948748786912943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10581281279726660196869029 1983990239948748786912943)
      ·
        refine ⟨2975985359923123180369415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983990239948748786912943 2975985359923123180369415)
        ·
          refine ⟨4463978039884684770554123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2975985359923123180369415 4463978039884684770554123)
          ·
            refine ⟨6695967059827027155831185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4463978039884684770554123 6695967059827027155831185)
            ·
              refine ⟨5021975294870270366873389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6695967059827027155831185 5021975294870270366873389)
              ·
                refine ⟨1883240735576351387577521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5021975294870270366873389 1883240735576351387577521)
                ·
                  refine ⟨1412430551682263540683141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1883240735576351387577521 1412430551682263540683141)
                  ·
                    refine ⟨264830728440424413878089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1412430551682263540683141 264830728440424413878089)
                    ·
                      refine ⟨198623046330318310408567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 264830728440424413878089 198623046330318310408567)
                      ·
                        rfl

theorem cell23_386817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_386817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386817 prefixEnd_386817 := by exact prefixLift 386817
  have htrace : WordTrace (prefixWord ++ tailWord_386817) baseStart_386817 baseEnd_386817 := by
    simpa [prefixWord, tailWord_386817, baseEnd_386817] using wordTrace_append hprefix tailTrace_386817
  have hstable : (prefixWord ++ tailWord_386817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386817).length < 2 ^ (prefixWord ++ tailWord_386817).sum := by decide
  have hdescent : baseEnd_386817 < baseStart_386817 := by decide
  rcases family_descends (prefixWord ++ tailWord_386817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386830 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_386830 : Nat := 118140960795 + 386830 * 2 ^ 59
def prefixEnd_386830 : Nat := 4983230072969 + 3 ^ 40 * 386830 * 2
def baseEnd_386830 : Nat := 198629721578826759546007

theorem tailTrace_386830 : CollatzResearch.WordTrace tailWord_386830 prefixEnd_386830 198629721578826759546007 := by
  unfold tailWord_386830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1763606148573556268672743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9405899459058966766254629 1763606148573556268672743)
  ·
    refine ⟨2645409222860334403009115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1763606148573556268672743 2645409222860334403009115)
    ·
      refine ⟨3968113834290501604513673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2645409222860334403009115 3968113834290501604513673)
      ·
        refine ⟨2976085375717876203385255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3968113834290501604513673 2976085375717876203385255)
        ·
          refine ⟨4464128063576814305077883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2976085375717876203385255 4464128063576814305077883)
          ·
            refine ⟨6696192095365221457616825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4464128063576814305077883 6696192095365221457616825)
            ·
              refine ⟨5022144071523916093212619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6696192095365221457616825 5022144071523916093212619)
              ·
                refine ⟨7533216107285874139818929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5022144071523916093212619 7533216107285874139818929)
                ·
                  refine ⟨5649912080464405604864197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7533216107285874139818929 5649912080464405604864197)
                  ·
                    refine ⟨1059358515087076050912037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5649912080464405604864197 1059358515087076050912037)
                    ·
                      refine ⟨198629721578826759546007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1059358515087076050912037 198629721578826759546007)
                      ·
                        rfl

theorem cell23_386830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_386830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386830 prefixEnd_386830 := by exact prefixLift 386830
  have htrace : WordTrace (prefixWord ++ tailWord_386830) baseStart_386830 baseEnd_386830 := by
    simpa [prefixWord, tailWord_386830, baseEnd_386830] using wordTrace_append hprefix tailTrace_386830
  have hstable : (prefixWord ++ tailWord_386830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386830).length < 2 ^ (prefixWord ++ tailWord_386830).sum := by decide
  have hdescent : baseEnd_386830 < baseStart_386830 := by decide
  rcases family_descends (prefixWord ++ tailWord_386830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386834 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_386834 : Nat := 118140960795 + 386834 * 2 ^ 59
def prefixEnd_386834 : Nat := 4983230072969 + 3 ^ 40 * 386834 * 2
def baseEnd_386834 : Nat := 198631775501444743895989

theorem tailTrace_386834 : CollatzResearch.WordTrace tailWord_386834 prefixEnd_386834 198631775501444743895989 := by
  unfold tailWord_386834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3527248770143489708131889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9405996720382639221685037 3527248770143489708131889)
  ·
    refine ⟨2645436577607617281098917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3527248770143489708131889 2645436577607617281098917)
    ·
      refine ⟨496019358301428240206047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2645436577607617281098917 496019358301428240206047)
      ·
        refine ⟨744029037452142360309071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496019358301428240206047 744029037452142360309071)
        ·
          refine ⟨1116043556178213540463607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744029037452142360309071 1116043556178213540463607)
          ·
            refine ⟨1674065334267320310695411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116043556178213540463607 1674065334267320310695411)
            ·
              refine ⟨2511098001400980466043117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674065334267320310695411 2511098001400980466043117)
              ·
                refine ⟨941661750525367674766169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2511098001400980466043117 941661750525367674766169)
                ·
                  refine ⟨706246312894025756074627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 941661750525367674766169 706246312894025756074627)
                  ·
                    refine ⟨1059369469341038634111941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 706246312894025756074627 1059369469341038634111941)
                    ·
                      refine ⟨198631775501444743895989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1059369469341038634111941 198631775501444743895989)
                      ·
                        rfl

theorem cell23_386834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_386834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386834 prefixEnd_386834 := by exact prefixLift 386834
  have htrace : WordTrace (prefixWord ++ tailWord_386834) baseStart_386834 baseEnd_386834 := by
    simpa [prefixWord, tailWord_386834, baseEnd_386834] using wordTrace_append hprefix tailTrace_386834
  have hstable : (prefixWord ++ tailWord_386834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386834).length < 2 ^ (prefixWord ++ tailWord_386834).sum := by decide
  have hdescent : baseEnd_386834 < baseStart_386834 := by decide
  rcases family_descends (prefixWord ++ tailWord_386834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386837 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_386837 : Nat := 118140960795 + 386837 * 2 ^ 59
def prefixEnd_386837 : Nat := 4983230072969 + 3 ^ 40 * 386837 * 2
def baseEnd_386837 : Nat := 198633315943408232158475

theorem tailTrace_386837 : CollatzResearch.WordTrace tailWord_386837 prefixEnd_386837 198633315943408232158475 := by
  unfold tailWord_386837
  simp only [CollatzResearch.WordTrace]
  refine ⟨14109104499563090344886765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9406069666375393563257843 14109104499563090344886765)
  ·
    refine ⟨5290914187336158879332537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14109104499563090344886765 5290914187336158879332537)
    ·
      refine ⟨3968185640502119159499403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5290914187336158879332537 3968185640502119159499403)
      ·
        refine ⟨5952278460753178739249105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3968185640502119159499403 5952278460753178739249105)
        ·
          refine ⟨4464208845564884054436829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5952278460753178739249105 4464208845564884054436829)
          ·
            refine ⟨1674078317086831520413811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4464208845564884054436829 1674078317086831520413811)
            ·
              refine ⟨2511117475630247280620717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674078317086831520413811 2511117475630247280620717)
              ·
                refine ⟨941669053361342730232769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2511117475630247280620717 941669053361342730232769)
                ·
                  refine ⟨706251790021007047674577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 941669053361342730232769 706251790021007047674577)
                  ·
                    refine ⟨529688842515755285755933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 706251790021007047674577 529688842515755285755933)
                    ·
                      refine ⟨198633315943408232158475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 529688842515755285755933 198633315943408232158475)
                      ·
                        rfl

theorem cell23_386837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_386837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386837 prefixEnd_386837 := by exact prefixLift 386837
  have htrace : WordTrace (prefixWord ++ tailWord_386837) baseStart_386837 baseEnd_386837 := by
    simpa [prefixWord, tailWord_386837, baseEnd_386837] using wordTrace_append hprefix tailTrace_386837
  have hstable : (prefixWord ++ tailWord_386837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386837).length < 2 ^ (prefixWord ++ tailWord_386837).sum := by decide
  have hdescent : baseEnd_386837 < baseStart_386837 := by decide
  rcases family_descends (prefixWord ++ tailWord_386837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386844 : List Nat := [2, 2, 3, 1, 1, 2, 2, 5, 1, 4]
def baseStart_386844 : Nat := 118140960795 + 386844 * 2 ^ 59
def prefixEnd_386844 : Nat := 4983230072969 + 3 ^ 40 * 386844 * 2
def baseEnd_386844 : Nat := 66212303435996568256981

theorem tailTrace_386844 : CollatzResearch.WordTrace tailWord_386844 prefixEnd_386844 66212303435996568256981 := by
  unfold tailWord_386844
  simp only [CollatzResearch.WordTrace]
  refine ⟨7054679905268865270195793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9406239873691820360261057 7054679905268865270195793)
  ·
    refine ⟨5291009928951648952646845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7054679905268865270195793 5291009928951648952646845)
    ·
      refine ⟨1984128723356868357242567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5291009928951648952646845 1984128723356868357242567)
      ·
        refine ⟨2976193085035302535863851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1984128723356868357242567 2976193085035302535863851)
        ·
          refine ⟨4464289627552953803795777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2976193085035302535863851 4464289627552953803795777)
          ·
            refine ⟨3348217220664715352846833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4464289627552953803795777 3348217220664715352846833)
            ·
              refine ⟨2511162915498536514635125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3348217220664715352846833 2511162915498536514635125)
              ·
                refine ⟨235421523327987798247043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2511162915498536514635125 235421523327987798247043)
                ·
                  refine ⟨353132284991981697370565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235421523327987798247043 353132284991981697370565)
                  ·
                    refine ⟨66212303435996568256981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 353132284991981697370565 66212303435996568256981)
                    ·
                      rfl

theorem cell23_386844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_386844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386844 prefixEnd_386844 := by exact prefixLift 386844
  have htrace : WordTrace (prefixWord ++ tailWord_386844) baseStart_386844 baseEnd_386844 := by
    simpa [prefixWord, tailWord_386844, baseEnd_386844] using wordTrace_append hprefix tailTrace_386844
  have hstable : (prefixWord ++ tailWord_386844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386844).length < 2 ^ (prefixWord ++ tailWord_386844).sum := by decide
  have hdescent : baseEnd_386844 < baseStart_386844 := by decide
  rcases family_descends (prefixWord ++ tailWord_386844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386901 : List Nat := [1, 3, 2, 2, 2, 2, 1, 5, 1, 1, 3]
def baseStart_386901 : Nat := 118140960795 + 386901 * 2 ^ 59
def prefixEnd_386901 : Nat := 4983230072969 + 3 ^ 40 * 386901 * 2
def baseEnd_386901 : Nat := 198666178705295981758181

theorem tailTrace_386901 : CollatzResearch.WordTrace tailWord_386901 prefixEnd_386901 198666178705295981758181 := by
  unfold tailWord_386901
  simp only [CollatzResearch.WordTrace]
  refine ⟨14111438771331229275216557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9407625847554152850144371 14111438771331229275216557)
  ·
    refine ⟨5291789539249210978206209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14111438771331229275216557 5291789539249210978206209)
    ·
      refine ⟨3968842154436908233654657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5291789539249210978206209 3968842154436908233654657)
      ·
        refine ⟨2976631615827681175240993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3968842154436908233654657 2976631615827681175240993)
        ·
          refine ⟨2232473711870760881430745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2976631615827681175240993 2232473711870760881430745)
          ·
            refine ⟨1674355283903070661073059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2232473711870760881430745 1674355283903070661073059)
            ·
              refine ⟨2511532925854605991609589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674355283903070661073059 2511532925854605991609589)
              ·
                refine ⟨235456211798869311713399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2511532925854605991609589 235456211798869311713399)
                ·
                  refine ⟨353184317698303967570099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235456211798869311713399 353184317698303967570099)
                  ·
                    refine ⟨529776476547455951355149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 353184317698303967570099 529776476547455951355149)
                    ·
                      refine ⟨198666178705295981758181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 529776476547455951355149 198666178705295981758181)
                      ·
                        rfl

theorem cell23_386901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_386901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386901 prefixEnd_386901 := by exact prefixLift 386901
  have htrace : WordTrace (prefixWord ++ tailWord_386901) baseStart_386901 baseEnd_386901 := by
    simpa [prefixWord, tailWord_386901, baseEnd_386901] using wordTrace_append hprefix tailTrace_386901
  have hstable : (prefixWord ++ tailWord_386901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386901).length < 2 ^ (prefixWord ++ tailWord_386901).sum := by decide
  have hdescent : baseEnd_386901 < baseStart_386901 := by decide
  rcases family_descends (prefixWord ++ tailWord_386901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386930 : List Nat := [3, 2, 1, 2, 1, 1, 1, 12]
def baseStart_386930 : Nat := 118140960795 + 386930 * 2 ^ 59
def prefixEnd_386930 : Nat := 4983230072969 + 3 ^ 40 * 386930 * 2
def baseEnd_386930 : Nat := 7358558134973198825761

theorem tailTrace_386930 : CollatzResearch.WordTrace tailWord_386930 prefixEnd_386930 7358558134973198825761 := by
  unfold tailWord_386930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3528124122056541807005561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9408330992150778152014829 3528124122056541807005561)
  ·
    refine ⟨2646093091542406355254171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3528124122056541807005561 2646093091542406355254171)
    ·
      refine ⟨3969139637313609532881257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2646093091542406355254171 3969139637313609532881257)
      ·
        refine ⟨2976854727985207149660943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3969139637313609532881257 2976854727985207149660943)
        ·
          refine ⟨4465282091977810724491415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2976854727985207149660943 4465282091977810724491415)
          ·
            refine ⟨6697923137966716086737123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4465282091977810724491415 6697923137966716086737123)
            ·
              refine ⟨10046884706950074130105685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6697923137966716086737123 10046884706950074130105685)
              ·
                refine ⟨7358558134973198825761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 10046884706950074130105685 7358558134973198825761)
                ·
                  rfl

theorem cell23_386930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 12].length) (baseStart_386930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386930 prefixEnd_386930 := by exact prefixLift 386930
  have htrace : WordTrace (prefixWord ++ tailWord_386930) baseStart_386930 baseEnd_386930 := by
    simpa [prefixWord, tailWord_386930, baseEnd_386930] using wordTrace_append hprefix tailTrace_386930
  have hstable : (prefixWord ++ tailWord_386930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386930).length < 2 ^ (prefixWord ++ tailWord_386930).sum := by decide
  have hdescent : baseEnd_386930 < baseStart_386930 := by decide
  rcases family_descends (prefixWord ++ tailWord_386930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386944 : List Nat := [2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 3]
def baseStart_386944 : Nat := 118140960795 + 386944 * 2 ^ 59
def prefixEnd_386944 : Nat := 4983230072969 + 3 ^ 40 * 386944 * 2
def baseEnd_386944 : Nat := 198688258373439313520483

theorem tailTrace_386944 : CollatzResearch.WordTrace tailWord_386944 prefixEnd_386944 198688258373439313520483 := by
  unfold tailWord_386944
  simp only [CollatzResearch.WordTrace]
  refine ⟨7056503555087723809515943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9408671406783631746021257 7056503555087723809515943)
  ·
    refine ⟨10584755332631585714273915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7056503555087723809515943 10584755332631585714273915)
    ·
      refine ⟨15877132998947378571410873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10584755332631585714273915 15877132998947378571410873)
      ·
        refine ⟨11907849749210533928558155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15877132998947378571410873 11907849749210533928558155)
        ·
          refine ⟨17861774623815800892837233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11907849749210533928558155 17861774623815800892837233)
          ·
            refine ⟨13396330967861850669627925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17861774623815800892837233 13396330967861850669627925)
            ·
              refine ⟨627953014118524250138809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13396330967861850669627925 627953014118524250138809)
              ·
                refine ⟨470964760588893187604107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627953014118524250138809 470964760588893187604107)
                ·
                  refine ⟨706447140883339781406161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470964760588893187604107 706447140883339781406161)
                  ·
                    refine ⟨529835355662504836054621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 706447140883339781406161 529835355662504836054621)
                    ·
                      refine ⟨198688258373439313520483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 529835355662504836054621 198688258373439313520483)
                      ·
                        rfl

theorem cell23_386944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_386944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386944 prefixEnd_386944 := by exact prefixLift 386944
  have htrace : WordTrace (prefixWord ++ tailWord_386944) baseStart_386944 baseEnd_386944 := by
    simpa [prefixWord, tailWord_386944, baseEnd_386944] using wordTrace_append hprefix tailTrace_386944
  have hstable : (prefixWord ++ tailWord_386944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386944).length < 2 ^ (prefixWord ++ tailWord_386944).sum := by decide
  have hdescent : baseEnd_386944 < baseStart_386944 := by decide
  rcases family_descends (prefixWord ++ tailWord_386944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386947 : List Nat := [1, 1, 1, 3, 4, 2, 4, 7]
def baseStart_386947 : Nat := 118140960795 + 386947 * 2 ^ 59
def prefixEnd_386947 : Nat := 4983230072969 + 3 ^ 40 * 386947 * 2
def baseEnd_386947 : Nat := 7358881437607511177147

theorem tailTrace_386947 : CollatzResearch.WordTrace tailWord_386947 prefixEnd_386947 7358881437607511177147 := by
  unfold tailWord_386947
  simp only [CollatzResearch.WordTrace]
  refine ⟨14113116529164579131391095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9408744352776386087594063 14113116529164579131391095)
  ·
    refine ⟨21169674793746868697086643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14113116529164579131391095 21169674793746868697086643)
    ·
      refine ⟨31754512190620303045629965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21169674793746868697086643 31754512190620303045629965)
      ·
        refine ⟨11907942071482613642111237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31754512190620303045629965 11907942071482613642111237)
        ·
          refine ⟨2232739138402990057895857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11907942071482613642111237 2232739138402990057895857)
          ·
            refine ⟨1674554353802242543421893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2232739138402990057895857 1674554353802242543421893)
            ·
              refine ⟨313978941337920476891605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1674554353802242543421893 313978941337920476891605)
              ·
                refine ⟨7358881437607511177147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 313978941337920476891605 7358881437607511177147)
                ·
                  rfl

theorem cell23_386947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 7].length) (baseStart_386947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386947 prefixEnd_386947 := by exact prefixLift 386947
  have htrace : WordTrace (prefixWord ++ tailWord_386947) baseStart_386947 baseEnd_386947 := by
    simpa [prefixWord, tailWord_386947, baseEnd_386947] using wordTrace_append hprefix tailTrace_386947
  have hstable : (prefixWord ++ tailWord_386947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386947).length < 2 ^ (prefixWord ++ tailWord_386947).sum := by decide
  have hdescent : baseEnd_386947 < baseStart_386947 := by decide
  rcases family_descends (prefixWord ++ tailWord_386947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386975 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 3, 2, 2]
def baseStart_386975 : Nat := 118140960795 + 386975 * 2 ^ 59
def prefixEnd_386975 : Nat := 4983230072969 + 3 ^ 40 * 386975 * 2
def baseEnd_386975 : Nat := 198704176273728692232841

theorem tailTrace_386975 : CollatzResearch.WordTrace tailWord_386975 prefixEnd_386975 198704176273728692232841 := by
  unfold tailWord_386975
  simp only [CollatzResearch.WordTrace]
  refine ⟨14114137773063139913410379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9409425182042093275606919 14114137773063139913410379)
  ·
    refine ⟨21171206659594709870115569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14114137773063139913410379 21171206659594709870115569)
    ·
      refine ⟨15878404994696032402586677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21171206659594709870115569 15878404994696032402586677)
      ·
        refine ⟨1488600468252753037742501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15878404994696032402586677 1488600468252753037742501)
        ·
          refine ⟨279112587797391194576719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1488600468252753037742501 279112587797391194576719)
          ·
            refine ⟨418668881696086791865079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279112587797391194576719 418668881696086791865079)
            ·
              refine ⟨628003322544130187797619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418668881696086791865079 628003322544130187797619)
              ·
                refine ⟨942004983816195281696429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628003322544130187797619 942004983816195281696429)
                ·
                  refine ⟨353251868931073230636161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942004983816195281696429 353251868931073230636161)
                  ·
                    refine ⟨264938901698304922977121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 353251868931073230636161 264938901698304922977121)
                    ·
                      refine ⟨198704176273728692232841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 264938901698304922977121 198704176273728692232841)
                      ·
                        rfl

theorem cell23_386975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_386975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_386975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_386975 prefixEnd_386975 := by exact prefixLift 386975
  have htrace : WordTrace (prefixWord ++ tailWord_386975) baseStart_386975 baseEnd_386975 := by
    simpa [prefixWord, tailWord_386975, baseEnd_386975] using wordTrace_append hprefix tailTrace_386975
  have hstable : (prefixWord ++ tailWord_386975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386975).length < 2 ^ (prefixWord ++ tailWord_386975).sum := by decide
  have hdescent : baseEnd_386975 < baseStart_386975 := by decide
  rcases family_descends (prefixWord ++ tailWord_386975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387054 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 7]
def baseStart_387054 : Nat := 118140960795 + 387054 * 2 ^ 59
def prefixEnd_387054 : Nat := 4983230072969 + 3 ^ 40 * 387054 * 2
def baseEnd_387054 : Nat := 22082749027270431460553

theorem tailTrace_387054 : CollatzResearch.WordTrace tailWord_387054 prefixEnd_387054 22082749027270431460553 := by
  unfold tailWord_387054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764627392472117050692027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9411346093184624270357477 1764627392472117050692027)
  ·
    refine ⟨2646941088708175576038041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1764627392472117050692027 2646941088708175576038041)
    ·
      refine ⟨1985205816531131682028531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2646941088708175576038041 1985205816531131682028531)
      ·
        refine ⟨2977808724796697523042797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1985205816531131682028531 2977808724796697523042797)
        ·
          refine ⟨1116678271798761571141049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2977808724796697523042797 1116678271798761571141049)
          ·
            refine ⟨837508703849071178355787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1116678271798761571141049 837508703849071178355787)
            ·
              refine ⟨1256263055773606767533681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837508703849071178355787 1256263055773606767533681)
              ·
                refine ⟨942197291830205075650261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256263055773606767533681 942197291830205075650261)
                ·
                  refine ⟨22082749027270431460553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 942197291830205075650261 22082749027270431460553)
                  ·
                    rfl

theorem cell23_387054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_387054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387054 prefixEnd_387054 := by exact prefixLift 387054
  have htrace : WordTrace (prefixWord ++ tailWord_387054) baseStart_387054 baseEnd_387054 := by
    simpa [prefixWord, tailWord_387054, baseEnd_387054] using wordTrace_append hprefix tailTrace_387054
  have hstable : (prefixWord ++ tailWord_387054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387054).length < 2 ^ (prefixWord ++ tailWord_387054).sum := by decide
  have hdescent : baseEnd_387054 < baseStart_387054 := by decide
  rcases family_descends (prefixWord ++ tailWord_387054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387082 : List Nat := [3, 1, 2, 2, 5, 1, 1, 2, 2, 2, 2]
def baseStart_387082 : Nat := 118140960795 + 387082 * 2 ^ 59
def prefixEnd_387082 : Nat := 4983230072969 + 3 ^ 40 * 387082 * 2
def baseEnd_387082 : Nat := 198759118703759773594849

theorem tailTrace_387082 : CollatzResearch.WordTrace tailWord_387082 prefixEnd_387082 198759118703759773594849 := by
  unfold tailWord_387082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3529510095918874296888875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9412026922450331458370333 3529510095918874296888875)
  ·
    refine ⟨5294265143878311445333313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3529510095918874296888875 5294265143878311445333313)
    ·
      refine ⟨3970698857908733583999985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5294265143878311445333313 3970698857908733583999985)
      ·
        refine ⟨2978024143431550187999989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3970698857908733583999985 2978024143431550187999989)
        ·
          refine ⟨279189763446707830124999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2978024143431550187999989 279189763446707830124999)
          ·
            refine ⟨418784645170061745187499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279189763446707830124999 418784645170061745187499)
            ·
              refine ⟨628176967755092617781249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418784645170061745187499 628176967755092617781249)
              ·
                refine ⟨471132725816319463335937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628176967755092617781249 471132725816319463335937)
                ·
                  refine ⟨353349544362239597501953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471132725816319463335937 353349544362239597501953)
                  ·
                    refine ⟨265012158271679698126465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 353349544362239597501953 265012158271679698126465)
                    ·
                      refine ⟨198759118703759773594849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 265012158271679698126465 198759118703759773594849)
                      ·
                        rfl

theorem cell23_387082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_387082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387082 prefixEnd_387082 := by exact prefixLift 387082
  have htrace : WordTrace (prefixWord ++ tailWord_387082) baseStart_387082 baseEnd_387082 := by
    simpa [prefixWord, tailWord_387082, baseEnd_387082] using wordTrace_append hprefix tailTrace_387082
  have hstable : (prefixWord ++ tailWord_387082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387082).length < 2 ^ (prefixWord ++ tailWord_387082).sum := by decide
  have hdescent : baseEnd_387082 < baseStart_387082 := by decide
  rcases family_descends (prefixWord ++ tailWord_387082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387127 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 8]
def baseStart_387127 : Nat := 118140960795 + 387127 * 2 ^ 59
def prefixEnd_387127 : Nat := 4983230072969 + 3 ^ 40 * 387127 * 2
def baseEnd_387127 : Nat := 22086913925912455281349

theorem tailTrace_387127 : CollatzResearch.WordTrace tailWord_387127 prefixEnd_387127 22086913925912455281349 := by
  unfold tailWord_387127
  simp only [CollatzResearch.WordTrace]
  refine ⟨14119681668512469872943635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9413121112341646581962423 14119681668512469872943635)
  ·
    refine ⟨21179522502768704809415453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14119681668512469872943635 21179522502768704809415453)
    ·
      refine ⟨7942320938538264303530795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21179522502768704809415453 7942320938538264303530795)
      ·
        refine ⟨11913481407807396455296193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7942320938538264303530795 11913481407807396455296193)
        ·
          refine ⟨8935111055855547341472145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11913481407807396455296193 8935111055855547341472145)
          ·
            refine ⟨6701333291891660506104109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8935111055855547341472145 6701333291891660506104109)
            ·
              refine ⟨2512999984459372689789041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6701333291891660506104109 2512999984459372689789041)
              ·
                refine ⟨1884749988344529517341781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2512999984459372689789041 1884749988344529517341781)
                ·
                  refine ⟨22086913925912455281349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1884749988344529517341781 22086913925912455281349)
                  ·
                    rfl

theorem cell23_387127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 8].length) (baseStart_387127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387127 prefixEnd_387127 := by exact prefixLift 387127
  have htrace : WordTrace (prefixWord ++ tailWord_387127) baseStart_387127 baseEnd_387127 := by
    simpa [prefixWord, tailWord_387127, baseEnd_387127] using wordTrace_append hprefix tailTrace_387127
  have hstable : (prefixWord ++ tailWord_387127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387127).length < 2 ^ (prefixWord ++ tailWord_387127).sum := by decide
  have hdescent : baseEnd_387127 < baseStart_387127 := by decide
  rcases family_descends (prefixWord ++ tailWord_387127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387167 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 7]
def baseStart_387167 : Nat := 118140960795 + 387167 * 2 ^ 59
def prefixEnd_387167 : Nat := 4983230072969 + 3 ^ 40 * 387167 * 2
def baseEnd_387167 : Nat := 198802764559391941031957

theorem tailTrace_387167 : CollatzResearch.WordTrace tailWord_387167 prefixEnd_387167 198802764559391941031957 := by
  unfold tailWord_387167
  simp only [CollatzResearch.WordTrace]
  refine ⟨14121140588367556704399755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9414093725578371136266503 14121140588367556704399755)
  ·
    refine ⟨21181710882551335056599633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14121140588367556704399755 21181710882551335056599633)
    ·
      refine ⟨15886283161913501292449725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21181710882551335056599633 15886283161913501292449725)
      ·
        refine ⟨5957356185717562984668647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15886283161913501292449725 5957356185717562984668647)
        ·
          refine ⟨8936034278576344477002971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5957356185717562984668647 8936034278576344477002971)
          ·
            refine ⟨13404051417864516715504457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8936034278576344477002971 13404051417864516715504457)
            ·
              refine ⟨10053038563398387536628343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13404051417864516715504457 10053038563398387536628343)
              ·
                refine ⟨15079557845097581304942515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10053038563398387536628343 15079557845097581304942515)
                ·
                  refine ⟨22619336767646371957413773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15079557845097581304942515 22619336767646371957413773)
                  ·
                    refine ⟨8482251287867389484030165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22619336767646371957413773 8482251287867389484030165)
                    ·
                      refine ⟨198802764559391941031957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8482251287867389484030165 198802764559391941031957)
                      ·
                        rfl

theorem cell23_387167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_387167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387167 prefixEnd_387167 := by exact prefixLift 387167
  have htrace : WordTrace (prefixWord ++ tailWord_387167) baseStart_387167 baseEnd_387167 := by
    simpa [prefixWord, tailWord_387167, baseEnd_387167] using wordTrace_append hprefix tailTrace_387167
  have hstable : (prefixWord ++ tailWord_387167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387167).length < 2 ^ (prefixWord ++ tailWord_387167).sum := by decide
  have hdescent : baseEnd_387167 < baseStart_387167 := by decide
  rcases family_descends (prefixWord ++ tailWord_387167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387171 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 3, 1, 3]
def baseStart_387171 : Nat := 118140960795 + 387171 * 2 ^ 59
def prefixEnd_387171 : Nat := 4983230072969 + 3 ^ 40 * 387171 * 2
def baseEnd_387171 : Nat := 198804818482009925381939

theorem tailTrace_387171 : CollatzResearch.WordTrace tailWord_387171 prefixEnd_387171 198804818482009925381939 := by
  unfold tailWord_387171
  simp only [CollatzResearch.WordTrace]
  refine ⟨14121286480353065387545367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9414190986902043591696911 14121286480353065387545367)
  ·
    refine ⟨21181929720529598081318051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14121286480353065387545367 21181929720529598081318051)
    ·
      refine ⟨31772894580794397121977077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21181929720529598081318051 31772894580794397121977077)
      ·
        refine ⟨2978708866949474730185351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31772894580794397121977077 2978708866949474730185351)
        ·
          refine ⟨4468063300424212095278027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2978708866949474730185351 4468063300424212095278027)
          ·
            refine ⟨6702094950636318142917041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4468063300424212095278027 6702094950636318142917041)
            ·
              refine ⟨5026571212977238607187781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6702094950636318142917041 5026571212977238607187781)
              ·
                refine ⟨942482102433232238847709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5026571212977238607187781 942482102433232238847709)
                ·
                  refine ⟨353430788412462089567891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942482102433232238847709 353430788412462089567891)
                  ·
                    refine ⟨530146182618693134351837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 353430788412462089567891 530146182618693134351837)
                    ·
                      refine ⟨198804818482009925381939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 530146182618693134351837 198804818482009925381939)
                      ·
                        rfl

theorem cell23_387171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_387171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387171 prefixEnd_387171 := by exact prefixLift 387171
  have htrace : WordTrace (prefixWord ++ tailWord_387171) baseStart_387171 baseEnd_387171 := by
    simpa [prefixWord, tailWord_387171, baseEnd_387171] using wordTrace_append hprefix tailTrace_387171
  have hstable : (prefixWord ++ tailWord_387171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387171).length < 2 ^ (prefixWord ++ tailWord_387171).sum := by decide
  have hdescent : baseEnd_387171 < baseStart_387171 := by decide
  rcases family_descends (prefixWord ++ tailWord_387171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387204 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_387204 : Nat := 118140960795 + 387204 * 2 ^ 59
def prefixEnd_387204 : Nat := 4983230072969 + 3 ^ 40 * 387204 * 2
def baseEnd_387204 : Nat := 66273921114536098756429

theorem tailTrace_387204 : CollatzResearch.WordTrace tailWord_387204 prefixEnd_387204 66273921114536098756429 := by
  unfold tailWord_387204
  simp only [CollatzResearch.WordTrace]
  refine ⟨7061245044616756011748333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9414993392822341348997777 7061245044616756011748333)
  ·
    refine ⟨2647966891731283504405625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7061245044616756011748333 2647966891731283504405625)
    ·
      refine ⟨1985975168798462628304219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2647966891731283504405625 1985975168798462628304219)
      ·
        refine ⟨2978962753197693942456329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1985975168798462628304219 2978962753197693942456329)
        ·
          refine ⟨2234222064898270456842247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2978962753197693942456329 2234222064898270456842247)
          ·
            refine ⟨3351333097347405685263371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234222064898270456842247 3351333097347405685263371)
            ·
              refine ⟨5026999646021108527895057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351333097347405685263371 5026999646021108527895057)
              ·
                refine ⟨3770249734515831395921293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5026999646021108527895057 3770249734515831395921293)
                ·
                  refine ⟨1413843650443436773470485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3770249734515831395921293 1413843650443436773470485)
                  ·
                    refine ⟨66273921114536098756429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1413843650443436773470485 66273921114536098756429)
                    ·
                      rfl

theorem cell23_387204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_387204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387204 prefixEnd_387204 := by exact prefixLift 387204
  have htrace : WordTrace (prefixWord ++ tailWord_387204) baseStart_387204 baseEnd_387204 := by
    simpa [prefixWord, tailWord_387204, baseEnd_387204] using wordTrace_append hprefix tailTrace_387204
  have hstable : (prefixWord ++ tailWord_387204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387204).length < 2 ^ (prefixWord ++ tailWord_387204).sum := by decide
  have hdescent : baseEnd_387204 < baseStart_387204 := by decide
  rcases family_descends (prefixWord ++ tailWord_387204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387205 : List Nat := [1, 3, 1, 1, 5, 2, 1, 4, 1, 1, 3]
def baseStart_387205 : Nat := 118140960795 + 387205 * 2 ^ 59
def prefixEnd_387205 : Nat := 4983230072969 + 3 ^ 40 * 387205 * 2
def baseEnd_387205 : Nat := 198822276824262792356783

theorem tailTrace_387205 : CollatzResearch.WordTrace tailWord_387205 prefixEnd_387205 198822276824262792356783 := by
  unfold tailWord_387205
  simp only [CollatzResearch.WordTrace]
  refine ⟨14122526562229889194283069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9415017708153259462855379 14122526562229889194283069)
  ·
    refine ⟨5295947460836208447856151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14122526562229889194283069 5295947460836208447856151)
    ·
      refine ⟨7943921191254312671784227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5295947460836208447856151 7943921191254312671784227)
      ·
        refine ⟨11915881786881469007676341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7943921191254312671784227 11915881786881469007676341)
        ·
          refine ⟨1117113917520137719469657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11915881786881469007676341 1117113917520137719469657)
          ·
            refine ⟨837835438140103289602243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1117113917520137719469657 837835438140103289602243)
            ·
              refine ⟨1256753157210154934403365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837835438140103289602243 1256753157210154934403365)
              ·
                refine ⟨235641216976904050200631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1256753157210154934403365 235641216976904050200631)
                ·
                  refine ⟨353461825465356075300947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235641216976904050200631 353461825465356075300947)
                  ·
                    refine ⟨530192738198034112951421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 353461825465356075300947 530192738198034112951421)
                    ·
                      refine ⟨198822276824262792356783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 530192738198034112951421 198822276824262792356783)
                      ·
                        rfl

theorem cell23_387205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 1, 1, 3].length) (baseStart_387205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387205 prefixEnd_387205 := by exact prefixLift 387205
  have htrace : WordTrace (prefixWord ++ tailWord_387205) baseStart_387205 baseEnd_387205 := by
    simpa [prefixWord, tailWord_387205, baseEnd_387205] using wordTrace_append hprefix tailTrace_387205
  have hstable : (prefixWord ++ tailWord_387205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387205).length < 2 ^ (prefixWord ++ tailWord_387205).sum := by decide
  have hdescent : baseEnd_387205 < baseStart_387205 := by decide
  rcases family_descends (prefixWord ++ tailWord_387205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387221 : List Nat := [1, 3, 2, 1, 1, 1, 3, 5, 2, 4]
def baseStart_387221 : Nat := 118140960795 + 387221 * 2 ^ 59
def prefixEnd_387221 : Nat := 4983230072969 + 3 ^ 40 * 387221 * 2
def baseEnd_387221 : Nat := 66276830838244909918903

theorem tailTrace_387221 : CollatzResearch.WordTrace tailWord_387221 prefixEnd_387221 66276830838244909918903 := by
  unfold tailWord_387221
  simp only [CollatzResearch.WordTrace]
  refine ⟨14123110130171923926865517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9415406753447949284577011 14123110130171923926865517)
  ·
    refine ⟨5296166298814471472574569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14123110130171923926865517 5296166298814471472574569)
    ·
      refine ⟨3972124724110853604430927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5296166298814471472574569 3972124724110853604430927)
      ·
        refine ⟨5958187086166280406646391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972124724110853604430927 5958187086166280406646391)
        ·
          refine ⟨8937280629249420609969587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958187086166280406646391 8937280629249420609969587)
          ·
            refine ⟨13405920943874130914954381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937280629249420609969587 13405920943874130914954381)
            ·
              refine ⟨5027220353952799093107893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13405920943874130914954381 5027220353952799093107893)
              ·
                refine ⟨471301908183074914978865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5027220353952799093107893 471301908183074914978865)
                ·
                  refine ⟨353476431137306186234149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471301908183074914978865 353476431137306186234149)
                  ·
                    refine ⟨66276830838244909918903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 353476431137306186234149 66276830838244909918903)
                    ·
                      rfl

theorem cell23_387221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_387221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387221 prefixEnd_387221 := by exact prefixLift 387221
  have htrace : WordTrace (prefixWord ++ tailWord_387221) baseStart_387221 baseEnd_387221 := by
    simpa [prefixWord, tailWord_387221, baseEnd_387221] using wordTrace_append hprefix tailTrace_387221
  have hstable : (prefixWord ++ tailWord_387221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387221).length < 2 ^ (prefixWord ++ tailWord_387221).sum := by decide
  have hdescent : baseEnd_387221 < baseStart_387221 := by decide
  rcases family_descends (prefixWord ++ tailWord_387221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387242 : List Nat := [3, 1, 5, 1, 2, 2, 2, 1, 1, 5]
def baseStart_387242 : Nat := 118140960795 + 387242 * 2 ^ 59
def prefixEnd_387242 : Nat := 4983230072969 + 3 ^ 40 * 387242 * 2
def baseEnd_387242 : Nat := 66280425202826382531371

theorem tailTrace_387242 : CollatzResearch.WordTrace tailWord_387242 prefixEnd_387242 66280425202826382531371 := by
  unfold tailWord_387242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3530969015773961128344995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9415917375397229675586653 3530969015773961128344995)
  ·
    refine ⟨5296453523660941692517493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3530969015773961128344995 5296453523660941692517493)
    ·
      refine ⟨496542517843213283673515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5296453523660941692517493 496542517843213283673515)
      ·
        refine ⟨744813776764819925510273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496542517843213283673515 744813776764819925510273)
        ·
          refine ⟨558610332573614944132705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 744813776764819925510273 558610332573614944132705)
          ·
            refine ⟨418957749430211208099529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558610332573614944132705 418957749430211208099529)
            ·
              refine ⟨314218312072658406074647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418957749430211208099529 314218312072658406074647)
              ·
                refine ⟨471327468108987609111971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314218312072658406074647 471327468108987609111971)
                ·
                  refine ⟨706991202163481413667957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 471327468108987609111971 706991202163481413667957)
                  ·
                    refine ⟨66280425202826382531371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 706991202163481413667957 66280425202826382531371)
                    ·
                      rfl

theorem cell23_387242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_387242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387242 prefixEnd_387242 := by exact prefixLift 387242
  have htrace : WordTrace (prefixWord ++ tailWord_387242) baseStart_387242 baseEnd_387242 := by
    simpa [prefixWord, tailWord_387242, baseEnd_387242] using wordTrace_append hprefix tailTrace_387242
  have hstable : (prefixWord ++ tailWord_387242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387242).length < 2 ^ (prefixWord ++ tailWord_387242).sum := by decide
  have hdescent : baseEnd_387242 < baseStart_387242 := by decide
  rcases family_descends (prefixWord ++ tailWord_387242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387244 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 3]
def baseStart_387244 : Nat := 118140960795 + 387244 * 2 ^ 59
def prefixEnd_387244 : Nat := 4983230072969 + 3 ^ 40 * 387244 * 2
def baseEnd_387244 : Nat := 198842302569788139769103

theorem tailTrace_387244 : CollatzResearch.WordTrace tailWord_387244 prefixEnd_387244 198842302569788139769103 := by
  unfold tailWord_387244
  simp only [CollatzResearch.WordTrace]
  refine ⟨7061974504544299427476393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9415966006059065903301857 7061974504544299427476393)
  ·
    refine ⟨5296480878408224570607295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7061974504544299427476393 5296480878408224570607295)
    ·
      refine ⟨7944721317612336855910943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5296480878408224570607295 7944721317612336855910943)
      ·
        refine ⟨11917081976418505283866415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7944721317612336855910943 11917081976418505283866415)
        ·
          refine ⟨17875622964627757925799623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11917081976418505283866415 17875622964627757925799623)
          ·
            refine ⟨26813434446941636888699435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17875622964627757925799623 26813434446941636888699435)
            ·
              refine ⟨40220151670412455333049153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26813434446941636888699435 40220151670412455333049153)
              ·
                refine ⟨30165113752809341499786865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40220151670412455333049153 30165113752809341499786865)
                ·
                  refine ⟨22623835314607006124840149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30165113752809341499786865 22623835314607006124840149)
                  ·
                    refine ⟨530246140186101706050941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22623835314607006124840149 530246140186101706050941)
                    ·
                      refine ⟨198842302569788139769103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 530246140186101706050941 198842302569788139769103)
                      ·
                        rfl

theorem cell23_387244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_387244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387244 prefixEnd_387244 := by exact prefixLift 387244
  have htrace : WordTrace (prefixWord ++ tailWord_387244) baseStart_387244 baseEnd_387244 := by
    simpa [prefixWord, tailWord_387244, baseEnd_387244] using wordTrace_append hprefix tailTrace_387244
  have hstable : (prefixWord ++ tailWord_387244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387244).length < 2 ^ (prefixWord ++ tailWord_387244).sum := by decide
  have hdescent : baseEnd_387244 < baseStart_387244 := by decide
  rcases family_descends (prefixWord ++ tailWord_387244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387245 : List Nat := [1, 5, 2, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_387245 : Nat := 118140960795 + 387245 * 2 ^ 59
def prefixEnd_387245 : Nat := 4983230072969 + 3 ^ 40 * 387245 * 2
def baseEnd_387245 : Nat := 198842816050442635856599

theorem tailTrace_387245 : CollatzResearch.WordTrace tailWord_387245 prefixEnd_387245 198842816050442635856599 := by
  unfold tailWord_387245
  simp only [CollatzResearch.WordTrace]
  refine ⟨14123985482084976025739189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9415990321389984017159459 14123985482084976025739189)
  ·
    refine ⟨1324123638945466502413049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14123985482084976025739189 1324123638945466502413049)
    ·
      refine ⟨993092729209099876809787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1324123638945466502413049 993092729209099876809787)
      ·
        refine ⟨1489639093813649815214681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993092729209099876809787 1489639093813649815214681)
        ·
          refine ⟨1117229320360237361411011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1489639093813649815214681 1117229320360237361411011)
          ·
            refine ⟨1675843980540356042116517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117229320360237361411011 1675843980540356042116517)
            ·
              refine ⟨314220746351316757896847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1675843980540356042116517 314220746351316757896847)
              ·
                refine ⟨471331119526975136845271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314220746351316757896847 471331119526975136845271)
                ·
                  refine ⟨706996679290462705267907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 471331119526975136845271 706996679290462705267907)
                  ·
                    refine ⟨1060495018935694057901861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 706996679290462705267907 1060495018935694057901861)
                    ·
                      refine ⟨198842816050442635856599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1060495018935694057901861 198842816050442635856599)
                      ·
                        rfl

theorem cell23_387245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_387245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387245 prefixEnd_387245 := by exact prefixLift 387245
  have htrace : WordTrace (prefixWord ++ tailWord_387245) baseStart_387245 baseEnd_387245 := by
    simpa [prefixWord, tailWord_387245, baseEnd_387245] using wordTrace_append hprefix tailTrace_387245
  have hstable : (prefixWord ++ tailWord_387245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387245).length < 2 ^ (prefixWord ++ tailWord_387245).sum := by decide
  have hdescent : baseEnd_387245 < baseStart_387245 := by decide
  rcases family_descends (prefixWord ++ tailWord_387245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387262 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_387262 : Nat := 118140960795 + 387262 * 2 ^ 59
def prefixEnd_387262 : Nat := 4983230072969 + 3 ^ 40 * 387262 * 2
def baseEnd_387262 : Nat := 198851545221569069344021

theorem tailTrace_387262 : CollatzResearch.WordTrace tailWord_387262 prefixEnd_387262 198851545221569069344021 := by
  unfold tailWord_387262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1765575690377923491138505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9416403682015591952738693 1765575690377923491138505)
  ·
    refine ⟨1324181767783442618353879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1765575690377923491138505 1324181767783442618353879)
    ·
      refine ⟨1986272651675163927530819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1324181767783442618353879 1986272651675163927530819)
      ·
        refine ⟨2979408977512745891296229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986272651675163927530819 2979408977512745891296229)
        ·
          refine ⟨558639183283639854618043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2979408977512745891296229 558639183283639854618043)
          ·
            refine ⟨837958774925459781927065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558639183283639854618043 837958774925459781927065)
            ·
              refine ⟨628469081194094836445299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837958774925459781927065 628469081194094836445299)
              ·
                refine ⟨942703621791142254667949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628469081194094836445299 942703621791142254667949)
                ·
                  refine ⟨353513858171678345500481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942703621791142254667949 353513858171678345500481)
                  ·
                    refine ⟨265135393628758759125361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 353513858171678345500481 265135393628758759125361)
                    ·
                      refine ⟨198851545221569069344021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 265135393628758759125361 198851545221569069344021)
                      ·
                        rfl

theorem cell23_387262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_387262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387262 prefixEnd_387262 := by exact prefixLift 387262
  have htrace : WordTrace (prefixWord ++ tailWord_387262) baseStart_387262 baseEnd_387262 := by
    simpa [prefixWord, tailWord_387262, baseEnd_387262] using wordTrace_append hprefix tailTrace_387262
  have hstable : (prefixWord ++ tailWord_387262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387262).length < 2 ^ (prefixWord ++ tailWord_387262).sum := by decide
  have hdescent : baseEnd_387262 < baseStart_387262 := by decide
  rcases family_descends (prefixWord ++ tailWord_387262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387278 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_387278 : Nat := 118140960795 + 387278 * 2 ^ 59
def prefixEnd_387278 : Nat := 4983230072969 + 3 ^ 40 * 387278 * 2
def baseEnd_387278 : Nat := 198859760912041006743947

theorem tailTrace_387278 : CollatzResearch.WordTrace tailWord_387278 prefixEnd_387278 198859760912041006743947 := by
  unfold tailWord_387278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1765648636370677832711311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9416792727310281774460325 1765648636370677832711311)
  ·
    refine ⟨2648472954556016749066967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1765648636370677832711311 2648472954556016749066967)
    ·
      refine ⟨3972709431834025123600451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2648472954556016749066967 3972709431834025123600451)
      ·
        refine ⟨5959064147751037685400677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972709431834025123600451 5959064147751037685400677)
        ·
          refine ⟨1117324527703319566012627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5959064147751037685400677 1117324527703319566012627)
          ·
            refine ⟨1675986791554979349018941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117324527703319566012627 1675986791554979349018941)
            ·
              refine ⟨628495046833117255882103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1675986791554979349018941 628495046833117255882103)
              ·
                refine ⟨942742570249675883823155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628495046833117255882103 942742570249675883823155)
                ·
                  refine ⟨1414113855374513825734733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 942742570249675883823155 1414113855374513825734733)
                  ·
                    refine ⟨530292695765442684650525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1414113855374513825734733 530292695765442684650525)
                    ·
                      refine ⟨198859760912041006743947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 530292695765442684650525 198859760912041006743947)
                      ·
                        rfl

theorem cell23_387278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_387278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387278 prefixEnd_387278 := by exact prefixLift 387278
  have htrace : WordTrace (prefixWord ++ tailWord_387278) baseStart_387278 baseEnd_387278 := by
    simpa [prefixWord, tailWord_387278, baseEnd_387278] using wordTrace_append hprefix tailTrace_387278
  have hstable : (prefixWord ++ tailWord_387278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387278).length < 2 ^ (prefixWord ++ tailWord_387278).sum := by decide
  have hdescent : baseEnd_387278 < baseStart_387278 := by decide
  rcases family_descends (prefixWord ++ tailWord_387278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387285 : List Nat := [1, 3, 2, 4, 3, 1, 2, 7]
def baseStart_387285 : Nat := 118140960795 + 387285 * 2 ^ 59
def prefixEnd_387285 : Nat := 4983230072969 + 3 ^ 40 * 387285 * 2
def baseEnd_387285 : Nat := 7365309454689721457645

theorem tailTrace_387285 : CollatzResearch.WordTrace tailWord_387285 prefixEnd_387285 7365309454689721457645 := by
  unfold tailWord_387285
  simp only [CollatzResearch.WordTrace]
  refine ⟨14125444401940062857195309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9416962934626708571463539 14125444401940062857195309)
  ·
    refine ⟨5297041650727523571448241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14125444401940062857195309 5297041650727523571448241)
    ·
      refine ⟨3972781238045642678586181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5297041650727523571448241 3972781238045642678586181)
      ·
        refine ⟨744896482133558002234909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3972781238045642678586181 744896482133558002234909)
        ·
          refine ⟨279336180800084250838091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 744896482133558002234909 279336180800084250838091)
          ·
            refine ⟨419004271200126376257137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279336180800084250838091 419004271200126376257137)
            ·
              refine ⟨314253203400094782192853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419004271200126376257137 314253203400094782192853)
              ·
                refine ⟨7365309454689721457645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 314253203400094782192853 7365309454689721457645)
                ·
                  rfl

theorem cell23_387285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 7].length) (baseStart_387285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387285 prefixEnd_387285 := by exact prefixLift 387285
  have htrace : WordTrace (prefixWord ++ tailWord_387285) baseStart_387285 baseEnd_387285 := by
    simpa [prefixWord, tailWord_387285, baseEnd_387285] using wordTrace_append hprefix tailTrace_387285
  have hstable : (prefixWord ++ tailWord_387285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387285).length < 2 ^ (prefixWord ++ tailWord_387285).sum := by decide
  have hdescent : baseEnd_387285 < baseStart_387285 := by decide
  rcases family_descends (prefixWord ++ tailWord_387285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387381 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_387381 : Nat := 118140960795 + 387381 * 2 ^ 59
def prefixEnd_387381 : Nat := 4983230072969 + 3 ^ 40 * 387381 * 2
def baseEnd_387381 : Nat := 198912649419454103755973

theorem tailTrace_387381 : CollatzResearch.WordTrace tailWord_387381 prefixEnd_387381 198912649419454103755973 := by
  unfold tailWord_387381
  simp only [CollatzResearch.WordTrace]
  refine ⟨14128945809592271252689997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9419297206394847501793331 14128945809592271252689997)
  ·
    refine ⟨5298354678597101719758749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14128945809592271252689997 5298354678597101719758749)
    ·
      refine ⟨1986883004473913144909531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5298354678597101719758749 1986883004473913144909531)
      ·
        refine ⟨2980324506710869717364297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986883004473913144909531 2980324506710869717364297)
        ·
          refine ⟨2235243380033152288023223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2980324506710869717364297 2235243380033152288023223)
          ·
            refine ⟨3352865070049728432034835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235243380033152288023223 3352865070049728432034835)
            ·
              refine ⟨5029297605074592648052253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352865070049728432034835 5029297605074592648052253)
              ·
                refine ⟨1885986601902972243019595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5029297605074592648052253 1885986601902972243019595)
                ·
                  refine ⟨2828979902854458364529393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885986601902972243019595 2828979902854458364529393)
                  ·
                    refine ⟨2121734927140843773397045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2828979902854458364529393 2121734927140843773397045)
                    ·
                      refine ⟨198912649419454103755973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2121734927140843773397045 198912649419454103755973)
                      ·
                        rfl

theorem cell23_387381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_387381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387381 prefixEnd_387381 := by exact prefixLift 387381
  have htrace : WordTrace (prefixWord ++ tailWord_387381) baseStart_387381 baseEnd_387381 := by
    simpa [prefixWord, tailWord_387381, baseEnd_387381] using wordTrace_append hprefix tailTrace_387381
  have hstable : (prefixWord ++ tailWord_387381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387381).length < 2 ^ (prefixWord ++ tailWord_387381).sum := by decide
  have hdescent : baseEnd_387381 < baseStart_387381 := by decide
  rcases family_descends (prefixWord ++ tailWord_387381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387391 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 4]
def baseStart_387391 : Nat := 118140960795 + 387391 * 2 ^ 59
def prefixEnd_387391 : Nat := 4983230072969 + 3 ^ 40 * 387391 * 2
def baseEnd_387391 : Nat := 198917784225999064630927

theorem tailTrace_387391 : CollatzResearch.WordTrace tailWord_387391 prefixEnd_387391 198917784225999064630927 := by
  unfold tailWord_387391
  simp only [CollatzResearch.WordTrace]
  refine ⟨14129310539556042960554027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9419540359704028640369351 14129310539556042960554027)
  ·
    refine ⟨21193965809334064440831041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14129310539556042960554027 21193965809334064440831041)
    ·
      refine ⟨15895474357000548330623281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21193965809334064440831041 15895474357000548330623281)
      ·
        refine ⟨11921605767750411247967461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15895474357000548330623281 11921605767750411247967461)
        ·
          refine ⟨2235301081453202108993899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11921605767750411247967461 2235301081453202108993899)
          ·
            refine ⟨3352951622179803163490849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235301081453202108993899 3352951622179803163490849)
            ·
              refine ⟨2514713716634852372618137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3352951622179803163490849 2514713716634852372618137)
              ·
                refine ⟨1886035287476139279463603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514713716634852372618137 1886035287476139279463603)
                ·
                  refine ⟨2829052931214208919195405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886035287476139279463603 2829052931214208919195405)
                  ·
                    refine ⟨1060894849205328344698277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2829052931214208919195405 1060894849205328344698277)
                    ·
                      refine ⟨198917784225999064630927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1060894849205328344698277 198917784225999064630927)
                      ·
                        rfl

theorem cell23_387391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_387391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387391 prefixEnd_387391 := by exact prefixLift 387391
  have htrace : WordTrace (prefixWord ++ tailWord_387391) baseStart_387391 baseEnd_387391 := by
    simpa [prefixWord, tailWord_387391, baseEnd_387391] using wordTrace_append hprefix tailTrace_387391
  have hstable : (prefixWord ++ tailWord_387391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387391).length < 2 ^ (prefixWord ++ tailWord_387391).sum := by decide
  have hdescent : baseEnd_387391 < baseStart_387391 := by decide
  rcases family_descends (prefixWord ++ tailWord_387391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387408 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 4]
def baseStart_387408 : Nat := 118140960795 + 387408 * 2 ^ 59
def prefixEnd_387408 : Nat := 4983230072969 + 3 ^ 40 * 387408 * 2
def baseEnd_387408 : Nat := 198926513397125498118349

theorem tailTrace_387408 : CollatzResearch.WordTrace tailWord_387408 prefixEnd_387408 198926513397125498118349 := by
  unfold tailWord_387408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7064965290247227431961439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9419953720329636575948585 7064965290247227431961439)
  ·
    refine ⟨10597447935370841147942159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7064965290247227431961439 10597447935370841147942159)
    ·
      refine ⟨15896171903056261721913239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10597447935370841147942159 15896171903056261721913239)
      ·
        refine ⟨23844257854584392582869859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15896171903056261721913239 23844257854584392582869859)
        ·
          refine ⟨35766386781876588874304789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23844257854584392582869859 35766386781876588874304789)
          ·
            refine ⟨1676549380400465103483037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35766386781876588874304789 1676549380400465103483037)
            ·
              refine ⟨628706017650174413806139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1676549380400465103483037 628706017650174413806139)
              ·
                refine ⟨943059026475261620709209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628706017650174413806139 943059026475261620709209)
                ·
                  refine ⟨707294269856446215531907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 943059026475261620709209 707294269856446215531907)
                  ·
                    refine ⟨1060941404784669323297861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 707294269856446215531907 1060941404784669323297861)
                    ·
                      refine ⟨198926513397125498118349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1060941404784669323297861 198926513397125498118349)
                      ·
                        rfl

theorem cell23_387408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 4].length) (baseStart_387408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387408 prefixEnd_387408 := by exact prefixLift 387408
  have htrace : WordTrace (prefixWord ++ tailWord_387408) baseStart_387408 baseEnd_387408 := by
    simpa [prefixWord, tailWord_387408, baseEnd_387408] using wordTrace_append hprefix tailTrace_387408
  have hstable : (prefixWord ++ tailWord_387408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387408).length < 2 ^ (prefixWord ++ tailWord_387408).sum := by decide
  have hdescent : baseEnd_387408 < baseStart_387408 := by decide
  rcases family_descends (prefixWord ++ tailWord_387408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387428 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_387428 : Nat := 118140960795 + 387428 * 2 ^ 59
def prefixEnd_387428 : Nat := 4983230072969 + 3 ^ 40 * 387428 * 2
def baseEnd_387428 : Nat := 198936783010215419868257

theorem tailTrace_387428 : CollatzResearch.WordTrace tailWord_387428 prefixEnd_387428 198936783010215419868257 := by
  unfold tailWord_387428
  simp only [CollatzResearch.WordTrace]
  refine ⟨7065330020210999139825469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9420440026947998853100625 7065330020210999139825469)
  ·
    refine ⟨2649498757579124677434551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7065330020210999139825469 2649498757579124677434551)
    ·
      refine ⟨3974248136368687016151827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2649498757579124677434551 3974248136368687016151827)
      ·
        refine ⟨5961372204553030524227741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3974248136368687016151827 5961372204553030524227741)
        ·
          refine ⟨2235514576707386446585403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5961372204553030524227741 2235514576707386446585403)
          ·
            refine ⟨3353271865061079669878105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235514576707386446585403 3353271865061079669878105)
            ·
              refine ⟨2514953898795809752408579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3353271865061079669878105 2514953898795809752408579)
              ·
                refine ⟨3772430848193714628612869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514953898795809752408579 3772430848193714628612869)
                ·
                  refine ⟨707330784036321492864913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3772430848193714628612869 707330784036321492864913)
                  ·
                    refine ⟨530498088027241119648685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 707330784036321492864913 530498088027241119648685)
                    ·
                      refine ⟨198936783010215419868257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 530498088027241119648685 198936783010215419868257)
                      ·
                        rfl

theorem cell23_387428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_387428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387428 prefixEnd_387428 := by exact prefixLift 387428
  have htrace : WordTrace (prefixWord ++ tailWord_387428) baseStart_387428 baseEnd_387428 := by
    simpa [prefixWord, tailWord_387428, baseEnd_387428] using wordTrace_append hprefix tailTrace_387428
  have hstable : (prefixWord ++ tailWord_387428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387428).length < 2 ^ (prefixWord ++ tailWord_387428).sum := by decide
  have hdescent : baseEnd_387428 < baseStart_387428 := by decide
  rcases family_descends (prefixWord ++ tailWord_387428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387486 : List Nat := [4, 3, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_387486 : Nat := 118140960795 + 387486 * 2 ^ 59
def prefixEnd_387486 : Nat := 4983230072969 + 3 ^ 40 * 387486 * 2
def baseEnd_387486 : Nat := 66322188296058730980997

theorem tailTrace_387486 : CollatzResearch.WordTrace tailWord_387486 prefixEnd_387486 66322188296058730980997 := by
  unfold tailWord_387486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1766596934276484273157789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9421850316141249456841541 1766596934276484273157789)
  ·
    refine ⟨662473850353681602434171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1766596934276484273157789 662473850353681602434171)
    ·
      refine ⟨993710775530522403651257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 662473850353681602434171 993710775530522403651257)
      ·
        refine ⟨745283081647891802738443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 993710775530522403651257 745283081647891802738443)
        ·
          refine ⟨1117924622471837704107665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745283081647891802738443 1117924622471837704107665)
          ·
            refine ⟨838443466853878278080749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1117924622471837704107665 838443466853878278080749)
            ·
              refine ⟨314416300070204354280281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 838443466853878278080749 314416300070204354280281)
              ·
                refine ⟨235812225052653265710211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314416300070204354280281 235812225052653265710211)
                ·
                  refine ⟨353718337578979898565317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235812225052653265710211 353718337578979898565317)
                  ·
                    refine ⟨66322188296058730980997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 353718337578979898565317 66322188296058730980997)
                    ·
                      rfl

theorem cell23_387486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_387486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387486 prefixEnd_387486 := by exact prefixLift 387486
  have htrace : WordTrace (prefixWord ++ tailWord_387486) baseStart_387486 baseEnd_387486 := by
    simpa [prefixWord, tailWord_387486, baseEnd_387486] using wordTrace_append hprefix tailTrace_387486
  have hstable : (prefixWord ++ tailWord_387486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387486).length < 2 ^ (prefixWord ++ tailWord_387486).sum := by decide
  have hdescent : baseEnd_387486 < baseStart_387486 := by decide
  rcases family_descends (prefixWord ++ tailWord_387486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387492 : List Nat := [2, 3, 1, 2, 1, 1, 2, 6, 1, 1, 3]
def baseStart_387492 : Nat := 118140960795 + 387492 * 2 ^ 59
def prefixEnd_387492 : Nat := 4983230072969 + 3 ^ 40 * 387492 * 2
def baseEnd_387492 : Nat := 198969645772103169467963

theorem tailTrace_387492 : CollatzResearch.WordTrace tailWord_387492 prefixEnd_387492 198969645772103169467963 := by
  unfold tailWord_387492
  simp only [CollatzResearch.WordTrace]
  refine ⟨7066497156095068604990365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9421996208126758139987153 7066497156095068604990365)
  ·
    refine ⟨2649936433535650726871387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7066497156095068604990365 2649936433535650726871387)
    ·
      refine ⟨3974904650303476090307081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2649936433535650726871387 3974904650303476090307081)
      ·
        refine ⟨2981178487727607067730311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3974904650303476090307081 2981178487727607067730311)
        ·
          refine ⟨4471767731591410601595467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981178487727607067730311 4471767731591410601595467)
          ·
            refine ⟨6707651597387115902393201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471767731591410601595467 6707651597387115902393201)
            ·
              refine ⟨5030738698040336926794901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6707651597387115902393201 5030738698040336926794901)
              ·
                refine ⟨235815876470640793443511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5030738698040336926794901 235815876470640793443511)
                ·
                  refine ⟨353723814705961190165267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235815876470640793443511 353723814705961190165267)
                  ·
                    refine ⟨530585722058941785247901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 353723814705961190165267 530585722058941785247901)
                    ·
                      refine ⟨198969645772103169467963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 530585722058941785247901 198969645772103169467963)
                      ·
                        rfl

theorem cell23_387492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_387492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387492 prefixEnd_387492 := by exact prefixLift 387492
  have htrace : WordTrace (prefixWord ++ tailWord_387492) baseStart_387492 baseEnd_387492 := by
    simpa [prefixWord, tailWord_387492, baseEnd_387492] using wordTrace_append hprefix tailTrace_387492
  have hstable : (prefixWord ++ tailWord_387492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387492).length < 2 ^ (prefixWord ++ tailWord_387492).sum := by decide
  have hdescent : baseEnd_387492 < baseStart_387492 := by decide
  rcases family_descends (prefixWord ++ tailWord_387492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387518 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_387518 : Nat := 118140960795 + 387518 * 2 ^ 59
def prefixEnd_387518 : Nat := 4983230072969 + 3 ^ 40 * 387518 * 2
def baseEnd_387518 : Nat := 198982996269120067742843

theorem tailTrace_387518 : CollatzResearch.WordTrace tailWord_387518 prefixEnd_387518 198982996269120067742843 := by
  unfold tailWord_387518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1766742826261992956303401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9422628406730629100284805 1766742826261992956303401)
  ·
    refine ⟨1325057119696494717227551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1766742826261992956303401 1325057119696494717227551)
    ·
      refine ⟨1987585679544742075841327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1325057119696494717227551 1987585679544742075841327)
      ·
        refine ⟨2981378519317113113761991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1987585679544742075841327 2981378519317113113761991)
        ·
          refine ⟨4472067778975669670642987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981378519317113113761991 4472067778975669670642987)
          ·
            refine ⟨6708101668463504505964481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472067778975669670642987 6708101668463504505964481)
            ·
              refine ⟨5031076251347628379473361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6708101668463504505964481 5031076251347628379473361)
              ·
                refine ⟨3773307188510721284605021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5031076251347628379473361 3773307188510721284605021)
                ·
                  refine ⟨1414990195691520481726883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3773307188510721284605021 1414990195691520481726883)
                  ·
                    refine ⟨2122485293537280722590325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1414990195691520481726883 2122485293537280722590325)
                    ·
                      refine ⟨198982996269120067742843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2122485293537280722590325 198982996269120067742843)
                      ·
                        rfl

theorem cell23_387518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_387518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387518 prefixEnd_387518 := by exact prefixLift 387518
  have htrace : WordTrace (prefixWord ++ tailWord_387518) baseStart_387518 baseEnd_387518 := by
    simpa [prefixWord, tailWord_387518, baseEnd_387518] using wordTrace_append hprefix tailTrace_387518
  have hstable : (prefixWord ++ tailWord_387518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387518).length < 2 ^ (prefixWord ++ tailWord_387518).sum := by decide
  have hdescent : baseEnd_387518 < baseStart_387518 := by decide
  rcases family_descends (prefixWord ++ tailWord_387518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387528 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_387528 : Nat := 118140960795 + 387528 * 2 ^ 59
def prefixEnd_387528 : Nat := 4983230072969 + 3 ^ 40 * 387528 * 2
def baseEnd_387528 : Nat := 198988131075665028617797

theorem tailTrace_387528 : CollatzResearch.WordTrace tailWord_387528 prefixEnd_387528 198988131075665028617797 := by
  unfold tailWord_387528
  simp only [CollatzResearch.WordTrace]
  refine ⟨7067153670029857679145619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9422871560039810238860825 7067153670029857679145619)
  ·
    refine ⟨10600730505044786518718429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7067153670029857679145619 10600730505044786518718429)
    ·
      refine ⟨3975273939391794944519411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10600730505044786518718429 3975273939391794944519411)
      ·
        refine ⟨5962910909087692416779117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3975273939391794944519411 5962910909087692416779117)
        ·
          refine ⟨2236091590907884656292169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5962910909087692416779117 2236091590907884656292169)
          ·
            refine ⟨1677068693180913492219127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2236091590907884656292169 1677068693180913492219127)
            ·
              refine ⟨2515603039771370238328691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1677068693180913492219127 2515603039771370238328691)
              ·
                refine ⟨3773404559657055357493037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2515603039771370238328691 3773404559657055357493037)
                ·
                  refine ⟨1415026709871395759059889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3773404559657055357493037 1415026709871395759059889)
                  ·
                    refine ⟨1061270032403546819294917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1415026709871395759059889 1061270032403546819294917)
                    ·
                      refine ⟨198988131075665028617797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1061270032403546819294917 198988131075665028617797)
                      ·
                        rfl

theorem cell23_387528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_387528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387528 prefixEnd_387528 := by exact prefixLift 387528
  have htrace : WordTrace (prefixWord ++ tailWord_387528) baseStart_387528 baseEnd_387528 := by
    simpa [prefixWord, tailWord_387528, baseEnd_387528] using wordTrace_append hprefix tailTrace_387528
  have hstable : (prefixWord ++ tailWord_387528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387528).length < 2 ^ (prefixWord ++ tailWord_387528).sum := by decide
  have hdescent : baseEnd_387528 < baseStart_387528 := by decide
  rcases family_descends (prefixWord ++ tailWord_387528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387538 : List Nat := [3, 2, 2, 4, 12]
def baseStart_387538 : Nat := 118140960795 + 387538 * 2 ^ 59
def prefixEnd_387538 : Nat := 4983230072969 + 3 ^ 40 * 387538 * 2
def baseEnd_387538 : Nat := 272967442911124814119

theorem tailTrace_387538 : CollatzResearch.WordTrace tailWord_387538 prefixEnd_387538 272967442911124814119 := by
  unfold tailWord_387538
  simp only [CollatzResearch.WordTrace]
  refine ⟨3533668017505871766538817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9423114713348991377436845 3533668017505871766538817)
  ·
    refine ⟨2650251013129403824904113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3533668017505871766538817 2650251013129403824904113)
    ·
      refine ⟨1987688259847052868678085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2650251013129403824904113 1987688259847052868678085)
      ·
        refine ⟨372691548721322412877141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1987688259847052868678085 372691548721322412877141)
        ·
          refine ⟨272967442911124814119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 372691548721322412877141 272967442911124814119)
          ·
            rfl

theorem cell23_387538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 12].length) (baseStart_387538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387538 prefixEnd_387538 := by exact prefixLift 387538
  have htrace : WordTrace (prefixWord ++ tailWord_387538) baseStart_387538 baseEnd_387538 := by
    simpa [prefixWord, tailWord_387538, baseEnd_387538] using wordTrace_append hprefix tailTrace_387538
  have hstable : (prefixWord ++ tailWord_387538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387538).length < 2 ^ (prefixWord ++ tailWord_387538).sum := by decide
  have hdescent : baseEnd_387538 < baseStart_387538 := by decide
  rcases family_descends (prefixWord ++ tailWord_387538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387555 : List Nat := [1, 1, 1, 6, 3, 2, 1, 8]
def baseStart_387555 : Nat := 118140960795 + 387555 * 2 ^ 59
def prefixEnd_387555 : Nat := 4983230072969 + 3 ^ 40 * 387555 * 2
def baseEnd_387555 : Nat := 7370444261234682332599

theorem tailTrace_387555 : CollatzResearch.WordTrace tailWord_387555 prefixEnd_387555 7370444261234682332599 := by
  unfold tailWord_387555
  simp only [CollatzResearch.WordTrace]
  refine ⟨14135292110961898969524119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9423528073974599313016079 14135292110961898969524119)
  ·
    refine ⟨21202938166442848454286179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14135292110961898969524119 21202938166442848454286179)
    ·
      refine ⟨31804407249664272681429269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21202938166442848454286179 31804407249664272681429269)
      ·
        refine ⟨1490831589828012781941997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31804407249664272681429269 1490831589828012781941997)
        ·
          refine ⟨559061846185504793228249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1490831589828012781941997 559061846185504793228249)
          ·
            refine ⟨419296384639128594921187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559061846185504793228249 419296384639128594921187)
            ·
              refine ⟨628944576958692892381781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419296384639128594921187 628944576958692892381781)
              ·
                refine ⟨7370444261234682332599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 628944576958692892381781 7370444261234682332599)
                ·
                  rfl

theorem cell23_387555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 8].length) (baseStart_387555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387555 prefixEnd_387555 := by exact prefixLift 387555
  have htrace : WordTrace (prefixWord ++ tailWord_387555) baseStart_387555 baseEnd_387555 := by
    simpa [prefixWord, tailWord_387555, baseEnd_387555] using wordTrace_append hprefix tailTrace_387555
  have hstable : (prefixWord ++ tailWord_387555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387555).length < 2 ^ (prefixWord ++ tailWord_387555).sum := by decide
  have hdescent : baseEnd_387555 < baseStart_387555 := by decide
  rcases family_descends (prefixWord ++ tailWord_387555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387616 : List Nat := [2, 1, 1, 6, 2, 1, 3, 1, 2, 1, 3]
def baseStart_387616 : Nat := 118140960795 + 387616 * 2 ^ 59
def prefixEnd_387616 : Nat := 4983230072969 + 3 ^ 40 * 387616 * 2
def baseEnd_387616 : Nat := 199033317373260684317393

theorem tailTrace_387616 : CollatzResearch.WordTrace tailWord_387616 prefixEnd_387616 199033317373260684317393 := by
  unfold tailWord_387616
  simp only [CollatzResearch.WordTrace]
  refine ⟨7068758481870453193747351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9425011309160604258329801 7068758481870453193747351)
  ·
    refine ⟨10603137722805679790621027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7068758481870453193747351 10603137722805679790621027)
    ·
      refine ⟨15904706584208519685931541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10603137722805679790621027 15904706584208519685931541)
      ·
        refine ⟨745533121134774360278041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15904706584208519685931541 745533121134774360278041)
        ·
          refine ⟨559149840851080770208531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 745533121134774360278041 559149840851080770208531)
          ·
            refine ⟨838724761276621155312797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559149840851080770208531 838724761276621155312797)
            ·
              refine ⟨314521785478732933242299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 838724761276621155312797 314521785478732933242299)
              ·
                refine ⟨471782678218099399863449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314521785478732933242299 471782678218099399863449)
                ·
                  refine ⟨353837008663574549897587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471782678218099399863449 353837008663574549897587)
                  ·
                    refine ⟨530755512995361824846381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 353837008663574549897587 530755512995361824846381)
                    ·
                      refine ⟨199033317373260684317393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 530755512995361824846381 199033317373260684317393)
                      ·
                        rfl

theorem cell23_387616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_387616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387616 prefixEnd_387616 := by exact prefixLift 387616
  have htrace : WordTrace (prefixWord ++ tailWord_387616) baseStart_387616 baseEnd_387616 := by
    simpa [prefixWord, tailWord_387616, baseEnd_387616] using wordTrace_append hprefix tailTrace_387616
  have hstable : (prefixWord ++ tailWord_387616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387616).length < 2 ^ (prefixWord ++ tailWord_387616).sum := by decide
  have hdescent : baseEnd_387616 < baseStart_387616 := by decide
  rcases family_descends (prefixWord ++ tailWord_387616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387695 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 4]
def baseStart_387695 : Nat := 118140960795 + 387695 * 2 ^ 59
def prefixEnd_387695 : Nat := 4983230072969 + 3 ^ 40 * 387695 * 2
def baseEnd_387695 : Nat := 199073882344965875229529

theorem tailTrace_387695 : CollatzResearch.WordTrace tailWord_387695 prefixEnd_387695 199073882344965875229529 := by
  unfold tailWord_387695
  simp only [CollatzResearch.WordTrace]
  refine ⟨14140398330454702879620539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9426932220303135253080359 14140398330454702879620539)
  ·
    refine ⟨21210597495682054319430809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14140398330454702879620539 21210597495682054319430809)
    ·
      refine ⟨15907948121761540739573107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21210597495682054319430809 15907948121761540739573107)
      ·
        refine ⟨23861922182642311109359661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15907948121761540739573107 23861922182642311109359661)
        ·
          refine ⟨8948220818490866666009873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23861922182642311109359661 8948220818490866666009873)
          ·
            refine ⟨6711165613868149999507405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8948220818490866666009873 6711165613868149999507405)
            ·
              refine ⟨2516687105200556249815277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6711165613868149999507405 2516687105200556249815277)
              ·
                refine ⟨943757664450208593680729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2516687105200556249815277 943757664450208593680729)
                ·
                  refine ⟨707818248337656445260547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 943757664450208593680729 707818248337656445260547)
                  ·
                    refine ⟨1061727372506484667890821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 707818248337656445260547 1061727372506484667890821)
                    ·
                      refine ⟨199073882344965875229529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1061727372506484667890821 199073882344965875229529)
                      ·
                        rfl

theorem cell23_387695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_387695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387695 prefixEnd_387695 := by exact prefixLift 387695
  have htrace : WordTrace (prefixWord ++ tailWord_387695) baseStart_387695 baseEnd_387695 := by
    simpa [prefixWord, tailWord_387695, baseEnd_387695] using wordTrace_append hprefix tailTrace_387695
  have hstable : (prefixWord ++ tailWord_387695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387695).length < 2 ^ (prefixWord ++ tailWord_387695).sum := by decide
  have hdescent : baseEnd_387695 < baseStart_387695 := by decide
  rcases family_descends (prefixWord ++ tailWord_387695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387735 : List Nat := [1, 1, 3, 3, 2, 1, 1, 5, 6]
def baseStart_387735 : Nat := 118140960795 + 387735 * 2 ^ 59
def prefixEnd_387735 : Nat := 4983230072969 + 3 ^ 40 * 387735 * 2
def baseEnd_387735 : Nat := 22121602396793968747705

theorem tailTrace_387735 : CollatzResearch.WordTrace tailWord_387735 prefixEnd_387735 22121602396793968747705 := by
  unfold tailWord_387735
  simp only [CollatzResearch.WordTrace]
  refine ⟨14141857250309789711076659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9427904833539859807384439 14141857250309789711076659)
  ·
    refine ⟨21212785875464684566614989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14141857250309789711076659 21212785875464684566614989)
    ·
      refine ⟨7954794703299256712480621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21212785875464684566614989 7954794703299256712480621)
      ·
        refine ⟨2983048013737221267180233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7954794703299256712480621 2983048013737221267180233)
        ·
          refine ⟨2237286010302915950385175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2983048013737221267180233 2237286010302915950385175)
          ·
            refine ⟨3355929015454373925577763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237286010302915950385175 3355929015454373925577763)
            ·
              refine ⟨5033893523181560888366645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355929015454373925577763 5033893523181560888366645)
              ·
                refine ⟨471927517798271333284373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5033893523181560888366645 471927517798271333284373)
                ·
                  refine ⟨22121602396793968747705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 471927517798271333284373 22121602396793968747705)
                  ·
                    rfl

theorem cell23_387735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 6].length) (baseStart_387735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387735 prefixEnd_387735 := by exact prefixLift 387735
  have htrace : WordTrace (prefixWord ++ tailWord_387735) baseStart_387735 baseEnd_387735 := by
    simpa [prefixWord, tailWord_387735, baseEnd_387735] using wordTrace_append hprefix tailTrace_387735
  have hstable : (prefixWord ++ tailWord_387735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387735).length < 2 ^ (prefixWord ++ tailWord_387735).sum := by decide
  have hdescent : baseEnd_387735 < baseStart_387735 := by decide
  rcases family_descends (prefixWord ++ tailWord_387735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387762 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_387762 : Nat := 118140960795 + 387762 * 2 ^ 59
def prefixEnd_387762 : Nat := 4983230072969 + 3 ^ 40 * 387762 * 2
def baseEnd_387762 : Nat := 199108285548817113091721

theorem tailTrace_387762 : CollatzResearch.WordTrace tailWord_387762 prefixEnd_387762 199108285548817113091721 := by
  unfold tailWord_387762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3535710505302993330577385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9428561347474648881539693 3535710505302993330577385)
  ·
    refine ⟨2651782878977244997933039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3535710505302993330577385 2651782878977244997933039)
    ·
      refine ⟨3977674318465867496899559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2651782878977244997933039 3977674318465867496899559)
      ·
        refine ⟨5966511477698801245349339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3977674318465867496899559 5966511477698801245349339)
        ·
          refine ⟨8949767216548201868024009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5966511477698801245349339 8949767216548201868024009)
          ·
            refine ⟨6712325412411151401018007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8949767216548201868024009 6712325412411151401018007)
            ·
              refine ⟨10068488118616727101527011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6712325412411151401018007 10068488118616727101527011)
              ·
                refine ⟨15102732177925090652290517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10068488118616727101527011 15102732177925090652290517)
                ·
                  refine ⟨353970285420119312163059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15102732177925090652290517 353970285420119312163059)
                  ·
                    refine ⟨530955428130178968244589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 353970285420119312163059 530955428130178968244589)
                    ·
                      refine ⟨199108285548817113091721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 530955428130178968244589 199108285548817113091721)
                      ·
                        rfl

theorem cell23_387762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_387762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387762 prefixEnd_387762 := by exact prefixLift 387762
  have htrace : WordTrace (prefixWord ++ tailWord_387762) baseStart_387762 baseEnd_387762 := by
    simpa [prefixWord, tailWord_387762, baseEnd_387762] using wordTrace_append hprefix tailTrace_387762
  have hstable : (prefixWord ++ tailWord_387762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387762).length < 2 ^ (prefixWord ++ tailWord_387762).sum := by decide
  have hdescent : baseEnd_387762 < baseStart_387762 := by decide
  rcases family_descends (prefixWord ++ tailWord_387762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387802 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2]
def baseStart_387802 : Nat := 118140960795 + 387802 * 2 ^ 59
def prefixEnd_387802 : Nat := 4983230072969 + 3 ^ 40 * 387802 * 2
def baseEnd_387802 : Nat := 199128824774996956591537

theorem tailTrace_387802 : CollatzResearch.WordTrace tailWord_387802 prefixEnd_387802 199128824774996956591537 := by
  unfold tailWord_387802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3536075235266765038441415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9429533960711373435843773 3536075235266765038441415)
  ·
    refine ⟨5304112852900147557662123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3536075235266765038441415 5304112852900147557662123)
    ·
      refine ⟨7956169279350221336493185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5304112852900147557662123 7956169279350221336493185)
      ·
        refine ⟨5967126959512666002369889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7956169279350221336493185 5967126959512666002369889)
        ·
          refine ⟨4475345219634499501777417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5967126959512666002369889 4475345219634499501777417)
          ·
            refine ⟨3356508914725874626333063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4475345219634499501777417 3356508914725874626333063)
            ·
              refine ⟨5034763372088811939499595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3356508914725874626333063 5034763372088811939499595)
              ·
                refine ⟨7552145058133217909249393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5034763372088811939499595 7552145058133217909249393)
                ·
                  refine ⟨5664108793599913431937045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7552145058133217909249393 5664108793599913431937045)
                  ·
                    refine ⟨265505099699995942122049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5664108793599913431937045 265505099699995942122049)
                    ·
                      refine ⟨199128824774996956591537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 265505099699995942122049 199128824774996956591537)
                      ·
                        rfl

theorem cell23_387802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_387802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387802 prefixEnd_387802 := by exact prefixLift 387802
  have htrace : WordTrace (prefixWord ++ tailWord_387802) baseStart_387802 baseEnd_387802 := by
    simpa [prefixWord, tailWord_387802, baseEnd_387802] using wordTrace_append hprefix tailTrace_387802
  have hstable : (prefixWord ++ tailWord_387802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387802).length < 2 ^ (prefixWord ++ tailWord_387802).sum := by decide
  have hdescent : baseEnd_387802 < baseStart_387802 := by decide
  rcases family_descends (prefixWord ++ tailWord_387802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387812 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_387812 : Nat := 118140960795 + 387812 * 2 ^ 59
def prefixEnd_387812 : Nat := 4983230072969 + 3 ^ 40 * 387812 * 2
def baseEnd_387812 : Nat := 66377986527180639155497

theorem tailTrace_387812 : CollatzResearch.WordTrace tailWord_387812 prefixEnd_387812 66377986527180639155497 := by
  unfold tailWord_387812
  simp only [CollatzResearch.WordTrace]
  refine ⟨7072332835515415930814845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9429777114020554574419793 7072332835515415930814845)
  ·
    refine ⟨2652124813318280974055567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7072332835515415930814845 2652124813318280974055567)
    ·
      refine ⟨3978187219977421461083351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2652124813318280974055567 3978187219977421461083351)
      ·
        refine ⟨5967280829966132191625027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3978187219977421461083351 5967280829966132191625027)
        ·
          refine ⟨8950921244949198287437541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5967280829966132191625027 8950921244949198287437541)
          ·
            refine ⟨1678297733427974678894539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8950921244949198287437541 1678297733427974678894539)
            ·
              refine ⟨2517446600141962018341809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678297733427974678894539 2517446600141962018341809)
              ·
                refine ⟨1888084950106471513756357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2517446600141962018341809 1888084950106471513756357)
                ·
                  refine ⟨354015928144963408829317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1888084950106471513756357 354015928144963408829317)
                  ·
                    refine ⟨66377986527180639155497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 354015928144963408829317 66377986527180639155497)
                    ·
                      rfl

theorem cell23_387812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_387812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387812 prefixEnd_387812 := by exact prefixLift 387812
  have htrace : WordTrace (prefixWord ++ tailWord_387812) baseStart_387812 baseEnd_387812 := by
    simpa [prefixWord, tailWord_387812, baseEnd_387812] using wordTrace_append hprefix tailTrace_387812
  have hstable : (prefixWord ++ tailWord_387812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387812).length < 2 ^ (prefixWord ++ tailWord_387812).sum := by decide
  have hdescent : baseEnd_387812 < baseStart_387812 := by decide
  rcases family_descends (prefixWord ++ tailWord_387812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387813 : List Nat := [1, 3, 1, 4, 1, 4, 1, 3, 1, 1, 3]
def baseStart_387813 : Nat := 118140960795 + 387813 * 2 ^ 59
def prefixEnd_387813 : Nat := 4983230072969 + 3 ^ 40 * 387813 * 2
def baseEnd_387813 : Nat := 199134473062196413553987

theorem tailTrace_387813 : CollatzResearch.WordTrace tailWord_387813 prefixEnd_387813 199134473062196413553987 := by
  unfold tailWord_387813
  simp only [CollatzResearch.WordTrace]
  refine ⟨14144702144027209032416093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9429801429351472688277395 14144702144027209032416093)
  ·
    refine ⟨5304263304010203387156035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14144702144027209032416093 5304263304010203387156035)
    ·
      refine ⟨7956394956015305080734053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5304263304010203387156035 7956394956015305080734053)
      ·
        refine ⟨1491824054252869702637635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7956394956015305080734053 1491824054252869702637635)
        ·
          refine ⟨2237736081379304553956453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1491824054252869702637635 2237736081379304553956453)
          ·
            refine ⟨419575515258619603866835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2237736081379304553956453 419575515258619603866835)
            ·
              refine ⟨629363272887929405800253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419575515258619603866835 629363272887929405800253)
              ·
                refine ⟨236011227332973527175095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 629363272887929405800253 236011227332973527175095)
                ·
                  refine ⟨354016840999460290762643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236011227332973527175095 354016840999460290762643)
                  ·
                    refine ⟨531025261499190436143965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 354016840999460290762643 531025261499190436143965)
                    ·
                      refine ⟨199134473062196413553987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 531025261499190436143965 199134473062196413553987)
                      ·
                        rfl

theorem cell23_387813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_387813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387813 prefixEnd_387813 := by exact prefixLift 387813
  have htrace : WordTrace (prefixWord ++ tailWord_387813) baseStart_387813 baseEnd_387813 := by
    simpa [prefixWord, tailWord_387813, baseEnd_387813] using wordTrace_append hprefix tailTrace_387813
  have hstable : (prefixWord ++ tailWord_387813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387813).length < 2 ^ (prefixWord ++ tailWord_387813).sum := by decide
  have hdescent : baseEnd_387813 < baseStart_387813 := by decide
  rcases family_descends (prefixWord ++ tailWord_387813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387822 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_387822 : Nat := 118140960795 + 387822 * 2 ^ 59
def prefixEnd_387822 : Nat := 4983230072969 + 3 ^ 40 * 387822 * 2
def baseEnd_387822 : Nat := 199139094388086878341445

theorem tailTrace_387822 : CollatzResearch.WordTrace tailWord_387822 prefixEnd_387822 199139094388086878341445 := by
  unfold tailWord_387822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768128800124325446186715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9430020267329735712995813 1768128800124325446186715)
  ·
    refine ⟨2652193200186488169280073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1768128800124325446186715 2652193200186488169280073)
    ·
      refine ⟨1989144900139866126960055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2652193200186488169280073 1989144900139866126960055)
      ·
        refine ⟨2983717350209799190440083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989144900139866126960055 2983717350209799190440083)
        ·
          refine ⟨4475576025314698785660125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2983717350209799190440083 4475576025314698785660125)
          ·
            refine ⟨1678341009493012044622547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4475576025314698785660125 1678341009493012044622547)
            ·
              refine ⟨2517511514239518066933821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678341009493012044622547 2517511514239518066933821)
              ·
                refine ⟨944066817839819275100183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2517511514239518066933821 944066817839819275100183)
                ·
                  refine ⟨1416100226759728912650275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944066817839819275100183 1416100226759728912650275)
                  ·
                    refine ⟨2124150340139593368975413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1416100226759728912650275 2124150340139593368975413)
                    ·
                      refine ⟨199139094388086878341445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2124150340139593368975413 199139094388086878341445)
                      ·
                        rfl

theorem cell23_387822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_387822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387822 prefixEnd_387822 := by exact prefixLift 387822
  have htrace : WordTrace (prefixWord ++ tailWord_387822) baseStart_387822 baseEnd_387822 := by
    simpa [prefixWord, tailWord_387822, baseEnd_387822] using wordTrace_append hprefix tailTrace_387822
  have hstable : (prefixWord ++ tailWord_387822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387822).length < 2 ^ (prefixWord ++ tailWord_387822).sum := by decide
  have hdescent : baseEnd_387822 < baseStart_387822 := by decide
  rcases family_descends (prefixWord ++ tailWord_387822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387836 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 3, 2, 2]
def baseStart_387836 : Nat := 118140960795 + 387836 * 2 ^ 59
def prefixEnd_387836 : Nat := 4983230072969 + 3 ^ 40 * 387836 * 2
def baseEnd_387836 : Nat := 199146283117249823566381

theorem tailTrace_387836 : CollatzResearch.WordTrace tailWord_387836 prefixEnd_387836 199146283117249823566381 := by
  unfold tailWord_387836
  simp only [CollatzResearch.WordTrace]
  refine ⟨7072770511471941980251681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9430360681962589307002241 7072770511471941980251681)
  ·
    refine ⟨5304577883603956485188761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7072770511471941980251681 5304577883603956485188761)
    ·
      refine ⟨3978433412702967363891571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5304577883603956485188761 3978433412702967363891571)
      ·
        refine ⟨5967650119054451045837357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3978433412702967363891571 5967650119054451045837357)
        ·
          refine ⟨2237868794645419142189009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5967650119054451045837357 2237868794645419142189009)
          ·
            refine ⟨1678401595984064356641757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2237868794645419142189009 1678401595984064356641757)
            ·
              refine ⟨629400598494024133740659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1678401595984064356641757 629400598494024133740659)
              ·
                refine ⟨944100897741036200610989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629400598494024133740659 944100897741036200610989)
                ·
                  refine ⟨354037836652888575229121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944100897741036200610989 354037836652888575229121)
                  ·
                    refine ⟨265528377489666431421841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 354037836652888575229121 265528377489666431421841)
                    ·
                      refine ⟨199146283117249823566381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 265528377489666431421841 199146283117249823566381)
                      ·
                        rfl

theorem cell23_387836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_387836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387836 prefixEnd_387836 := by exact prefixLift 387836
  have htrace : WordTrace (prefixWord ++ tailWord_387836) baseStart_387836 baseEnd_387836 := by
    simpa [prefixWord, tailWord_387836, baseEnd_387836] using wordTrace_append hprefix tailTrace_387836
  have hstable : (prefixWord ++ tailWord_387836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387836).length < 2 ^ (prefixWord ++ tailWord_387836).sum := by decide
  have hdescent : baseEnd_387836 < baseStart_387836 := by decide
  rcases family_descends (prefixWord ++ tailWord_387836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387842 : List Nat := [3, 4, 1, 1, 1, 2, 1, 10]
def baseStart_387842 : Nat := 118140960795 + 387842 * 2 ^ 59
def prefixEnd_387842 : Nat := 4983230072969 + 3 ^ 40 * 387842 * 2
def baseEnd_387842 : Nat := 7375902370413955558939

theorem tailTrace_387842 : CollatzResearch.WordTrace tailWord_387842 prefixEnd_387842 7375902370413955558939 := by
  unfold tailWord_387842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3536439965230536746305445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9430506573948097990147853 3536439965230536746305445)
  ·
    refine ⟨663082493480725639932271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3536439965230536746305445 663082493480725639932271)
    ·
      refine ⟨994623740221088459898407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 663082493480725639932271 994623740221088459898407)
      ·
        refine ⟨1491935610331632689847611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 994623740221088459898407 1491935610331632689847611)
        ·
          refine ⟨2237903415497449034771417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1491935610331632689847611 2237903415497449034771417)
          ·
            refine ⟨1678427561623086776078563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2237903415497449034771417 1678427561623086776078563)
            ·
              refine ⟨2517641342434630164117845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678427561623086776078563 2517641342434630164117845)
              ·
                refine ⟨7375902370413955558939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2517641342434630164117845 7375902370413955558939)
                ·
                  rfl

theorem cell23_387842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 10].length) (baseStart_387842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387842 prefixEnd_387842 := by exact prefixLift 387842
  have htrace : WordTrace (prefixWord ++ tailWord_387842) baseStart_387842 baseEnd_387842 := by
    simpa [prefixWord, tailWord_387842, baseEnd_387842] using wordTrace_append hprefix tailTrace_387842
  have hstable : (prefixWord ++ tailWord_387842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387842).length < 2 ^ (prefixWord ++ tailWord_387842).sum := by decide
  have hdescent : baseEnd_387842 < baseStart_387842 := by decide
  rcases family_descends (prefixWord ++ tailWord_387842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387852 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 1, 3, 3]
def baseStart_387852 : Nat := 118140960795 + 387852 * 2 ^ 59
def prefixEnd_387852 : Nat := 4983230072969 + 3 ^ 40 * 387852 * 2
def baseEnd_387852 : Nat := 199154498807721760966307

theorem tailTrace_387852 : CollatzResearch.WordTrace tailWord_387852 prefixEnd_387852 199154498807721760966307 := by
  unfold tailWord_387852
  simp only [CollatzResearch.WordTrace]
  refine ⟨7073062295442959346542905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9430749727257279128723873 7073062295442959346542905)
  ·
    refine ⟨5304796721582219509907179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7073062295442959346542905 5304796721582219509907179)
    ·
      refine ⟨7957195082373329264860769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5304796721582219509907179 7957195082373329264860769)
      ·
        refine ⟨5967896311779996948645577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7957195082373329264860769 5967896311779996948645577)
        ·
          refine ⟨4475922233834997711484183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5967896311779996948645577 4475922233834997711484183)
          ·
            refine ⟨6713883350752496567226275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475922233834997711484183 6713883350752496567226275)
            ·
              refine ⟨10070825026128744850839413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6713883350752496567226275 10070825026128744850839413)
              ·
                refine ⟨944139846199569829766195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10070825026128744850839413 944139846199569829766195)
                ·
                  refine ⟨1416209769299354744649293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944139846199569829766195 1416209769299354744649293)
                  ·
                    refine ⟨531078663487258029243485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1416209769299354744649293 531078663487258029243485)
                    ·
                      refine ⟨199154498807721760966307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 531078663487258029243485 199154498807721760966307)
                      ·
                        rfl

theorem cell23_387852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_387852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387852 prefixEnd_387852 := by exact prefixLift 387852
  have htrace : WordTrace (prefixWord ++ tailWord_387852) baseStart_387852 baseEnd_387852 := by
    simpa [prefixWord, tailWord_387852, baseEnd_387852] using wordTrace_append hprefix tailTrace_387852
  have hstable : (prefixWord ++ tailWord_387852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387852).length < 2 ^ (prefixWord ++ tailWord_387852).sum := by decide
  have hdescent : baseEnd_387852 < baseStart_387852 := by decide
  rcases family_descends (prefixWord ++ tailWord_387852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387865 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 5]
def baseStart_387865 : Nat := 118140960795 + 387865 * 2 ^ 59
def prefixEnd_387865 : Nat := 4983230072969 + 3 ^ 40 * 387865 * 2
def baseEnd_387865 : Nat := 199161174056230210103747

theorem tailTrace_387865 : CollatzResearch.WordTrace tailWord_387865 prefixEnd_387865 199161174056230210103747 := by
  unfold tailWord_387865
  simp only [CollatzResearch.WordTrace]
  refine ⟨14146598739838821913309049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9431065826559214608872699 14146598739838821913309049)
  ·
    refine ⟨10609949054879116434981787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14146598739838821913309049 10609949054879116434981787)
    ·
      refine ⟨15914923582318674652472681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10609949054879116434981787 15914923582318674652472681)
      ·
        refine ⟨11936192686739005989354511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15914923582318674652472681 11936192686739005989354511)
        ·
          refine ⟨17904289030108508984031767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11936192686739005989354511 17904289030108508984031767)
          ·
            refine ⟨26856433545162763476047651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17904289030108508984031767 26856433545162763476047651)
            ·
              refine ⟨40284650317744145214071477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26856433545162763476047651 40284650317744145214071477)
              ·
                refine ⟨3776685967288513613819201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40284650317744145214071477 3776685967288513613819201)
                ·
                  refine ⟨2832514475466385210364401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3776685967288513613819201 2832514475466385210364401)
                  ·
                    refine ⟨2124385856599788907773301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2832514475466385210364401 2124385856599788907773301)
                    ·
                      refine ⟨199161174056230210103747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2124385856599788907773301 199161174056230210103747)
                      ·
                        rfl

theorem cell23_387865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_387865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387865 prefixEnd_387865 := by exact prefixLift 387865
  have htrace : WordTrace (prefixWord ++ tailWord_387865) baseStart_387865 baseEnd_387865 := by
    simpa [prefixWord, tailWord_387865, baseEnd_387865] using wordTrace_append hprefix tailTrace_387865
  have hstable : (prefixWord ++ tailWord_387865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387865).length < 2 ^ (prefixWord ++ tailWord_387865).sum := by decide
  have hdescent : baseEnd_387865 < baseStart_387865 := by decide
  rcases family_descends (prefixWord ++ tailWord_387865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387912 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_387912 : Nat := 118140960795 + 387912 * 2 ^ 59
def prefixEnd_387912 : Nat := 4983230072969 + 3 ^ 40 * 387912 * 2
def baseEnd_387912 : Nat := 199185307646991526216031

theorem tailTrace_387912 : CollatzResearch.WordTrace tailWord_387912 prefixEnd_387912 199185307646991526216031 := by
  unfold tailWord_387912
  simp only [CollatzResearch.WordTrace]
  refine ⟨7074156485334274470134995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9432208647112365960179993 7074156485334274470134995)
  ·
    refine ⟨10611234728001411705202493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7074156485334274470134995 10611234728001411705202493)
    ·
      refine ⟨3979213023000529389450935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10611234728001411705202493 3979213023000529389450935)
      ·
        refine ⟨5968819534500794084176403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3979213023000529389450935 5968819534500794084176403)
        ·
          refine ⟨8953229301751191126264605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5968819534500794084176403 8953229301751191126264605)
          ·
            refine ⟨3357460988156696672349227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8953229301751191126264605 3357460988156696672349227)
            ·
              refine ⟨5036191482235045008523841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3357460988156696672349227 5036191482235045008523841)
              ·
                refine ⟨3777143611676283756392881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5036191482235045008523841 3777143611676283756392881)
                ·
                  refine ⟨2832857708757212817294661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3777143611676283756392881 2832857708757212817294661)
                  ·
                    refine ⟨531160820391977403242749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2832857708757212817294661 531160820391977403242749)
                    ·
                      refine ⟨199185307646991526216031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 531160820391977403242749 199185307646991526216031)
                      ·
                        rfl

theorem cell23_387912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_387912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387912 prefixEnd_387912 := by exact prefixLift 387912
  have htrace : WordTrace (prefixWord ++ tailWord_387912) baseStart_387912 baseEnd_387912 := by
    simpa [prefixWord, tailWord_387912, baseEnd_387912] using wordTrace_append hprefix tailTrace_387912
  have hstable : (prefixWord ++ tailWord_387912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387912).length < 2 ^ (prefixWord ++ tailWord_387912).sum := by decide
  have hdescent : baseEnd_387912 < baseStart_387912 := by decide
  rcases family_descends (prefixWord ++ tailWord_387912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387922 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_387922 : Nat := 118140960795 + 387922 * 2 ^ 59
def prefixEnd_387922 : Nat := 4983230072969 + 3 ^ 40 * 387922 * 2
def baseEnd_387922 : Nat := 199190442453536487090985

theorem tailTrace_387922 : CollatzResearch.WordTrace tailWord_387922 prefixEnd_387922 199190442453536487090985 := by
  unfold tailWord_387922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3537169425158080162033505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9432451800421547098756013 3537169425158080162033505)
  ·
    refine ⟨2652877068868560121525129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3537169425158080162033505 2652877068868560121525129)
    ·
      refine ⟨1989657801651420091143847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2652877068868560121525129 1989657801651420091143847)
      ·
        refine ⟨2984486702477130136715771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989657801651420091143847 2984486702477130136715771)
        ·
          refine ⟨4476730053715695205073657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984486702477130136715771 4476730053715695205073657)
          ·
            refine ⟨3357547540286771403805243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4476730053715695205073657 3357547540286771403805243)
            ·
              refine ⟨5036321310430157105707865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3357547540286771403805243 5036321310430157105707865)
              ·
                refine ⟨3777240982822617829280899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5036321310430157105707865 3777240982822617829280899)
                ·
                  refine ⟨5665861474233926743921349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777240982822617829280899 5665861474233926743921349)
                  ·
                    refine ⟨1062349026418861264485253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5665861474233926743921349 1062349026418861264485253)
                    ·
                      refine ⟨199190442453536487090985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1062349026418861264485253 199190442453536487090985)
                      ·
                        rfl

theorem cell23_387922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_387922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387922 prefixEnd_387922 := by exact prefixLift 387922
  have htrace : WordTrace (prefixWord ++ tailWord_387922) baseStart_387922 baseEnd_387922 := by
    simpa [prefixWord, tailWord_387922, baseEnd_387922] using wordTrace_append hprefix tailTrace_387922
  have hstable : (prefixWord ++ tailWord_387922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387922).length < 2 ^ (prefixWord ++ tailWord_387922).sum := by decide
  have hdescent : baseEnd_387922 < baseStart_387922 := by decide
  rcases family_descends (prefixWord ++ tailWord_387922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387943 : List Nat := [1, 1, 5, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_387943 : Nat := 118140960795 + 387943 * 2 ^ 59
def prefixEnd_387943 : Nat := 4983230072969 + 3 ^ 40 * 387943 * 2
def baseEnd_387943 : Nat := 199201225547280904928389

theorem tailTrace_387943 : CollatzResearch.WordTrace tailWord_387943 prefixEnd_387943 199201225547280904928389 := by
  unfold tailWord_387943
  simp only [CollatzResearch.WordTrace]
  refine ⟨14149443633556241234648483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9432962422370827489765655 14149443633556241234648483)
  ·
    refine ⟨21224165450334361851972725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14149443633556241234648483 21224165450334361851972725)
    ·
      refine ⟨1989765510968846423622443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21224165450334361851972725 1989765510968846423622443)
      ·
        refine ⟨2984648266453269635433665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989765510968846423622443 2984648266453269635433665)
        ·
          refine ⟨2238486199839952226575249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2984648266453269635433665 2238486199839952226575249)
          ·
            refine ⟨1678864649879964169931437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2238486199839952226575249 1678864649879964169931437)
            ·
              refine ⟨629574243704986563724289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1678864649879964169931437 629574243704986563724289)
              ·
                refine ⟨472180682778739922793217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629574243704986563724289 472180682778739922793217)
                ·
                  refine ⟨354135512084054942094913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472180682778739922793217 354135512084054942094913)
                  ·
                    refine ⟨265601634063041206571185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 354135512084054942094913 265601634063041206571185)
                    ·
                      refine ⟨199201225547280904928389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 265601634063041206571185 199201225547280904928389)
                      ·
                        rfl

theorem cell23_387943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_387943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387943 prefixEnd_387943 := by exact prefixLift 387943
  have htrace : WordTrace (prefixWord ++ tailWord_387943) baseStart_387943 baseEnd_387943 := by
    simpa [prefixWord, tailWord_387943, baseEnd_387943] using wordTrace_append hprefix tailTrace_387943
  have hstable : (prefixWord ++ tailWord_387943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387943).length < 2 ^ (prefixWord ++ tailWord_387943).sum := by decide
  have hdescent : baseEnd_387943 < baseStart_387943 := by decide
  rcases family_descends (prefixWord ++ tailWord_387943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387972 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_387972 : Nat := 118140960795 + 387972 * 2 ^ 59
def prefixEnd_387972 : Nat := 4983230072969 + 3 ^ 40 * 387972 * 2
def baseEnd_387972 : Nat := 199216116486261291465755

theorem tailTrace_387972 : CollatzResearch.WordTrace tailWord_387972 prefixEnd_387972 199216116486261291465755 := by
  unfold tailWord_387972
  simp only [CollatzResearch.WordTrace]
  refine ⟨7075250675225589593727085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9433667566967452791636113 7075250675225589593727085)
  ·
    refine ⟨2653219003209596097647657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7075250675225589593727085 2653219003209596097647657)
    ·
      refine ⟨1989914252407197073235743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2653219003209596097647657 1989914252407197073235743)
      ·
        refine ⟨2984871378610795609853615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989914252407197073235743 2984871378610795609853615)
        ·
          refine ⟨4477307067916193414780423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984871378610795609853615 4477307067916193414780423)
          ·
            refine ⟨6715960601874290122170635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4477307067916193414780423 6715960601874290122170635)
            ·
              refine ⟨10073940902811435183255953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6715960601874290122170635 10073940902811435183255953)
              ·
                refine ⟨7555455677108576387441965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10073940902811435183255953 7555455677108576387441965)
                ·
                  refine ⟨2833295878915716145290737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7555455677108576387441965 2833295878915716145290737)
                  ·
                    refine ⟨2124971909186787108968053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2833295878915716145290737 2124971909186787108968053)
                    ·
                      refine ⟨199216116486261291465755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2124971909186787108968053 199216116486261291465755)
                      ·
                        rfl

theorem cell23_387972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_387972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387972 prefixEnd_387972 := by exact prefixLift 387972
  have htrace : WordTrace (prefixWord ++ tailWord_387972) baseStart_387972 baseEnd_387972 := by
    simpa [prefixWord, tailWord_387972, baseEnd_387972] using wordTrace_append hprefix tailTrace_387972
  have hstable : (prefixWord ++ tailWord_387972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387972).length < 2 ^ (prefixWord ++ tailWord_387972).sum := by decide
  have hdescent : baseEnd_387972 < baseStart_387972 := by decide
  rcases family_descends (prefixWord ++ tailWord_387972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387996 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 2, 5]
def baseStart_387996 : Nat := 118140960795 + 387996 * 2 ^ 59
def prefixEnd_387996 : Nat := 4983230072969 + 3 ^ 40 * 387996 * 2
def baseEnd_387996 : Nat := 66409480007323065855215

theorem tailTrace_387996 : CollatzResearch.WordTrace tailWord_387996 prefixEnd_387996 66409480007323065855215 := by
  unfold tailWord_387996
  simp only [CollatzResearch.WordTrace]
  refine ⟨7075688351182115643163921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9434251134909487524218561 7075688351182115643163921)
  ·
    refine ⟨5306766263386586732372941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7075688351182115643163921 5306766263386586732372941)
    ·
      refine ⟨1990037348769970024639853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5306766263386586732372941 1990037348769970024639853)
      ·
        refine ⟨746264005788738759239945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1990037348769970024639853 746264005788738759239945)
        ·
          refine ⟨559698004341554069429959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746264005788738759239945 559698004341554069429959)
          ·
            refine ⟨839547006512331104144939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559698004341554069429959 839547006512331104144939)
            ·
              refine ⟨1259320509768496656217409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839547006512331104144939 1259320509768496656217409)
              ·
                refine ⟨944490382326372492163057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1259320509768496656217409 944490382326372492163057)
                ·
                  refine ⟨708367786744779369122293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 944490382326372492163057 708367786744779369122293)
                  ·
                    refine ⟨66409480007323065855215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 708367786744779369122293 66409480007323065855215)
                    ·
                      rfl

theorem cell23_387996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_387996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387996 prefixEnd_387996 := by exact prefixLift 387996
  have htrace : WordTrace (prefixWord ++ tailWord_387996) baseStart_387996 baseEnd_387996 := by
    simpa [prefixWord, tailWord_387996, baseEnd_387996] using wordTrace_append hprefix tailTrace_387996
  have hstable : (prefixWord ++ tailWord_387996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387996).length < 2 ^ (prefixWord ++ tailWord_387996).sum := by decide
  have hdescent : baseEnd_387996 < baseStart_387996 := by decide
  rcases family_descends (prefixWord ++ tailWord_387996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387999 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 4]
def baseStart_387999 : Nat := 118140960795 + 387999 * 2 ^ 59
def prefixEnd_387999 : Nat := 4983230072969 + 3 ^ 40 * 387999 * 2
def baseEnd_387999 : Nat := 199229980463932685828131

theorem tailTrace_387999 : CollatzResearch.WordTrace tailWord_387999 prefixEnd_387999 199229980463932685828131 := by
  unfold tailWord_387999
  simp only [CollatzResearch.WordTrace]
  refine ⟨14151486121353362798687051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9434324080902241865791367 14151486121353362798687051)
  ·
    refine ⟨21227229182030044198030577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14151486121353362798687051 21227229182030044198030577)
    ·
      refine ⟨15920421886522533148522933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21227229182030044198030577 15920421886522533148522933)
      ·
        refine ⟨1492539551861487482674025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15920421886522533148522933 1492539551861487482674025)
        ·
          refine ⟨1119404663896115612005519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1492539551861487482674025 1119404663896115612005519)
          ·
            refine ⟨1679106995844173418008279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119404663896115612005519 1679106995844173418008279)
            ·
              refine ⟨2518660493766260127012419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1679106995844173418008279 2518660493766260127012419)
              ·
                refine ⟨3777990740649390190518629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2518660493766260127012419 3777990740649390190518629)
                ·
                  refine ⟨708373263871760660722243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3777990740649390190518629 708373263871760660722243)
                  ·
                    refine ⟨1062559895807640991083365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 708373263871760660722243 1062559895807640991083365)
                    ·
                      refine ⟨199229980463932685828131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1062559895807640991083365 199229980463932685828131)
                      ·
                        rfl

theorem cell23_387999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_387999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_387999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_387999 prefixEnd_387999 := by exact prefixLift 387999
  have htrace : WordTrace (prefixWord ++ tailWord_387999) baseStart_387999 baseEnd_387999 := by
    simpa [prefixWord, tailWord_387999, baseEnd_387999] using wordTrace_append hprefix tailTrace_387999
  have hstable : (prefixWord ++ tailWord_387999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387999).length < 2 ^ (prefixWord ++ tailWord_387999).sum := by decide
  have hdescent : baseEnd_387999 < baseStart_387999 := by decide
  rcases family_descends (prefixWord ++ tailWord_387999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388042 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_388042 : Nat := 118140960795 + 388042 * 2 ^ 59
def prefixEnd_388042 : Nat := 4983230072969 + 3 ^ 40 * 388042 * 2
def baseEnd_388042 : Nat := 199252060132076017590433

theorem tailTrace_388042 : CollatzResearch.WordTrace tailWord_388042 prefixEnd_388042 199252060132076017590433 := by
  unfold tailWord_388042
  simp only [CollatzResearch.WordTrace]
  refine ⟨3538263615049395285625595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9435369640131720761668253 3538263615049395285625595)
  ·
    refine ⟨5307395422574092928438393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3538263615049395285625595 5307395422574092928438393)
    ·
      refine ⟨3980546566930569696328795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5307395422574092928438393 3980546566930569696328795)
      ·
        refine ⟨5970819850395854544493193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3980546566930569696328795 5970819850395854544493193)
        ·
          refine ⟨4478114887796890908369895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5970819850395854544493193 4478114887796890908369895)
          ·
            refine ⟨6717172331695336362554843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4478114887796890908369895 6717172331695336362554843)
            ·
              refine ⟨10075758497543004543832265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6717172331695336362554843 10075758497543004543832265)
              ·
                refine ⟨7556818873157253407874199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10075758497543004543832265 7556818873157253407874199)
                ·
                  refine ⟨11335228309735880111811299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7556818873157253407874199 11335228309735880111811299)
                  ·
                    refine ⟨17002842464603820167716949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11335228309735880111811299 17002842464603820167716949)
                    ·
                      refine ⟨199252060132076017590433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 17002842464603820167716949 199252060132076017590433)
                      ·
                        rfl

theorem cell23_388042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_388042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388042 prefixEnd_388042 := by exact prefixLift 388042
  have htrace : WordTrace (prefixWord ++ tailWord_388042) baseStart_388042 baseEnd_388042 := by
    simpa [prefixWord, tailWord_388042, baseEnd_388042] using wordTrace_append hprefix tailTrace_388042
  have hstable : (prefixWord ++ tailWord_388042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388042).length < 2 ^ (prefixWord ++ tailWord_388042).sum := by decide
  have hdescent : baseEnd_388042 < baseStart_388042 := by decide
  rcases family_descends (prefixWord ++ tailWord_388042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388084 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_388084 : Nat := 118140960795 + 388084 * 2 ^ 59
def prefixEnd_388084 : Nat := 4983230072969 + 3 ^ 40 * 388084 * 2
def baseEnd_388084 : Nat := 199273626319564853265241

theorem tailTrace_388084 : CollatzResearch.WordTrace tailWord_388084 prefixEnd_388084 199273626319564853265241 := by
  unfold tailWord_388084
  simp only [CollatzResearch.WordTrace]
  refine ⟨7077293163022711157765653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9436390884030281543687537 7077293163022711157765653)
  ·
    refine ⟨331748117016689585520265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7077293163022711157765653 331748117016689585520265)
    ·
      refine ⟨248811087762517189140199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331748117016689585520265 248811087762517189140199)
      ·
        refine ⟨373216631643775783710299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248811087762517189140199 373216631643775783710299)
        ·
          refine ⟨559824947465663675565449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373216631643775783710299 559824947465663675565449)
          ·
            refine ⟨419868710599247756674087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559824947465663675565449 419868710599247756674087)
            ·
              refine ⟨629803065898871635011131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419868710599247756674087 629803065898871635011131)
              ·
                refine ⟨944704598848307452516697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629803065898871635011131 944704598848307452516697)
                ·
                  refine ⟨708528449136230589387523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 944704598848307452516697 708528449136230589387523)
                  ·
                    refine ⟨1062792673704345884081285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 708528449136230589387523 1062792673704345884081285)
                    ·
                      refine ⟨199273626319564853265241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1062792673704345884081285 199273626319564853265241)
                      ·
                        rfl

theorem cell23_388084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_388084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388084 prefixEnd_388084 := by exact prefixLift 388084
  have htrace : WordTrace (prefixWord ++ tailWord_388084) baseStart_388084 baseEnd_388084 := by
    simpa [prefixWord, tailWord_388084, baseEnd_388084] using wordTrace_append hprefix tailTrace_388084
  have hstable : (prefixWord ++ tailWord_388084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388084).length < 2 ^ (prefixWord ++ tailWord_388084).sum := by decide
  have hdescent : baseEnd_388084 < baseStart_388084 := by decide
  rcases family_descends (prefixWord ++ tailWord_388084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388086 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_388086 : Nat := 118140960795 + 388086 * 2 ^ 59
def prefixEnd_388086 : Nat := 4983230072969 + 3 ^ 40 * 388086 * 2
def baseEnd_388086 : Nat := 66424884426957948480077

theorem tailTrace_388086 : CollatzResearch.WordTrace tailWord_388086 prefixEnd_388086 66424884426957948480077 := by
  unfold tailWord_388086
  simp only [CollatzResearch.WordTrace]
  refine ⟨884666204502386041069007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9436439514692117771402741 884666204502386041069007)
  ·
    refine ⟨1326999306753579061603511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 884666204502386041069007 1326999306753579061603511)
    ·
      refine ⟨1990498960130368592405267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1326999306753579061603511 1990498960130368592405267)
      ·
        refine ⟨2985748440195552888607901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1990498960130368592405267 2985748440195552888607901)
        ·
          refine ⟨1119655665073332333227963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2985748440195552888607901 1119655665073332333227963)
          ·
            refine ⟨1679483497609998499841945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119655665073332333227963 1679483497609998499841945)
            ·
              refine ⟨1259612623207498874881459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679483497609998499841945 1259612623207498874881459)
              ·
                refine ⟨1889418934811248312322189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259612623207498874881459 1889418934811248312322189)
                ·
                  refine ⟨708532100554218117120821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1889418934811248312322189 708532100554218117120821)
                  ·
                    refine ⟨66424884426957948480077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 708532100554218117120821 66424884426957948480077)
                    ·
                      rfl

theorem cell23_388086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_388086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388086 prefixEnd_388086 := by exact prefixLift 388086
  have htrace : WordTrace (prefixWord ++ tailWord_388086) baseStart_388086 baseEnd_388086 := by
    simpa [prefixWord, tailWord_388086, baseEnd_388086] using wordTrace_append hprefix tailTrace_388086
  have hstable : (prefixWord ++ tailWord_388086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388086).length < 2 ^ (prefixWord ++ tailWord_388086).sum := by decide
  have hdescent : baseEnd_388086 < baseStart_388086 := by decide
  rcases family_descends (prefixWord ++ tailWord_388086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388089 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 3, 1, 4]
def baseStart_388089 : Nat := 118140960795 + 388089 * 2 ^ 59
def prefixEnd_388089 : Nat := 4983230072969 + 3 ^ 40 * 388089 * 2
def baseEnd_388089 : Nat := 199276193722837333702717

theorem tailTrace_388089 : CollatzResearch.WordTrace tailWord_388089 prefixEnd_388089 199276193722837333702717 := by
  unfold tailWord_388089
  simp only [CollatzResearch.WordTrace]
  refine ⟨14154768691027308169463321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9436512460684872112975547 14154768691027308169463321)
  ·
    refine ⟨10616076518270481127097491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14154768691027308169463321 10616076518270481127097491)
    ·
      refine ⟨15924114777405721690646237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10616076518270481127097491 15924114777405721690646237)
      ·
        refine ⟨5971543041527145633992339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15924114777405721690646237 5971543041527145633992339)
        ·
          refine ⟨8957314562290718450988509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5971543041527145633992339 8957314562290718450988509)
          ·
            refine ⟨3358992960859019419120691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8957314562290718450988509 3358992960859019419120691)
            ·
              refine ⟨5038489441288529128681037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3358992960859019419120691 5038489441288529128681037)
              ·
                refine ⟨1889433540483198423255389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5038489441288529128681037 1889433540483198423255389)
                ·
                  refine ⟨708537577681199408720771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1889433540483198423255389 708537577681199408720771)
                  ·
                    refine ⟨1062806366521799113081157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 708537577681199408720771 1062806366521799113081157)
                    ·
                      refine ⟨199276193722837333702717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1062806366521799113081157 199276193722837333702717)
                      ·
                        rfl

theorem cell23_388089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_388089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388089 prefixEnd_388089 := by exact prefixLift 388089
  have htrace : WordTrace (prefixWord ++ tailWord_388089) baseStart_388089 baseEnd_388089 := by
    simpa [prefixWord, tailWord_388089, baseEnd_388089] using wordTrace_append hprefix tailTrace_388089
  have hstable : (prefixWord ++ tailWord_388089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388089).length < 2 ^ (prefixWord ++ tailWord_388089).sum := by decide
  have hdescent : baseEnd_388089 < baseStart_388089 := by decide
  rcases family_descends (prefixWord ++ tailWord_388089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388133 : List Nat := [1, 3, 1, 2, 2, 2, 5, 1, 2, 4]
def baseStart_388133 : Nat := 118140960795 + 388133 * 2 ^ 59
def prefixEnd_388133 : Nat := 4983230072969 + 3 ^ 40 * 388133 * 2
def baseEnd_388133 : Nat := 66432928957211720517505

theorem tailTrace_388133 : CollatzResearch.WordTrace tailWord_388133 prefixEnd_388133 66432928957211720517505 := by
  unfold tailWord_388133
  simp only [CollatzResearch.WordTrace]
  refine ⟨14156373502867903684065053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9437582335245269122710035 14156373502867903684065053)
  ·
    refine ⟨5308640063575463881524395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14156373502867903684065053 5308640063575463881524395)
    ·
      refine ⟨7962960095363195822286593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5308640063575463881524395 7962960095363195822286593)
      ·
        refine ⟨5972220071522396866714945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7962960095363195822286593 5972220071522396866714945)
        ·
          refine ⟨4479165053641797650036209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5972220071522396866714945 4479165053641797650036209)
          ·
            refine ⟨3359373790231348237527157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4479165053641797650036209 3359373790231348237527157)
            ·
              refine ⟨314941292834188897268171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3359373790231348237527157 314941292834188897268171)
              ·
                refine ⟨472411939251283345902257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314941292834188897268171 472411939251283345902257)
                ·
                  refine ⟨354308954438462509426693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472411939251283345902257 354308954438462509426693)
                  ·
                    refine ⟨66432928957211720517505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 354308954438462509426693 66432928957211720517505)
                    ·
                      rfl

theorem cell23_388133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_388133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388133 prefixEnd_388133 := by exact prefixLift 388133
  have htrace : WordTrace (prefixWord ++ tailWord_388133) baseStart_388133 baseEnd_388133 := by
    simpa [prefixWord, tailWord_388133, baseEnd_388133] using wordTrace_append hprefix tailTrace_388133
  have hstable : (prefixWord ++ tailWord_388133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388133).length < 2 ^ (prefixWord ++ tailWord_388133).sum := by decide
  have hdescent : baseEnd_388133 < baseStart_388133 := by decide
  rcases family_descends (prefixWord ++ tailWord_388133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388157 : List Nat := [1, 4, 1, 3, 1, 2, 3, 3, 1, 2, 2]
def baseStart_388157 : Nat := 118140960795 + 388157 * 2 ^ 59
def prefixEnd_388157 : Nat := 4983230072969 + 3 ^ 40 * 388157 * 2
def baseEnd_388157 : Nat := 199311110407343067652405

theorem tailTrace_388157 : CollatzResearch.WordTrace tailWord_388157 prefixEnd_388157 199311110407343067652405 := by
  unfold tailWord_388157
  simp only [CollatzResearch.WordTrace]
  refine ⟨14157248854780955782938725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9438165903187303855292483 14157248854780955782938725)
  ·
    refine ⟨2654484160271429209301011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14157248854780955782938725 2654484160271429209301011)
    ·
      refine ⟨3981726240407143813951517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2654484160271429209301011 3981726240407143813951517)
      ·
        refine ⟨1493147340152678930231819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3981726240407143813951517 1493147340152678930231819)
        ·
          refine ⟨2239721010229018395347729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493147340152678930231819 2239721010229018395347729)
          ·
            refine ⟨1679790757671763796510797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2239721010229018395347729 1679790757671763796510797)
            ·
              refine ⟨629921534126911423691549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1679790757671763796510797 629921534126911423691549)
              ·
                refine ⟨236220575297591783884331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 629921534126911423691549 236220575297591783884331)
                ·
                  refine ⟨354330862946387675826497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236220575297591783884331 354330862946387675826497)
                  ·
                    refine ⟨265748147209790756869873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 354330862946387675826497 265748147209790756869873)
                    ·
                      refine ⟨199311110407343067652405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 265748147209790756869873 199311110407343067652405)
                      ·
                        rfl

theorem cell23_388157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_388157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388157 prefixEnd_388157 := by exact prefixLift 388157
  have htrace : WordTrace (prefixWord ++ tailWord_388157) baseStart_388157 baseEnd_388157 := by
    simpa [prefixWord, tailWord_388157, baseEnd_388157] using wordTrace_append hprefix tailTrace_388157
  have hstable : (prefixWord ++ tailWord_388157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388157).length < 2 ^ (prefixWord ++ tailWord_388157).sum := by decide
  have hdescent : baseEnd_388157 < baseStart_388157 := by decide
  rcases family_descends (prefixWord ++ tailWord_388157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388209 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_388209 : Nat := 118140960795 + 388209 * 2 ^ 59
def prefixEnd_388209 : Nat := 4983230072969 + 3 ^ 40 * 388209 * 2
def baseEnd_388209 : Nat := 199337811401376864202165

theorem tailTrace_388209 : CollatzResearch.WordTrace tailWord_388209 prefixEnd_388209 199337811401376864202165 := by
  unfold tailWord_388209
  simp only [CollatzResearch.WordTrace]
  refine ⟨14159145450592568663831681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9439430300395045775887787 14159145450592568663831681)
  ·
    refine ⟨10619359087944426497873761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14159145450592568663831681 10619359087944426497873761)
    ·
      refine ⟨7964519315958319873405321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10619359087944426497873761 7964519315958319873405321)
      ·
        refine ⟨5973389486968739905053991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7964519315958319873405321 5973389486968739905053991)
        ·
          refine ⟨8960084230453109857580987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5973389486968739905053991 8960084230453109857580987)
          ·
            refine ⟨13440126345679664786371481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8960084230453109857580987 13440126345679664786371481)
            ·
              refine ⟨10080094759259748589778611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13440126345679664786371481 10080094759259748589778611)
              ·
                refine ⟨15120142138889622884667917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10080094759259748589778611 15120142138889622884667917)
                ·
                  refine ⟨5670053302083608581750469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15120142138889622884667917 5670053302083608581750469)
                  ·
                    refine ⟨1063134994140676609078213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5670053302083608581750469 1063134994140676609078213)
                    ·
                      refine ⟨199337811401376864202165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1063134994140676609078213 199337811401376864202165)
                      ·
                        rfl

theorem cell23_388209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_388209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388209 prefixEnd_388209 := by exact prefixLift 388209
  have htrace : WordTrace (prefixWord ++ tailWord_388209) baseStart_388209 baseEnd_388209 := by
    simpa [prefixWord, tailWord_388209, baseEnd_388209] using wordTrace_append hprefix tailTrace_388209
  have hstable : (prefixWord ++ tailWord_388209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388209).length < 2 ^ (prefixWord ++ tailWord_388209).sum := by decide
  have hdescent : baseEnd_388209 < baseStart_388209 := by decide
  rcases family_descends (prefixWord ++ tailWord_388209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388217 : List Nat := [1, 2, 1, 3, 5, 1, 3, 1, 1, 3, 2]
def baseStart_388217 : Nat := 118140960795 + 388217 * 2 ^ 59
def prefixEnd_388217 : Nat := 4983230072969 + 3 ^ 40 * 388217 * 2
def baseEnd_388217 : Nat := 199341919246612832902129

theorem tailTrace_388217 : CollatzResearch.WordTrace tailWord_388217 prefixEnd_388217 199341919246612832902129 := by
  unfold tailWord_388217
  simp only [CollatzResearch.WordTrace]
  refine ⟨14159437234563586030122905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9439624823042390686748603 14159437234563586030122905)
  ·
    refine ⟨10619577925922689522592179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14159437234563586030122905 10619577925922689522592179)
    ·
      refine ⟨15929366888884034283888269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10619577925922689522592179 15929366888884034283888269)
      ·
        refine ⟨5973512583331512856458101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15929366888884034283888269 5973512583331512856458101)
        ·
          refine ⟨560016804687329330292947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5973512583331512856458101 560016804687329330292947)
          ·
            refine ⟨840025207030993995439421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560016804687329330292947 840025207030993995439421)
            ·
              refine ⟨315009452636622748289783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 840025207030993995439421 315009452636622748289783)
              ·
                refine ⟨472514178954934122434675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315009452636622748289783 472514178954934122434675)
                ·
                  refine ⟨708771268432401183652013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472514178954934122434675 708771268432401183652013)
                  ·
                    refine ⟨265789225662150443869505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 708771268432401183652013 265789225662150443869505)
                    ·
                      refine ⟨199341919246612832902129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 265789225662150443869505 199341919246612832902129)
                      ·
                        rfl

theorem cell23_388217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_388217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388217 prefixEnd_388217 := by exact prefixLift 388217
  have htrace : WordTrace (prefixWord ++ tailWord_388217) baseStart_388217 baseEnd_388217 := by
    simpa [prefixWord, tailWord_388217, baseEnd_388217] using wordTrace_append hprefix tailTrace_388217
  have hstable : (prefixWord ++ tailWord_388217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388217).length < 2 ^ (prefixWord ++ tailWord_388217).sum := by decide
  have hdescent : baseEnd_388217 < baseStart_388217 := by decide
  rcases family_descends (prefixWord ++ tailWord_388217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388259 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 7]
def baseStart_388259 : Nat := 118140960795 + 388259 * 2 ^ 59
def prefixEnd_388259 : Nat := 4983230072969 + 3 ^ 40 * 388259 * 2
def baseEnd_388259 : Nat := 199363485434101668576935

theorem tailTrace_388259 : CollatzResearch.WordTrace tailWord_388259 prefixEnd_388259 199363485434101668576935 := by
  unfold tailWord_388259
  simp only [CollatzResearch.WordTrace]
  refine ⟨14160969100411427203151831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9440646066940951468767887 14160969100411427203151831)
  ·
    refine ⟨21241453650617140804727747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14160969100411427203151831 21241453650617140804727747)
    ·
      refine ⟨31862180475925711207091621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21241453650617140804727747 31862180475925711207091621)
      ·
        refine ⟨5974158839236070851329679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31862180475925711207091621 5974158839236070851329679)
        ·
          refine ⟨8961238258854106276994519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5974158839236070851329679 8961238258854106276994519)
          ·
            refine ⟨13441857388281159415491779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8961238258854106276994519 13441857388281159415491779)
            ·
              refine ⟨20162786082421739123237669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13441857388281159415491779 20162786082421739123237669)
              ·
                refine ⟨3780522390454076085607063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20162786082421739123237669 3780522390454076085607063)
                ·
                  refine ⟨5670783585681114128410595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780522390454076085607063 5670783585681114128410595)
                  ·
                    refine ⟨8506175378521671192615893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5670783585681114128410595 8506175378521671192615893)
                    ·
                      refine ⟨199363485434101668576935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8506175378521671192615893 199363485434101668576935)
                      ·
                        rfl

theorem cell23_388259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_388259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388259 prefixEnd_388259 := by exact prefixLift 388259
  have htrace : WordTrace (prefixWord ++ tailWord_388259) baseStart_388259 baseEnd_388259 := by
    simpa [prefixWord, tailWord_388259, baseEnd_388259] using wordTrace_append hprefix tailTrace_388259
  have hstable : (prefixWord ++ tailWord_388259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388259).length < 2 ^ (prefixWord ++ tailWord_388259).sum := by decide
  have hdescent : baseEnd_388259 < baseStart_388259 := by decide
  rcases family_descends (prefixWord ++ tailWord_388259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388380 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_388380 : Nat := 118140960795 + 388380 * 2 ^ 59
def prefixEnd_388380 : Nat := 4983230072969 + 3 ^ 40 * 388380 * 2
def baseEnd_388380 : Nat := 199425616593295695163879

theorem tailTrace_388380 : CollatzResearch.WordTrace tailWord_388380 prefixEnd_388380 199425616593295695163879 := by
  unfold tailWord_388380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7082691166486532434153297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9443588221982043245537729 7082691166486532434153297)
  ·
    refine ⟨5312018374864899325614973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7082691166486532434153297 5312018374864899325614973)
    ·
      refine ⟨1992006890574337247105615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5312018374864899325614973 1992006890574337247105615)
      ·
        refine ⟨2988010335861505870658423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992006890574337247105615 2988010335861505870658423)
        ·
          refine ⟨4482015503792258805987635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988010335861505870658423 4482015503792258805987635)
          ·
            refine ⟨6723023255688388208981453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4482015503792258805987635 6723023255688388208981453)
            ·
              refine ⟨2521133720883145578368045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6723023255688388208981453 2521133720883145578368045)
              ·
                refine ⟨945425145331179591888017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2521133720883145578368045 945425145331179591888017)
                ·
                  refine ⟨709068858998384693916013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 945425145331179591888017 709068858998384693916013)
                  ·
                    refine ⟨265900822124394260218505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 709068858998384693916013 265900822124394260218505)
                    ·
                      refine ⟨199425616593295695163879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 265900822124394260218505 199425616593295695163879)
                      ·
                        rfl

theorem cell23_388380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_388380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388380 prefixEnd_388380 := by exact prefixLift 388380
  have htrace : WordTrace (prefixWord ++ tailWord_388380) baseStart_388380 baseEnd_388380 := by
    simpa [prefixWord, tailWord_388380, baseEnd_388380] using wordTrace_append hprefix tailTrace_388380
  have hstable : (prefixWord ++ tailWord_388380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388380).length < 2 ^ (prefixWord ++ tailWord_388380).sum := by decide
  have hdescent : baseEnd_388380 < baseStart_388380 := by decide
  rcases family_descends (prefixWord ++ tailWord_388380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388404 : List Nat := [2, 5, 1, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_388404 : Nat := 118140960795 + 388404 * 2 ^ 59
def prefixEnd_388404 : Nat := 4983230072969 + 3 ^ 40 * 388404 * 2
def baseEnd_388404 : Nat := 199437940129003601263769

theorem tailTrace_388404 : CollatzResearch.WordTrace tailWord_388404 prefixEnd_388404 199437940129003601263769 := by
  unfold tailWord_388404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7083128842443058483590133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9444171789924077978120177 7083128842443058483590133)
  ·
    refine ⟨664043328979036732836575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7083128842443058483590133 664043328979036732836575)
    ·
      refine ⟨996064993468555099254863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 664043328979036732836575 996064993468555099254863)
      ·
        refine ⟨1494097490202832648882295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996064993468555099254863 1494097490202832648882295)
        ·
          refine ⟨2241146235304248973323443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494097490202832648882295 2241146235304248973323443)
          ·
            refine ⟨3361719352956373459985165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2241146235304248973323443 3361719352956373459985165)
            ·
              refine ⟨1260644757358640047494437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3361719352956373459985165 1260644757358640047494437)
              ·
                refine ⟨236370892004745008905207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1260644757358640047494437 236370892004745008905207)
                ·
                  refine ⟨354556338007117513357811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236370892004745008905207 354556338007117513357811)
                  ·
                    refine ⟨531834507010676270036717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 354556338007117513357811 531834507010676270036717)
                    ·
                      refine ⟨199437940129003601263769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 531834507010676270036717 199437940129003601263769)
                      ·
                        rfl

theorem cell23_388404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_388404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388404 prefixEnd_388404 := by exact prefixLift 388404
  have htrace : WordTrace (prefixWord ++ tailWord_388404) baseStart_388404 baseEnd_388404 := by
    simpa [prefixWord, tailWord_388404, baseEnd_388404] using wordTrace_append hprefix tailTrace_388404
  have hstable : (prefixWord ++ tailWord_388404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388404).length < 2 ^ (prefixWord ++ tailWord_388404).sum := by decide
  have hdescent : baseEnd_388404 < baseStart_388404 := by decide
  rcases family_descends (prefixWord ++ tailWord_388404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388420 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_388420 : Nat := 118140960795 + 388420 * 2 ^ 59
def prefixEnd_388420 : Nat := 4983230072969 + 3 ^ 40 * 388420 * 2
def baseEnd_388420 : Nat := 66482051939825179554565

theorem tailTrace_388420 : CollatzResearch.WordTrace tailWord_388420 prefixEnd_388420 66482051939825179554565 := by
  unfold tailWord_388420
  simp only [CollatzResearch.WordTrace]
  refine ⟨7083420626414075849881357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9444560835218767799841809 7083420626414075849881357)
  ·
    refine ⟨2656282734905278443705509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7083420626414075849881357 2656282734905278443705509)
    ·
      refine ⟨498053012794739708194783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2656282734905278443705509 498053012794739708194783)
      ·
        refine ⟨747079519192109562292175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498053012794739708194783 747079519192109562292175)
        ·
          refine ⟨1120619278788164343438263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747079519192109562292175 1120619278788164343438263)
          ·
            refine ⟨1680928918182246515157395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120619278788164343438263 1680928918182246515157395)
            ·
              refine ⟨2521393377273369772736093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680928918182246515157395 2521393377273369772736093)
              ·
                refine ⟨945522516477513664776035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2521393377273369772736093 945522516477513664776035)
                ·
                  refine ⟨1418283774716270497164053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945522516477513664776035 1418283774716270497164053)
                  ·
                    refine ⟨66482051939825179554565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1418283774716270497164053 66482051939825179554565)
                    ·
                      rfl

theorem cell23_388420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_388420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388420 prefixEnd_388420 := by exact prefixLift 388420
  have htrace : WordTrace (prefixWord ++ tailWord_388420) baseStart_388420 baseEnd_388420 := by
    simpa [prefixWord, tailWord_388420, baseEnd_388420] using wordTrace_append hprefix tailTrace_388420
  have hstable : (prefixWord ++ tailWord_388420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388420).length < 2 ^ (prefixWord ++ tailWord_388420).sum := by decide
  have hdescent : baseEnd_388420 < baseStart_388420 := by decide
  rcases family_descends (prefixWord ++ tailWord_388420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388423 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_388423 : Nat := 118140960795 + 388423 * 2 ^ 59
def prefixEnd_388423 : Nat := 4983230072969 + 3 ^ 40 * 388423 * 2
def baseEnd_388423 : Nat := 199447696261439026926181

theorem tailTrace_388423 : CollatzResearch.WordTrace tailWord_388423 prefixEnd_388423 199447696261439026926181 := by
  unfold tailWord_388423
  simp only [CollatzResearch.WordTrace]
  refine ⟨14166950671817283212121923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9444633781211522141414615 14166950671817283212121923)
  ·
    refine ⟨21250426007725924818182885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14166950671817283212121923 21250426007725924818182885)
    ·
      refine ⟨3984454876448610903409291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21250426007725924818182885 3984454876448610903409291)
      ·
        refine ⟨5976682314672916355113937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3984454876448610903409291 5976682314672916355113937)
        ·
          refine ⟨4482511736004687266335453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5976682314672916355113937 4482511736004687266335453)
          ·
            refine ⟨1680941901001757724875795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4482511736004687266335453 1680941901001757724875795)
            ·
              refine ⟨2521412851502636587313693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680941901001757724875795 2521412851502636587313693)
              ·
                refine ⟨945529819313488720242635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2521412851502636587313693 945529819313488720242635)
                ·
                  refine ⟨1418294728970233080363953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945529819313488720242635 1418294728970233080363953)
                  ·
                    refine ⟨1063721046727674810272965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1418294728970233080363953 1063721046727674810272965)
                    ·
                      refine ⟨199447696261439026926181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1063721046727674810272965 199447696261439026926181)
                      ·
                        rfl

theorem cell23_388423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_388423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388423 prefixEnd_388423 := by exact prefixLift 388423
  have htrace : WordTrace (prefixWord ++ tailWord_388423) baseStart_388423 baseEnd_388423 := by
    simpa [prefixWord, tailWord_388423, baseEnd_388423] using wordTrace_append hprefix tailTrace_388423
  have hstable : (prefixWord ++ tailWord_388423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388423).length < 2 ^ (prefixWord ++ tailWord_388423).sum := by decide
  have hdescent : baseEnd_388423 < baseStart_388423 := by decide
  rcases family_descends (prefixWord ++ tailWord_388423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388426 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_388426 : Nat := 118140960795 + 388426 * 2 ^ 59
def prefixEnd_388426 : Nat := 4983230072969 + 3 ^ 40 * 388426 * 2
def baseEnd_388426 : Nat := 199449236703402515188667

theorem tailTrace_388426 : CollatzResearch.WordTrace tailWord_388426 prefixEnd_388426 199449236703402515188667 := by
  unfold tailWord_388426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3541765022701603681120283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9444706727204276482987421 3541765022701603681120283)
  ·
    refine ⟨5312647534052405521680425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3541765022701603681120283 5312647534052405521680425)
    ·
      refine ⟨3984485650539304141260319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5312647534052405521680425 3984485650539304141260319)
      ·
        refine ⟨5976728475808956211890479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3984485650539304141260319 5976728475808956211890479)
        ·
          refine ⟨8965092713713434317835719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5976728475808956211890479 8965092713713434317835719)
          ·
            refine ⟨13447639070570151476753579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8965092713713434317835719 13447639070570151476753579)
            ·
              refine ⟨20171458605855227215130369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13447639070570151476753579 20171458605855227215130369)
              ·
                refine ⟨15128593954391420411347777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20171458605855227215130369 15128593954391420411347777)
                ·
                  refine ⟨11346445465793565308510833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15128593954391420411347777 11346445465793565308510833)
                  ·
                    refine ⟨8509834099345173981383125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11346445465793565308510833 8509834099345173981383125)
                    ·
                      refine ⟨199449236703402515188667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8509834099345173981383125 199449236703402515188667)
                      ·
                        rfl

theorem cell23_388426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_388426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388426 prefixEnd_388426 := by exact prefixLift 388426
  have htrace : WordTrace (prefixWord ++ tailWord_388426) baseStart_388426 baseEnd_388426 := by
    simpa [prefixWord, tailWord_388426, baseEnd_388426] using wordTrace_append hprefix tailTrace_388426
  have hstable : (prefixWord ++ tailWord_388426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388426).length < 2 ^ (prefixWord ++ tailWord_388426).sum := by decide
  have hdescent : baseEnd_388426 < baseStart_388426 := by decide
  rcases family_descends (prefixWord ++ tailWord_388426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388430 : List Nat := [4, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_388430 : Nat := 118140960795 + 388430 * 2 ^ 59
def prefixEnd_388430 : Nat := 4983230072969 + 3 ^ 40 * 388430 * 2
def baseEnd_388430 : Nat := 199451290626020499538649

theorem tailTrace_388430 : CollatzResearch.WordTrace tailWord_388430 prefixEnd_388430 199451290626020499538649 := by
  unfold tailWord_388430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770900747848990425953343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9444803988527948938417829 1770900747848990425953343)
  ·
    refine ⟨2656351121773485638930015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1770900747848990425953343 2656351121773485638930015)
    ·
      refine ⟨3984526682660228458395023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2656351121773485638930015 3984526682660228458395023)
      ·
        refine ⟨5976790023990342687592535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3984526682660228458395023 5976790023990342687592535)
        ·
          refine ⟨8965185035985514031388803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5976790023990342687592535 8965185035985514031388803)
          ·
            refine ⟨13447777553978271047083205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8965185035985514031388803 13447777553978271047083205)
            ·
              refine ⟨2521458291370925821328101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13447777553978271047083205 2521458291370925821328101)
              ·
                refine ⟨472773429632048591499019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2521458291370925821328101 472773429632048591499019)
                ·
                  refine ⟨709160144448072887248529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472773429632048591499019 709160144448072887248529)
                  ·
                    refine ⟨531870108336054665436397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 709160144448072887248529 531870108336054665436397)
                    ·
                      refine ⟨199451290626020499538649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 531870108336054665436397 199451290626020499538649)
                      ·
                        rfl

theorem cell23_388430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_388430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388430 prefixEnd_388430 := by exact prefixLift 388430
  have htrace : WordTrace (prefixWord ++ tailWord_388430) baseStart_388430 baseEnd_388430 := by
    simpa [prefixWord, tailWord_388430, baseEnd_388430] using wordTrace_append hprefix tailTrace_388430
  have hstable : (prefixWord ++ tailWord_388430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388430).length < 2 ^ (prefixWord ++ tailWord_388430).sum := by decide
  have hdescent : baseEnd_388430 < baseStart_388430 := by decide
  rcases family_descends (prefixWord ++ tailWord_388430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388433 : List Nat := [1, 2, 2, 1, 4, 1, 5, 7]
def baseStart_388433 : Nat := 118140960795 + 388433 * 2 ^ 59
def prefixEnd_388433 : Nat := 4983230072969 + 3 ^ 40 * 388433 * 2
def baseEnd_388433 : Nat := 7387141891406814363005

theorem tailTrace_388433 : CollatzResearch.WordTrace tailWord_388433 prefixEnd_388433 7387141891406814363005 := by
  unfold tailWord_388433
  simp only [CollatzResearch.WordTrace]
  refine ⟨14167315401781054919985953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9444876934520703279990635 14167315401781054919985953)
  ·
    refine ⟨10625486551335791189989465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14167315401781054919985953 10625486551335791189989465)
    ·
      refine ⟨7969114913501843392492099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10625486551335791189989465 7969114913501843392492099)
      ·
        refine ⟨11953672370252765088738149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7969114913501843392492099 11953672370252765088738149)
        ·
          refine ⟨2241313569422393454138403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11953672370252765088738149 2241313569422393454138403)
          ·
            refine ⟨3361970354133590181207605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2241313569422393454138403 3361970354133590181207605)
            ·
              refine ⟨315184720700024079488213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3361970354133590181207605 315184720700024079488213)
              ·
                refine ⟨7387141891406814363005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 315184720700024079488213 7387141891406814363005)
                ·
                  rfl

theorem cell23_388433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 7].length) (baseStart_388433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388433 prefixEnd_388433 := by exact prefixLift 388433
  have htrace : WordTrace (prefixWord ++ tailWord_388433) baseStart_388433 baseEnd_388433 := by
    simpa [prefixWord, tailWord_388433, baseEnd_388433] using wordTrace_append hprefix tailTrace_388433
  have hstable : (prefixWord ++ tailWord_388433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388433).length < 2 ^ (prefixWord ++ tailWord_388433).sum := by decide
  have hdescent : baseEnd_388433 < baseStart_388433 := by decide
  rcases family_descends (prefixWord ++ tailWord_388433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388487 : List Nat := [1, 1, 4, 2, 2, 2, 1, 4, 1, 3, 2]
def baseStart_388487 : Nat := 118140960795 + 388487 * 2 ^ 59
def prefixEnd_388487 : Nat := 4983230072969 + 3 ^ 40 * 388487 * 2
def baseEnd_388487 : Nat := 199480559023326776525887

theorem tailTrace_388487 : CollatzResearch.WordTrace tailWord_388487 prefixEnd_388487 199480559023326776525887 := by
  unfold tailWord_388487
  simp only [CollatzResearch.WordTrace]
  refine ⟨14169284943585422142451715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9446189962390281428301143 14169284943585422142451715)
  ·
    refine ⟨21253927415378133213677573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14169284943585422142451715 21253927415378133213677573)
    ·
      refine ⟨3985111390383399977564545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21253927415378133213677573 3985111390383399977564545)
      ·
        refine ⟨2988833542787549983173409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3985111390383399977564545 2988833542787549983173409)
        ·
          refine ⟨2241625157090662487380057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2988833542787549983173409 2241625157090662487380057)
          ·
            refine ⟨1681218867817996865535043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2241625157090662487380057 1681218867817996865535043)
            ·
              refine ⟨2521828301726995298302565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681218867817996865535043 2521828301726995298302565)
              ·
                refine ⟨472842806573811618431731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2521828301726995298302565 472842806573811618431731)
                ·
                  refine ⟨709264209860717427647597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472842806573811618431731 709264209860717427647597)
                  ·
                    refine ⟨265974078697769035367849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 709264209860717427647597 265974078697769035367849)
                    ·
                      refine ⟨199480559023326776525887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 265974078697769035367849 199480559023326776525887)
                      ·
                        rfl

theorem cell23_388487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_388487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388487 prefixEnd_388487 := by exact prefixLift 388487
  have htrace : WordTrace (prefixWord ++ tailWord_388487) baseStart_388487 baseEnd_388487 := by
    simpa [prefixWord, tailWord_388487, baseEnd_388487] using wordTrace_append hprefix tailTrace_388487
  have hstable : (prefixWord ++ tailWord_388487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388487).length < 2 ^ (prefixWord ++ tailWord_388487).sum := by decide
  have hdescent : baseEnd_388487 < baseStart_388487 := by decide
  rcases family_descends (prefixWord ++ tailWord_388487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388503 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 3]
def baseStart_388503 : Nat := 118140960795 + 388503 * 2 ^ 59
def prefixEnd_388503 : Nat := 4983230072969 + 3 ^ 40 * 388503 * 2
def baseEnd_388503 : Nat := 199488774713798713925813

theorem tailTrace_388503 : CollatzResearch.WordTrace tailWord_388503 prefixEnd_388503 199488774713798713925813 := by
  unfold tailWord_388503
  simp only [CollatzResearch.WordTrace]
  refine ⟨14169868511527456875034163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9446579007684971250022775 14169868511527456875034163)
  ·
    refine ⟨21254802767291185312551245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14169868511527456875034163 21254802767291185312551245)
    ·
      refine ⟨7970551037734194492206717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21254802767291185312551245 7970551037734194492206717)
      ·
        refine ⟨2988956639150322934577519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7970551037734194492206717 2988956639150322934577519)
        ·
          refine ⟨4483434958725484401866279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988956639150322934577519 4483434958725484401866279)
          ·
            refine ⟨6725152438088226602799419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4483434958725484401866279 6725152438088226602799419)
            ·
              refine ⟨10087728657132339904199129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6725152438088226602799419 10087728657132339904199129)
              ·
                refine ⟨7565796492849254928149347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10087728657132339904199129 7565796492849254928149347)
                ·
                  refine ⟨11348694739273882392224021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7565796492849254928149347 11348694739273882392224021)
                  ·
                    refine ⟨531970065903463237135501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11348694739273882392224021 531970065903463237135501)
                    ·
                      refine ⟨199488774713798713925813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 531970065903463237135501 199488774713798713925813)
                      ·
                        rfl

theorem cell23_388503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_388503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388503 prefixEnd_388503 := by exact prefixLift 388503
  have htrace : WordTrace (prefixWord ++ tailWord_388503) baseStart_388503 baseEnd_388503 := by
    simpa [prefixWord, tailWord_388503, baseEnd_388503] using wordTrace_append hprefix tailTrace_388503
  have hstable : (prefixWord ++ tailWord_388503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388503).length < 2 ^ (prefixWord ++ tailWord_388503).sum := by decide
  have hdescent : baseEnd_388503 < baseStart_388503 := by decide
  rcases family_descends (prefixWord ++ tailWord_388503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388570 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 2, 5]
def baseStart_388570 : Nat := 118140960795 + 388570 * 2 ^ 59
def prefixEnd_388570 : Nat := 4983230072969 + 3 ^ 40 * 388570 * 2
def baseEnd_388570 : Nat := 66507725972549983929335

theorem tailTrace_388570 : CollatzResearch.WordTrace tailWord_388570 prefixEnd_388570 66507725972549983929335 := by
  unfold tailWord_388570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3543078050571181829430791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9448208134856484878482109 3543078050571181829430791)
  ·
    refine ⟨5314617075856772744146187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3543078050571181829430791 5314617075856772744146187)
    ·
      refine ⟨7971925613785159116219281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5314617075856772744146187 7971925613785159116219281)
      ·
        refine ⟨5978944210338869337164461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7971925613785159116219281 5978944210338869337164461)
        ·
          refine ⟨2242104078877076001436673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5978944210338869337164461 2242104078877076001436673)
          ·
            refine ⟨1681578059157807001077505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2242104078877076001436673 1681578059157807001077505)
            ·
              refine ⟨1261183544368355250808129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681578059157807001077505 1261183544368355250808129)
              ·
                refine ⟨945887658276266438106097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261183544368355250808129 945887658276266438106097)
                ·
                  refine ⟨709415743707199828579573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 945887658276266438106097 709415743707199828579573)
                  ·
                    refine ⟨66507725972549983929335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 709415743707199828579573 66507725972549983929335)
                    ·
                      rfl

theorem cell23_388570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_388570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388570 prefixEnd_388570 := by exact prefixLift 388570
  have htrace : WordTrace (prefixWord ++ tailWord_388570) baseStart_388570 baseEnd_388570 := by
    simpa [prefixWord, tailWord_388570, baseEnd_388570] using wordTrace_append hprefix tailTrace_388570
  have hstable : (prefixWord ++ tailWord_388570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388570).length < 2 ^ (prefixWord ++ tailWord_388570).sum := by decide
  have hdescent : baseEnd_388570 < baseStart_388570 := by decide
  rcases family_descends (prefixWord ++ tailWord_388570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388590 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_388590 : Nat := 118140960795 + 388590 * 2 ^ 59
def prefixEnd_388590 : Nat := 4983230072969 + 3 ^ 40 * 388590 * 2
def baseEnd_388590 : Nat := 199533447530739873537913

theorem tailTrace_388590 : CollatzResearch.WordTrace tailWord_388590 prefixEnd_388590 199533447530739873537913 := by
  unfold tailWord_388590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771630207776533841681403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9448694441474847155634149 1771630207776533841681403)
  ·
    refine ⟨2657445311664800762522105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1771630207776533841681403 2657445311664800762522105)
    ·
      refine ⟨1993083983748600571891579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2657445311664800762522105 1993083983748600571891579)
      ·
        refine ⟨2989625975622900857837369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993083983748600571891579 2989625975622900857837369)
        ·
          refine ⟨2242219481717175643378027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2989625975622900857837369 2242219481717175643378027)
          ·
            refine ⟨3363329222575763465067041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242219481717175643378027 3363329222575763465067041)
            ·
              refine ⟨2522496916931822598800281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3363329222575763465067041 2522496916931822598800281)
              ·
                refine ⟨1891872687698866949100211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2522496916931822598800281 1891872687698866949100211)
                ·
                  refine ⟨2837809031548300423650317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891872687698866949100211 2837809031548300423650317)
                  ·
                    refine ⟨1064178386830612658868869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2837809031548300423650317 1064178386830612658868869)
                    ·
                      refine ⟨199533447530739873537913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1064178386830612658868869 199533447530739873537913)
                      ·
                        rfl

theorem cell23_388590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_388590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388590 prefixEnd_388590 := by exact prefixLift 388590
  have htrace : WordTrace (prefixWord ++ tailWord_388590) baseStart_388590 baseEnd_388590 := by
    simpa [prefixWord, tailWord_388590, baseEnd_388590] using wordTrace_append hprefix tailTrace_388590
  have hstable : (prefixWord ++ tailWord_388590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388590).length < 2 ^ (prefixWord ++ tailWord_388590).sum := by decide
  have hdescent : baseEnd_388590 < baseStart_388590 := by decide
  rcases family_descends (prefixWord ++ tailWord_388590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388600 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 5, 4]
def baseStart_388600 : Nat := 118140960795 + 388600 * 2 ^ 59
def prefixEnd_388600 : Nat := 4983230072969 + 3 ^ 40 * 388600 * 2
def baseEnd_388600 : Nat := 66512860779094944804289

theorem tailTrace_388600 : CollatzResearch.WordTrace tailWord_388600 prefixEnd_388600 66512860779094944804289 := by
  unfold tailWord_388600
  simp only [CollatzResearch.WordTrace]
  refine ⟨7086703196088021220657627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9448937594784028294210169 7086703196088021220657627)
  ·
    refine ⟨10630054794132031830986441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7086703196088021220657627 10630054794132031830986441)
    ·
      refine ⟨7972541095599023873239831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10630054794132031830986441 7972541095599023873239831)
      ·
        refine ⟨11958811643398535809859747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7972541095599023873239831 11958811643398535809859747)
        ·
          refine ⟨17938217465097803714789621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11958811643398535809859747 17938217465097803714789621)
          ·
            refine ⟨1681707887352919098261527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17938217465097803714789621 1681707887352919098261527)
            ·
              refine ⟨2522561831029378647392291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681707887352919098261527 2522561831029378647392291)
              ·
                refine ⟨3783842746544067971088437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2522561831029378647392291 3783842746544067971088437)
                ·
                  refine ⟨354735257488506372289541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3783842746544067971088437 354735257488506372289541)
                  ·
                    refine ⟨66512860779094944804289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 354735257488506372289541 66512860779094944804289)
                    ·
                      rfl

theorem cell23_388600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_388600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388600 prefixEnd_388600 := by exact prefixLift 388600
  have htrace : WordTrace (prefixWord ++ tailWord_388600) baseStart_388600 baseEnd_388600 := by
    simpa [prefixWord, tailWord_388600, baseEnd_388600] using wordTrace_append hprefix tailTrace_388600
  have hstable : (prefixWord ++ tailWord_388600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388600).length < 2 ^ (prefixWord ++ tailWord_388600).sum := by decide
  have hdescent : baseEnd_388600 < baseStart_388600 := by decide
  rcases family_descends (prefixWord ++ tailWord_388600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388603 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 4]
def baseStart_388603 : Nat := 118140960795 + 388603 * 2 ^ 59
def prefixEnd_388603 : Nat := 4983230072969 + 3 ^ 40 * 388603 * 2
def baseEnd_388603 : Nat := 199540122779248322675353

theorem tailTrace_388603 : CollatzResearch.WordTrace tailWord_388603 prefixEnd_388603 199540122779248322675353 := by
  unfold tailWord_388603
  simp only [CollatzResearch.WordTrace]
  refine ⟨14173515811165173953674463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9449010540776782635782975 14173515811165173953674463)
  ·
    refine ⟨21260273716747760930511695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14173515811165173953674463 21260273716747760930511695)
    ·
      refine ⟨31890410575121641395767543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21260273716747760930511695 31890410575121641395767543)
      ·
        refine ⟨47835615862682462093651315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31890410575121641395767543 47835615862682462093651315)
        ·
          refine ⟨71753423794023693140476973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47835615862682462093651315 71753423794023693140476973)
          ·
            refine ⟨26907533922758884927678865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71753423794023693140476973 26907533922758884927678865)
            ·
              refine ⟨20180650442069163695759149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26907533922758884927678865 20180650442069163695759149)
              ·
                refine ⟨7567743915775936385909681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20180650442069163695759149 7567743915775936385909681)
                ·
                  refine ⟨5675807936831952289432261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7567743915775936385909681 5675807936831952289432261)
                  ·
                    refine ⟨1064213988155991054268549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5675807936831952289432261 1064213988155991054268549)
                    ·
                      refine ⟨199540122779248322675353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1064213988155991054268549 199540122779248322675353)
                      ·
                        rfl

theorem cell23_388603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 4].length) (baseStart_388603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388603 prefixEnd_388603 := by exact prefixLift 388603
  have htrace : WordTrace (prefixWord ++ tailWord_388603) baseStart_388603 baseEnd_388603 := by
    simpa [prefixWord, tailWord_388603, baseEnd_388603] using wordTrace_append hprefix tailTrace_388603
  have hstable : (prefixWord ++ tailWord_388603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388603).length < 2 ^ (prefixWord ++ tailWord_388603).sum := by decide
  have hdescent : baseEnd_388603 < baseStart_388603 := by decide
  rcases family_descends (prefixWord ++ tailWord_388603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388613 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 8]
def baseStart_388613 : Nat := 118140960795 + 388613 * 2 ^ 59
def prefixEnd_388613 : Nat := 4983230072969 + 3 ^ 40 * 388613 * 2
def baseEnd_388613 : Nat := 22171695287310364838923

theorem tailTrace_388613 : CollatzResearch.WordTrace tailWord_388613 prefixEnd_388613 22171695287310364838923 := by
  unfold tailWord_388613
  simp only [CollatzResearch.WordTrace]
  refine ⟨14173880541128945661538493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9449253694085963774358995 14173880541128945661538493)
  ·
    refine ⟨5315205202923354623076935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14173880541128945661538493 5315205202923354623076935)
    ·
      refine ⟨7972807804385031934615403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5315205202923354623076935 7972807804385031934615403)
      ·
        refine ⟨11959211706577547901923105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7972807804385031934615403 11959211706577547901923105)
        ·
          refine ⟨8969408779933160926442329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11959211706577547901923105 8969408779933160926442329)
          ·
            refine ⟨6727056584949870694831747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8969408779933160926442329 6727056584949870694831747)
            ·
              refine ⟨10090584877424806042247621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727056584949870694831747 10090584877424806042247621)
              ·
                refine ⟨1891984664517151132921429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10090584877424806042247621 1891984664517151132921429)
                ·
                  refine ⟨22171695287310364838923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1891984664517151132921429 22171695287310364838923)
                  ·
                    rfl

theorem cell23_388613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_388613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388613 prefixEnd_388613 := by exact prefixLift 388613
  have htrace : WordTrace (prefixWord ++ tailWord_388613) baseStart_388613 baseEnd_388613 := by
    simpa [prefixWord, tailWord_388613, baseEnd_388613] using wordTrace_append hprefix tailTrace_388613
  have hstable : (prefixWord ++ tailWord_388613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388613).length < 2 ^ (prefixWord ++ tailWord_388613).sum := by decide
  have hdescent : baseEnd_388613 < baseStart_388613 := by decide
  rcases family_descends (prefixWord ++ tailWord_388613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388650 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_388650 : Nat := 118140960795 + 388650 * 2 ^ 59
def prefixEnd_388650 : Nat := 4983230072969 + 3 ^ 40 * 388650 * 2
def baseEnd_388650 : Nat := 199564256370009638787637

theorem tailTrace_388650 : CollatzResearch.WordTrace tailWord_388650 prefixEnd_388650 199564256370009638787637 := by
  unfold tailWord_388650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3543807510498725245158851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9450153361329933987090269 3543807510498725245158851)
  ·
    refine ⟨5315711265748087867738277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3543807510498725245158851 5315711265748087867738277)
    ·
      refine ⟨996695862327766475200927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5315711265748087867738277 996695862327766475200927)
      ·
        refine ⟨1495043793491649712801391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996695862327766475200927 1495043793491649712801391)
        ·
          refine ⟨2242565690237474569202087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495043793491649712801391 2242565690237474569202087)
          ·
            refine ⟨3363848535356211853803131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242565690237474569202087 3363848535356211853803131)
            ·
              refine ⟨5045772803034317780704697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363848535356211853803131 5045772803034317780704697)
              ·
                refine ⟨3784329602275738335528523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045772803034317780704697 3784329602275738335528523)
                ·
                  refine ⟨5676494403413607503292785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784329602275738335528523 5676494403413607503292785)
                  ·
                    refine ⟨4257370802560205627469589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5676494403413607503292785 4257370802560205627469589)
                    ·
                      refine ⟨199564256370009638787637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4257370802560205627469589 199564256370009638787637)
                      ·
                        rfl

theorem cell23_388650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_388650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388650 prefixEnd_388650 := by exact prefixLift 388650
  have htrace : WordTrace (prefixWord ++ tailWord_388650) baseStart_388650 baseEnd_388650 := by
    simpa [prefixWord, tailWord_388650, baseEnd_388650] using wordTrace_append hprefix tailTrace_388650
  have hstable : (prefixWord ++ tailWord_388650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388650).length < 2 ^ (prefixWord ++ tailWord_388650).sum := by decide
  have hdescent : baseEnd_388650 < baseStart_388650 := by decide
  rcases family_descends (prefixWord ++ tailWord_388650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388668 : List Nat := [2, 2, 2, 2, 5, 1, 1, 3, 1, 4]
def baseStart_388668 : Nat := 118140960795 + 388668 * 2 ^ 59
def prefixEnd_388668 : Nat := 4983230072969 + 3 ^ 40 * 388668 * 2
def baseEnd_388668 : Nat := 66524499673930189454185

theorem tailTrace_388668 : CollatzResearch.WordTrace tailWord_388668 prefixEnd_388668 66524499673930189454185 := by
  unfold tailWord_388668
  simp only [CollatzResearch.WordTrace]
  refine ⟨7087943277964845027395329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9450591037286460036527105 7087943277964845027395329)
  ·
    refine ⟨5315957458473633770546497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7087943277964845027395329 5315957458473633770546497)
    ·
      refine ⟨3986968093855225327909873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5315957458473633770546497 3986968093855225327909873)
      ·
        refine ⟨2990226070391418995932405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3986968093855225327909873 2990226070391418995932405)
        ·
          refine ⟨280333694099195530868663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2990226070391418995932405 280333694099195530868663)
          ·
            refine ⟨420500541148793296302995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280333694099195530868663 420500541148793296302995)
            ·
              refine ⟨630750811723189944454493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420500541148793296302995 630750811723189944454493)
              ·
                refine ⟨236531554396196229170435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 630750811723189944454493 236531554396196229170435)
                ·
                  refine ⟨354797331594294343755653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236531554396196229170435 354797331594294343755653)
                  ·
                    refine ⟨66524499673930189454185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 354797331594294343755653 66524499673930189454185)
                    ·
                      rfl

theorem cell23_388668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_388668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388668 prefixEnd_388668 := by exact prefixLift 388668
  have htrace : WordTrace (prefixWord ++ tailWord_388668) baseStart_388668 baseEnd_388668 := by
    simpa [prefixWord, tailWord_388668, baseEnd_388668] using wordTrace_append hprefix tailTrace_388668
  have hstable : (prefixWord ++ tailWord_388668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388668).length < 2 ^ (prefixWord ++ tailWord_388668).sum := by decide
  have hdescent : baseEnd_388668 < baseStart_388668 := by decide
  rcases family_descends (prefixWord ++ tailWord_388668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388680 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_388680 : Nat := 118140960795 + 388680 * 2 ^ 59
def prefixEnd_388680 : Nat := 4983230072969 + 3 ^ 40 * 388680 * 2
def baseEnd_388680 : Nat := 199579660789644521412499

theorem tailTrace_388680 : CollatzResearch.WordTrace tailWord_388680 prefixEnd_388680 199579660789644521412499 := by
  unfold tailWord_388680
  simp only [CollatzResearch.WordTrace]
  refine ⟨7088162115943108052113747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9450882821257477402818329 7088162115943108052113747)
  ·
    refine ⟨10632243173914662078170621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7088162115943108052113747 10632243173914662078170621)
    ·
      refine ⟨3987091190217998279313983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10632243173914662078170621 3987091190217998279313983)
      ·
        refine ⟨5980636785326997418970975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3987091190217998279313983 5980636785326997418970975)
        ·
          refine ⟨8970955177990496128456463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5980636785326997418970975 8970955177990496128456463)
          ·
            refine ⟨13456432766985744192684695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8970955177990496128456463 13456432766985744192684695)
            ·
              refine ⟨20184649150478616289027043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13456432766985744192684695 20184649150478616289027043)
              ·
                refine ⟨30276973725717924433540565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20184649150478616289027043 30276973725717924433540565)
                ·
                  refine ⟨709616571696513853911107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 30276973725717924433540565 709616571696513853911107)
                  ·
                    refine ⟨1064424857544770780866661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 709616571696513853911107 1064424857544770780866661)
                    ·
                      refine ⟨199579660789644521412499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1064424857544770780866661 199579660789644521412499)
                      ·
                        rfl

theorem cell23_388680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_388680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388680 prefixEnd_388680 := by exact prefixLift 388680
  have htrace : WordTrace (prefixWord ++ tailWord_388680) baseStart_388680 baseEnd_388680 := by
    simpa [prefixWord, tailWord_388680, baseEnd_388680] using wordTrace_append hprefix tailTrace_388680
  have hstable : (prefixWord ++ tailWord_388680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388680).length < 2 ^ (prefixWord ++ tailWord_388680).sum := by decide
  have hdescent : baseEnd_388680 < baseStart_388680 := by decide
  rcases family_descends (prefixWord ++ tailWord_388680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388684 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 2, 3, 2]
def baseStart_388684 : Nat := 118140960795 + 388684 * 2 ^ 59
def prefixEnd_388684 : Nat := 4983230072969 + 3 ^ 40 * 388684 * 2
def baseEnd_388684 : Nat := 199581714712262505762481

theorem tailTrace_388684 : CollatzResearch.WordTrace tailWord_388684 prefixEnd_388684 199581714712262505762481 := by
  unfold tailWord_388684
  simp only [CollatzResearch.WordTrace]
  refine ⟨7088235061935862393686553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9450980082581149858248737 7088235061935862393686553)
  ·
    refine ⟨5316176296451896795264915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7088235061935862393686553 5316176296451896795264915)
    ·
      refine ⟨7974264444677845192897373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5316176296451896795264915 7974264444677845192897373)
      ·
        refine ⟨2990349166754191947336515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7974264444677845192897373 2990349166754191947336515)
        ·
          refine ⟨4485523750131287921004773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2990349166754191947336515 4485523750131287921004773)
          ·
            refine ⟨841035703149616485188395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4485523750131287921004773 841035703149616485188395)
            ·
              refine ⟨1261553554724424727782593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841035703149616485188395 1261553554724424727782593)
              ·
                refine ⟨946165166043318545836945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261553554724424727782593 946165166043318545836945)
                ·
                  refine ⟨709623874532488909377709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 946165166043318545836945 709623874532488909377709)
                  ·
                    refine ⟨266108952949683341016641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 709623874532488909377709 266108952949683341016641)
                    ·
                      refine ⟨199581714712262505762481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266108952949683341016641 199581714712262505762481)
                      ·
                        rfl

theorem cell23_388684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_388684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388684 prefixEnd_388684 := by exact prefixLift 388684
  have htrace : WordTrace (prefixWord ++ tailWord_388684) baseStart_388684 baseEnd_388684 := by
    simpa [prefixWord, tailWord_388684, baseEnd_388684] using wordTrace_append hprefix tailTrace_388684
  have hstable : (prefixWord ++ tailWord_388684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388684).length < 2 ^ (prefixWord ++ tailWord_388684).sum := by decide
  have hdescent : baseEnd_388684 < baseStart_388684 := by decide
  rcases family_descends (prefixWord ++ tailWord_388684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388714 : List Nat := [3, 1, 3, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_388714 : Nat := 118140960795 + 388714 * 2 ^ 59
def prefixEnd_388714 : Nat := 4983230072969 + 3 ^ 40 * 388714 * 2
def baseEnd_388714 : Nat := 199597119131897388387343

theorem tailTrace_388714 : CollatzResearch.WordTrace tailWord_388714 prefixEnd_388714 199597119131897388387343 := by
  unfold tailWord_388714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3544391078440759977741299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9451709542508693273976797 3544391078440759977741299)
  ·
    refine ⟨5316586617661139966611949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3544391078440759977741299 5316586617661139966611949)
    ·
      refine ⟨1993719981622927487479481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5316586617661139966611949 1993719981622927487479481)
      ·
        refine ⟨1495289986217195615609611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1993719981622927487479481 1495289986217195615609611)
        ·
          refine ⟨2242934979325793423414417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495289986217195615609611 2242934979325793423414417)
          ·
            refine ⟨1682201234494345067560813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2242934979325793423414417 1682201234494345067560813)
            ·
              refine ⟨630825462935379400335305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1682201234494345067560813 630825462935379400335305)
              ·
                refine ⟨473119097201534550251479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630825462935379400335305 473119097201534550251479)
                ·
                  refine ⟨709678645802301825377219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473119097201534550251479 709678645802301825377219)
                  ·
                    refine ⟨1064517968703452738065829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 709678645802301825377219 1064517968703452738065829)
                    ·
                      refine ⟨199597119131897388387343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1064517968703452738065829 199597119131897388387343)
                      ·
                        rfl

theorem cell23_388714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_388714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388714 prefixEnd_388714 := by exact prefixLift 388714
  have htrace : WordTrace (prefixWord ++ tailWord_388714) baseStart_388714 baseEnd_388714 := by
    simpa [prefixWord, tailWord_388714, baseEnd_388714] using wordTrace_append hprefix tailTrace_388714
  have hstable : (prefixWord ++ tailWord_388714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388714).length < 2 ^ (prefixWord ++ tailWord_388714).sum := by decide
  have hdescent : baseEnd_388714 < baseStart_388714 := by decide
  rcases family_descends (prefixWord ++ tailWord_388714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388720 : List Nat := [2, 1, 1, 1, 6, 1, 2, 9]
def baseStart_388720 : Nat := 118140960795 + 388720 * 2 ^ 59
def prefixEnd_388720 : Nat := 4983230072969 + 3 ^ 40 * 388720 * 2
def baseEnd_388720 : Nat := 7392600000586087589345

theorem tailTrace_388720 : CollatzResearch.WordTrace tailWord_388720 prefixEnd_388720 7392600000586087589345 := by
  unfold tailWord_388720
  simp only [CollatzResearch.WordTrace]
  refine ⟨7088891575870651467841807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9451855434494201957122409 7088891575870651467841807)
  ·
    refine ⟨10633337363805977201762711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7088891575870651467841807 10633337363805977201762711)
    ·
      refine ⟨15950006045708965802644067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10633337363805977201762711 15950006045708965802644067)
      ·
        refine ⟨23925009068563448703966101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15950006045708965802644067 23925009068563448703966101)
        ·
          refine ⟨1121484800088911657998411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23925009068563448703966101 1121484800088911657998411)
          ·
            refine ⟨1682227200133367486997617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121484800088911657998411 1682227200133367486997617)
            ·
              refine ⟨1261670400100025615248213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682227200133367486997617 1261670400100025615248213)
              ·
                refine ⟨7392600000586087589345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1261670400100025615248213 7392600000586087589345)
                ·
                  rfl

theorem cell23_388720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 9].length) (baseStart_388720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388720 prefixEnd_388720 := by exact prefixLift 388720
  have htrace : WordTrace (prefixWord ++ tailWord_388720) baseStart_388720 baseEnd_388720 := by
    simpa [prefixWord, tailWord_388720, baseEnd_388720] using wordTrace_append hprefix tailTrace_388720
  have hstable : (prefixWord ++ tailWord_388720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388720).length < 2 ^ (prefixWord ++ tailWord_388720).sum := by decide
  have hdescent : baseEnd_388720 < baseStart_388720 := by decide
  rcases family_descends (prefixWord ++ tailWord_388720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388731 : List Nat := [1, 1, 1, 1, 1, 4, 4, 5, 1, 2, 2]
def baseStart_388731 : Nat := 118140960795 + 388731 * 2 ^ 59
def prefixEnd_388731 : Nat := 4983230072969 + 3 ^ 40 * 388731 * 2
def baseEnd_388731 : Nat := 199605848303023821874765

theorem tailTrace_388731 : CollatzResearch.WordTrace tailWord_388731 prefixEnd_388731 199605848303023821874765 := by
  unfold tailWord_388731
  simp only [CollatzResearch.WordTrace]
  refine ⟨14178184354701451814334047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9452122903134301209556031 14178184354701451814334047)
  ·
    refine ⟨21267276532052177721501071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14178184354701451814334047 21267276532052177721501071)
    ·
      refine ⟨31900914798078266582251607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21267276532052177721501071 31900914798078266582251607)
      ·
        refine ⟨47851372197117399873377411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31900914798078266582251607 47851372197117399873377411)
        ·
          refine ⟨71777058295676099810066117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47851372197117399873377411 71777058295676099810066117)
          ·
            refine ⟨13458198430439268714387397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71777058295676099810066117 13458198430439268714387397)
            ·
              refine ⟨2523412205707362883947637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13458198430439268714387397 2523412205707362883947637)
              ·
                refine ⟨236569894285065270370091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2523412205707362883947637 236569894285065270370091)
                ·
                  refine ⟨354854841427597905555137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236569894285065270370091 354854841427597905555137)
                  ·
                    refine ⟨266141131070698429166353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 354854841427597905555137 266141131070698429166353)
                    ·
                      refine ⟨199605848303023821874765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266141131070698429166353 199605848303023821874765)
                      ·
                        rfl

theorem cell23_388731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 1, 2, 2].length) (baseStart_388731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388731 prefixEnd_388731 := by exact prefixLift 388731
  have htrace : WordTrace (prefixWord ++ tailWord_388731) baseStart_388731 baseEnd_388731 := by
    simpa [prefixWord, tailWord_388731, baseEnd_388731] using wordTrace_append hprefix tailTrace_388731
  have hstable : (prefixWord ++ tailWord_388731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388731).length < 2 ^ (prefixWord ++ tailWord_388731).sum := by decide
  have hdescent : baseEnd_388731 < baseStart_388731 := by decide
  rcases family_descends (prefixWord ++ tailWord_388731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388754 : List Nat := [3, 2, 3, 1, 3, 2, 1, 8]
def baseStart_388754 : Nat := 118140960795 + 388754 * 2 ^ 59
def prefixEnd_388754 : Nat := 4983230072969 + 3 ^ 40 * 388754 * 2
def baseEnd_388754 : Nat := 7393246605854712292117

theorem tailTrace_388754 : CollatzResearch.WordTrace tailWord_388754 prefixEnd_388754 7393246605854712292117 := by
  unfold tailWord_388754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3544755808404531685605329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9452682155745417828280877 3544755808404531685605329)
  ·
    refine ⟨2658566856303398764203997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3544755808404531685605329 2658566856303398764203997)
    ·
      refine ⟨996962571113774536576499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2658566856303398764203997 996962571113774536576499)
      ·
        refine ⟨1495443856670661804864749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996962571113774536576499 1495443856670661804864749)
        ·
          refine ⟨560791446251498176824281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1495443856670661804864749 560791446251498176824281)
          ·
            refine ⟨420593584688623632618211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560791446251498176824281 420593584688623632618211)
            ·
              refine ⟨630890377032935448927317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420593584688623632618211 630890377032935448927317)
              ·
                refine ⟨7393246605854712292117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 630890377032935448927317 7393246605854712292117)
                ·
                  rfl

theorem cell23_388754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 8].length) (baseStart_388754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388754 prefixEnd_388754 := by exact prefixLift 388754
  have htrace : WordTrace (prefixWord ++ tailWord_388754) baseStart_388754 baseEnd_388754 := by
    simpa [prefixWord, tailWord_388754, baseEnd_388754] using wordTrace_append hprefix tailTrace_388754
  have hstable : (prefixWord ++ tailWord_388754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388754).length < 2 ^ (prefixWord ++ tailWord_388754).sum := by decide
  have hdescent : baseEnd_388754 < baseStart_388754 := by decide
  rcases family_descends (prefixWord ++ tailWord_388754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388782 : List Nat := [4, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_388782 : Nat := 118140960795 + 388782 * 2 ^ 59
def prefixEnd_388782 : Nat := 4983230072969 + 3 ^ 40 * 388782 * 2
def baseEnd_388782 : Nat := 199632035816403122337031

theorem tailTrace_388782 : CollatzResearch.WordTrace tailWord_388782 prefixEnd_388782 199632035816403122337031 := by
  unfold tailWord_388782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1772505559689585940555075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9453362985011125016293733 1772505559689585940555075)
  ·
    refine ⟨2658758339534378910832613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1772505559689585940555075 2658758339534378910832613)
    ·
      refine ⟨498517188662696045781115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2658758339534378910832613 498517188662696045781115)
      ·
        refine ⟨747775782994044068671673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498517188662696045781115 747775782994044068671673)
        ·
          refine ⟨560831837245533051503755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 747775782994044068671673 560831837245533051503755)
          ·
            refine ⟨841247755868299577255633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560831837245533051503755 841247755868299577255633)
            ·
              refine ⟨630935816901224682941725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 841247755868299577255633 630935816901224682941725)
              ·
                refine ⟨236600931337959256103147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 630935816901224682941725 236600931337959256103147)
                ·
                  refine ⟨354901397006938884154721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236600931337959256103147 354901397006938884154721)
                  ·
                    refine ⟨266176047755204163116041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 354901397006938884154721 266176047755204163116041)
                    ·
                      refine ⟨199632035816403122337031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266176047755204163116041 199632035816403122337031)
                      ·
                        rfl

theorem cell23_388782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_388782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388782 prefixEnd_388782 := by exact prefixLift 388782
  have htrace : WordTrace (prefixWord ++ tailWord_388782) baseStart_388782 baseEnd_388782 := by
    simpa [prefixWord, tailWord_388782, baseEnd_388782] using wordTrace_append hprefix tailTrace_388782
  have hstable : (prefixWord ++ tailWord_388782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388782).length < 2 ^ (prefixWord ++ tailWord_388782).sum := by decide
  have hdescent : baseEnd_388782 < baseStart_388782 := by decide
  rcases family_descends (prefixWord ++ tailWord_388782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388791 : List Nat := [1, 1, 3, 1, 5, 2, 1, 3, 1, 3, 2]
def baseStart_388791 : Nat := 118140960795 + 388791 * 2 ^ 59
def prefixEnd_388791 : Nat := 4983230072969 + 3 ^ 40 * 388791 * 2
def baseEnd_388791 : Nat := 199636657142293587124489

theorem tailTrace_388791 : CollatzResearch.WordTrace tailWord_388791 prefixEnd_388791 199636657142293587124489 := by
  unfold tailWord_388791
  simp only [CollatzResearch.WordTrace]
  refine ⟨14180372734484082061518227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9453581822989388041012151 14180372734484082061518227)
  ·
    refine ⟨21270559101726123092277341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14180372734484082061518227 21270559101726123092277341)
    ·
      refine ⟨7976459663147296159604003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21270559101726123092277341 7976459663147296159604003)
      ·
        refine ⟨11964689494720944239406005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7976459663147296159604003 11964689494720944239406005)
        ·
          refine ⟨1121689640130088522444313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11964689494720944239406005 1121689640130088522444313)
          ·
            refine ⟨841267230097566391833235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1121689640130088522444313 841267230097566391833235)
            ·
              refine ⟨1261900845146349587749853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841267230097566391833235 1261900845146349587749853)
              ·
                refine ⟨473212816929881095406195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1261900845146349587749853 473212816929881095406195)
                ·
                  refine ⟨709819225394821643109293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473212816929881095406195 709819225394821643109293)
                  ·
                    refine ⟨266182209523058116165985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 709819225394821643109293 266182209523058116165985)
                    ·
                      refine ⟨199636657142293587124489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266182209523058116165985 199636657142293587124489)
                      ·
                        rfl

theorem cell23_388791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 3, 2].length) (baseStart_388791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388791 prefixEnd_388791 := by exact prefixLift 388791
  have htrace : WordTrace (prefixWord ++ tailWord_388791) baseStart_388791 baseEnd_388791 := by
    simpa [prefixWord, tailWord_388791, baseEnd_388791] using wordTrace_append hprefix tailTrace_388791
  have hstable : (prefixWord ++ tailWord_388791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388791).length < 2 ^ (prefixWord ++ tailWord_388791).sum := by decide
  have hdescent : baseEnd_388791 < baseStart_388791 := by decide
  rcases family_descends (prefixWord ++ tailWord_388791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388798 : List Nat := [4, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_388798 : Nat := 118140960795 + 388798 * 2 ^ 59
def prefixEnd_388798 : Nat := 4983230072969 + 3 ^ 40 * 388798 * 2
def baseEnd_388798 : Nat := 199640251506875059736957

theorem tailTrace_388798 : CollatzResearch.WordTrace tailWord_388798 prefixEnd_388798 199640251506875059736957 := by
  unfold tailWord_388798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1772578505682340282127881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9453752030305814838015365 1772578505682340282127881)
  ·
    refine ⟨1329433879261755211595911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1772578505682340282127881 1329433879261755211595911)
    ·
      refine ⟨1994150818892632817393867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1329433879261755211595911 1994150818892632817393867)
      ·
        refine ⟨2991226228338949226090801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1994150818892632817393867 2991226228338949226090801)
        ·
          refine ⟨2243419671254211919568101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2991226228338949226090801 2243419671254211919568101)
          ·
            refine ⟨420641188360164734919019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2243419671254211919568101 420641188360164734919019)
            ·
              refine ⟨630961782540247102378529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420641188360164734919019 630961782540247102378529)
              ·
                refine ⟨473221336905185326783897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630961782540247102378529 473221336905185326783897)
                ·
                  refine ⟨354916002678888995087923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473221336905185326783897 354916002678888995087923)
                  ·
                    refine ⟨532374004018333492631885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 354916002678888995087923 532374004018333492631885)
                    ·
                      refine ⟨199640251506875059736957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 532374004018333492631885 199640251506875059736957)
                      ·
                        rfl

theorem cell23_388798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_388798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388798 prefixEnd_388798 := by exact prefixLift 388798
  have htrace : WordTrace (prefixWord ++ tailWord_388798) baseStart_388798 baseEnd_388798 := by
    simpa [prefixWord, tailWord_388798, baseEnd_388798] using wordTrace_append hprefix tailTrace_388798
  have hstable : (prefixWord ++ tailWord_388798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388798).length < 2 ^ (prefixWord ++ tailWord_388798).sum := by decide
  have hdescent : baseEnd_388798 < baseStart_388798 := by decide
  rcases family_descends (prefixWord ++ tailWord_388798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388817 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_388817 : Nat := 118140960795 + 388817 * 2 ^ 59
def prefixEnd_388817 : Nat := 4983230072969 + 3 ^ 40 * 388817 * 2
def baseEnd_388817 : Nat := 199650007639310485399369

theorem tailTrace_388817 : CollatzResearch.WordTrace tailWord_388817 prefixEnd_388817 199650007639310485399369 := by
  unfold tailWord_388817
  simp only [CollatzResearch.WordTrace]
  refine ⟨14181321032389888501964705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9454214021593259001309803 14181321032389888501964705)
  ·
    refine ⟨10635990774292416376473529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14181321032389888501964705 10635990774292416376473529)
    ·
      refine ⟨7976993080719312282355147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10635990774292416376473529 7976993080719312282355147)
      ·
        refine ⟨11965489621078968423532721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7976993080719312282355147 11965489621078968423532721)
        ·
          refine ⟨8974117215809226317649541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11965489621078968423532721 8974117215809226317649541)
          ·
            refine ⟨1682646977964229934559289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8974117215809226317649541 1682646977964229934559289)
            ·
              refine ⟨1261985233473172450919467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682646977964229934559289 1261985233473172450919467)
              ·
                refine ⟨1892977850209758676379201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261985233473172450919467 1892977850209758676379201)
                ·
                  refine ⟨1419733387657319007284401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1892977850209758676379201 1419733387657319007284401)
                  ·
                    refine ⟨1064800040742989255463301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1419733387657319007284401 1064800040742989255463301)
                    ·
                      refine ⟨199650007639310485399369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1064800040742989255463301 199650007639310485399369)
                      ·
                        rfl

theorem cell23_388817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_388817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388817 prefixEnd_388817 := by exact prefixLift 388817
  have htrace : WordTrace (prefixWord ++ tailWord_388817) baseStart_388817 baseEnd_388817 := by
    simpa [prefixWord, tailWord_388817, baseEnd_388817] using wordTrace_append hprefix tailTrace_388817
  have hstable : (prefixWord ++ tailWord_388817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388817).length < 2 ^ (prefixWord ++ tailWord_388817).sum := by decide
  have hdescent : baseEnd_388817 < baseStart_388817 := by decide
  rcases family_descends (prefixWord ++ tailWord_388817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388844 : List Nat := [2, 2, 1, 1, 2, 2, 5, 3, 5]
def baseStart_388844 : Nat := 118140960795 + 388844 * 2 ^ 59
def prefixEnd_388844 : Nat := 4983230072969 + 3 ^ 40 * 388844 * 2
def baseEnd_388844 : Nat := 22184874624109097751305

theorem tailTrace_388844 : CollatzResearch.WordTrace tailWord_388844 prefixEnd_388844 22184874624109097751305 := by
  unfold tailWord_388844
  simp only [CollatzResearch.WordTrace]
  refine ⟨7091152901646036056598793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9454870535528048075465057 7091152901646036056598793)
  ·
    refine ⟨5318364676234527042449095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7091152901646036056598793 5318364676234527042449095)
    ·
      refine ⟨7977547014351790563673643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5318364676234527042449095 7977547014351790563673643)
      ·
        refine ⟨11966320521527685845510465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7977547014351790563673643 11966320521527685845510465)
        ·
          refine ⟨8974740391145764384132849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11966320521527685845510465 8974740391145764384132849)
          ·
            refine ⟨6731055293359323288099637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8974740391145764384132849 6731055293359323288099637)
            ·
              refine ⟨631036433752436558259341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6731055293359323288099637 631036433752436558259341)
              ·
                refine ⟨236638662657163709347253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 631036433752436558259341 236638662657163709347253)
                ·
                  refine ⟨22184874624109097751305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 236638662657163709347253 22184874624109097751305)
                  ·
                    rfl

theorem cell23_388844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 5].length) (baseStart_388844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388844 prefixEnd_388844 := by exact prefixLift 388844
  have htrace : WordTrace (prefixWord ++ tailWord_388844) baseStart_388844 baseEnd_388844 := by
    simpa [prefixWord, tailWord_388844, baseEnd_388844] using wordTrace_append hprefix tailTrace_388844
  have hstable : (prefixWord ++ tailWord_388844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388844).length < 2 ^ (prefixWord ++ tailWord_388844).sum := by decide
  have hdescent : baseEnd_388844 < baseStart_388844 := by decide
  rcases family_descends (prefixWord ++ tailWord_388844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388948 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_388948 : Nat := 118140960795 + 388948 * 2 ^ 59
def prefixEnd_388948 : Nat := 4983230072969 + 3 ^ 40 * 388948 * 2
def baseEnd_388948 : Nat := 199717273605049472861267

theorem tailTrace_388948 : CollatzResearch.WordTrace tailWord_388948 prefixEnd_388948 199717273605049472861267 := by
  unfold tailWord_388948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7093049497457648937491749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9457399329943531916655665 7093049497457648937491749)
  ·
    refine ⟨1329946780773309175779703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7093049497457648937491749 1329946780773309175779703)
    ·
      refine ⟨1994920171159963763669555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1329946780773309175779703 1994920171159963763669555)
      ·
        refine ⟨2992380256739945645504333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1994920171159963763669555 2992380256739945645504333)
        ·
          refine ⟨1122142596277479617064125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2992380256739945645504333 1122142596277479617064125)
          ·
            refine ⟨420803473604054856399047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1122142596277479617064125 420803473604054856399047)
            ·
              refine ⟨631205210406082284598571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420803473604054856399047 631205210406082284598571)
              ·
                refine ⟨946807815609123426897857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631205210406082284598571 946807815609123426897857)
                ·
                  refine ⟨710105861706842570173393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 946807815609123426897857 710105861706842570173393)
                  ·
                    refine ⟨532579396280131927630045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 710105861706842570173393 532579396280131927630045)
                    ·
                      refine ⟨199717273605049472861267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 532579396280131927630045 199717273605049472861267)
                      ·
                        rfl

theorem cell23_388948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_388948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_388948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_388948 prefixEnd_388948 := by exact prefixLift 388948
  have htrace : WordTrace (prefixWord ++ tailWord_388948) baseStart_388948 baseEnd_388948 := by
    simpa [prefixWord, tailWord_388948, baseEnd_388948] using wordTrace_append hprefix tailTrace_388948
  have hstable : (prefixWord ++ tailWord_388948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388948).length < 2 ^ (prefixWord ++ tailWord_388948).sum := by decide
  have hdescent : baseEnd_388948 < baseStart_388948 := by decide
  rcases family_descends (prefixWord ++ tailWord_388948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389001 : List Nat := [1, 2, 1, 1, 5, 1, 4, 2, 1, 1, 4]
def baseStart_389001 : Nat := 118140960795 + 389001 * 2 ^ 59
def prefixEnd_389001 : Nat := 4983230072969 + 3 ^ 40 * 389001 * 2
def baseEnd_389001 : Nat := 199744488079737765498523

theorem tailTrace_389001 : CollatzResearch.WordTrace tailWord_389001 prefixEnd_389001 199744488079737765498523 := by
  unfold tailWord_389001
  simp only [CollatzResearch.WordTrace]
  refine ⟨14188032063723287926662857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9458688042482191951108571 14188032063723287926662857)
  ·
    refine ⟨10641024047792465944997143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14188032063723287926662857 10641024047792465944997143)
    ·
      refine ⟨15961536071688698917495715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10641024047792465944997143 15961536071688698917495715)
      ·
        refine ⟨23942304107533048376243573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15961536071688698917495715 23942304107533048376243573)
        ·
          refine ⟨2244591010081223285272835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23942304107533048376243573 2244591010081223285272835)
          ·
            refine ⟨3366886515121834927909253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244591010081223285272835 3366886515121834927909253)
            ·
              refine ⟨631291221585344048982985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3366886515121834927909253 631291221585344048982985)
              ·
                refine ⟨473468416189008036737239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631291221585344048982985 473468416189008036737239)
                ·
                  refine ⟨710202624283512055105859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473468416189008036737239 710202624283512055105859)
                  ·
                    refine ⟨1065303936425268082658789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 710202624283512055105859 1065303936425268082658789)
                    ·
                      refine ⟨199744488079737765498523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1065303936425268082658789 199744488079737765498523)
                      ·
                        rfl

theorem cell23_389001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 1, 4].length) (baseStart_389001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389001 prefixEnd_389001 := by exact prefixLift 389001
  have htrace : WordTrace (prefixWord ++ tailWord_389001) baseStart_389001 baseEnd_389001 := by
    simpa [prefixWord, tailWord_389001, baseEnd_389001] using wordTrace_append hprefix tailTrace_389001
  have hstable : (prefixWord ++ tailWord_389001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389001).length < 2 ^ (prefixWord ++ tailWord_389001).sum := by decide
  have hdescent : baseEnd_389001 < baseStart_389001 := by decide
  rcases family_descends (prefixWord ++ tailWord_389001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389012 : List Nat := [2, 4, 2, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_389012 : Nat := 118140960795 + 389012 * 2 ^ 59
def prefixEnd_389012 : Nat := 4983230072969 + 3 ^ 40 * 389012 * 2
def baseEnd_389012 : Nat := 199750136366937222460973

theorem tailTrace_389012 : CollatzResearch.WordTrace tailWord_389012 prefixEnd_389012 199750136366937222460973 := by
  unfold tailWord_389012
  simp only [CollatzResearch.WordTrace]
  refine ⟨7094216633341718402656645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9458955511122291203542193 7094216633341718402656645)
  ·
    refine ⟨1330165618751572200498121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7094216633341718402656645 1330165618751572200498121)
    ·
      refine ⟨997624214063679150373591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1330165618751572200498121 997624214063679150373591)
      ·
        refine ⟨1496436321095518725560387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997624214063679150373591 1496436321095518725560387)
        ·
          refine ⟨2244654481643278088340581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496436321095518725560387 2244654481643278088340581)
          ·
            refine ⟨420872715308114641563859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2244654481643278088340581 420872715308114641563859)
            ·
              refine ⟨631309072962171962345789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420872715308114641563859 631309072962171962345789)
              ·
                refine ⟨236740902360814485879671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 631309072962171962345789 236740902360814485879671)
                ·
                  refine ⟨355111353541221728819507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236740902360814485879671 355111353541221728819507)
                  ·
                    refine ⟨532667030311832593229261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 355111353541221728819507 532667030311832593229261)
                    ·
                      refine ⟨199750136366937222460973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 532667030311832593229261 199750136366937222460973)
                      ·
                        rfl

theorem cell23_389012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_389012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389012 prefixEnd_389012 := by exact prefixLift 389012
  have htrace : WordTrace (prefixWord ++ tailWord_389012) baseStart_389012 baseEnd_389012 := by
    simpa [prefixWord, tailWord_389012, baseEnd_389012] using wordTrace_append hprefix tailTrace_389012
  have hstable : (prefixWord ++ tailWord_389012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389012).length < 2 ^ (prefixWord ++ tailWord_389012).sum := by decide
  have hdescent : baseEnd_389012 < baseStart_389012 := by decide
  rcases family_descends (prefixWord ++ tailWord_389012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389021 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_389021 : Nat := 118140960795 + 389021 * 2 ^ 59
def prefixEnd_389021 : Nat := 4983230072969 + 3 ^ 40 * 389021 * 2
def baseEnd_389021 : Nat := 199754757692827687248431

theorem tailTrace_389021 : CollatzResearch.WordTrace tailWord_389021 prefixEnd_389021 199754757692827687248431 := by
  unfold tailWord_389021
  simp only [CollatzResearch.WordTrace]
  refine ⟨14188761523650831342390917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9459174349100554228260611 14188761523650831342390917)
  ·
    refine ⟨2660392785684530876698297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14188761523650831342390917 2660392785684530876698297)
    ·
      refine ⟨1995294589263398157523723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2660392785684530876698297 1995294589263398157523723)
      ·
        refine ⟨2992941883895097236285585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995294589263398157523723 2992941883895097236285585)
        ·
          refine ⟨2244706412921322927214189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2992941883895097236285585 2244706412921322927214189)
          ·
            refine ⟨841764904845496097705321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2244706412921322927214189 841764904845496097705321)
            ·
              refine ⟨631323678634122073278991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 841764904845496097705321 631323678634122073278991)
              ·
                refine ⟨946985517951183109918487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631323678634122073278991 946985517951183109918487)
                ·
                  refine ⟨1420478276926774664877731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 946985517951183109918487 1420478276926774664877731)
                  ·
                    refine ⟨2130717415390161997316597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1420478276926774664877731 2130717415390161997316597)
                    ·
                      refine ⟨199754757692827687248431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2130717415390161997316597 199754757692827687248431)
                      ·
                        rfl

theorem cell23_389021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_389021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389021 prefixEnd_389021 := by exact prefixLift 389021
  have htrace : WordTrace (prefixWord ++ tailWord_389021) baseStart_389021 baseEnd_389021 := by
    simpa [prefixWord, tailWord_389021, baseEnd_389021] using wordTrace_append hprefix tailTrace_389021
  have hstable : (prefixWord ++ tailWord_389021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389021).length < 2 ^ (prefixWord ++ tailWord_389021).sum := by decide
  have hdescent : baseEnd_389021 < baseStart_389021 := by decide
  rcases family_descends (prefixWord ++ tailWord_389021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389022 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_389022 : Nat := 118140960795 + 389022 * 2 ^ 59
def prefixEnd_389022 : Nat := 4983230072969 + 3 ^ 40 * 389022 * 2
def baseEnd_389022 : Nat := 199755271173482183335927

theorem tailTrace_389022 : CollatzResearch.WordTrace tailWord_389022 prefixEnd_389022 199755271173482183335927 := by
  unfold tailWord_389022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1773599749580901064147165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9459198664431472342118213 1773599749580901064147165)
  ·
    refine ⟨665099906092837899055187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1773599749580901064147165 665099906092837899055187)
    ·
      refine ⟨997649859139256848582781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 665099906092837899055187 997649859139256848582781)
      ·
        refine ⟨374118697177221318218543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 997649859139256848582781 374118697177221318218543)
        ·
          refine ⟨561178045765831977327815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374118697177221318218543 561178045765831977327815)
          ·
            refine ⟨841767068648747965991723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561178045765831977327815 841767068648747965991723)
            ·
              refine ⟨1262650602973121948987585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841767068648747965991723 1262650602973121948987585)
              ·
                refine ⟨946987952229841461740689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1262650602973121948987585 946987952229841461740689)
                ·
                  refine ⟨710240964172381096305517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 946987952229841461740689 710240964172381096305517)
                  ·
                    refine ⟨266340361564642911114569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 710240964172381096305517 266340361564642911114569)
                    ·
                      refine ⟨199755271173482183335927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266340361564642911114569 199755271173482183335927)
                      ·
                        rfl

theorem cell23_389022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_389022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389022 prefixEnd_389022 := by exact prefixLift 389022
  have htrace : WordTrace (prefixWord ++ tailWord_389022) baseStart_389022 baseEnd_389022 := by
    simpa [prefixWord, tailWord_389022, baseEnd_389022] using wordTrace_append hprefix tailTrace_389022
  have hstable : (prefixWord ++ tailWord_389022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389022).length < 2 ^ (prefixWord ++ tailWord_389022).sum := by decide
  have hdescent : baseEnd_389022 < baseStart_389022 := by decide
  rcases family_descends (prefixWord ++ tailWord_389022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389045 : List Nat := [1, 3, 3, 2, 1, 4, 2, 1, 2, 4]
def baseStart_389045 : Nat := 118140960795 + 389045 * 2 ^ 59
def prefixEnd_389045 : Nat := 4983230072969 + 3 ^ 40 * 389045 * 2
def baseEnd_389045 : Nat := 66589027076178531116107

theorem tailTrace_389045 : CollatzResearch.WordTrace tailWord_389045 prefixEnd_389045 66589027076178531116107 := by
  unfold tailWord_389045
  simp only [CollatzResearch.WordTrace]
  refine ⟨14189636875563883441264589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9459757917042588960843059 14189636875563883441264589)
  ·
    refine ⟨5321113828336456290474221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14189636875563883441264589 5321113828336456290474221)
    ·
      refine ⟨1995417685626171108927833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5321113828336456290474221 1995417685626171108927833)
      ·
        refine ⟨1496563264219628331695875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1995417685626171108927833 1496563264219628331695875)
        ·
          refine ⟨2244844896329442497543813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496563264219628331695875 2244844896329442497543813)
          ·
            refine ⟨420908418061770468289465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2244844896329442497543813 420908418061770468289465)
            ·
              refine ⟨315681313546327851217099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420908418061770468289465 315681313546327851217099)
              ·
                refine ⟨473521970319491776825649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315681313546327851217099 473521970319491776825649)
                ·
                  refine ⟨355141477739618832619237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473521970319491776825649 355141477739618832619237)
                  ·
                    refine ⟨66589027076178531116107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 355141477739618832619237 66589027076178531116107)
                    ·
                      rfl

theorem cell23_389045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_389045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389045 prefixEnd_389045 := by exact prefixLift 389045
  have htrace : WordTrace (prefixWord ++ tailWord_389045) baseStart_389045 baseEnd_389045 := by
    simpa [prefixWord, tailWord_389045, baseEnd_389045] using wordTrace_append hprefix tailTrace_389045
  have hstable : (prefixWord ++ tailWord_389045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389045).length < 2 ^ (prefixWord ++ tailWord_389045).sum := by decide
  have hdescent : baseEnd_389045 < baseStart_389045 := by decide
  rcases family_descends (prefixWord ++ tailWord_389045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389052 : List Nat := [2, 2, 2, 5, 2, 1, 1, 2, 1, 1, 4]
def baseStart_389052 : Nat := 118140960795 + 389052 * 2 ^ 59
def prefixEnd_389052 : Nat := 4983230072969 + 3 ^ 40 * 389052 * 2
def baseEnd_389052 : Nat := 199770675593117065960789

theorem tailTrace_389052 : CollatzResearch.WordTrace tailWord_389052 prefixEnd_389052 199770675593117065960789 := by
  unfold tailWord_389052
  simp only [CollatzResearch.WordTrace]
  refine ⟨7094946093269261818384705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9459928124359015757846273 7094946093269261818384705)
  ·
    refine ⟨5321209569951946363788529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7094946093269261818384705 5321209569951946363788529)
    ·
      refine ⟨3990907177463959772841397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5321209569951946363788529 3990907177463959772841397)
      ·
        refine ⟨374147547887246228703881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3990907177463959772841397 374147547887246228703881)
        ·
          refine ⟨280610660915434671527911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374147547887246228703881 280610660915434671527911)
          ·
            refine ⟨420915991373152007291867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280610660915434671527911 420915991373152007291867)
            ·
              refine ⟨631373987059728010937801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420915991373152007291867 631373987059728010937801)
              ·
                refine ⟨473530490294796008203351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631373987059728010937801 473530490294796008203351)
                ·
                  refine ⟨710295735442194012305027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473530490294796008203351 710295735442194012305027)
                  ·
                    refine ⟨1065443603163291018457541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 710295735442194012305027 1065443603163291018457541)
                    ·
                      refine ⟨199770675593117065960789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1065443603163291018457541 199770675593117065960789)
                      ·
                        rfl

theorem cell23_389052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_389052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389052 prefixEnd_389052 := by exact prefixLift 389052
  have htrace : WordTrace (prefixWord ++ tailWord_389052) baseStart_389052 baseEnd_389052 := by
    simpa [prefixWord, tailWord_389052, baseEnd_389052] using wordTrace_append hprefix tailTrace_389052
  have hstable : (prefixWord ++ tailWord_389052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389052).length < 2 ^ (prefixWord ++ tailWord_389052).sum := by decide
  have hdescent : baseEnd_389052 < baseStart_389052 := by decide
  rcases family_descends (prefixWord ++ tailWord_389052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389104 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 4]
def baseStart_389104 : Nat := 118140960795 + 389104 * 2 ^ 59
def prefixEnd_389104 : Nat := 4983230072969 + 3 ^ 40 * 389104 * 2
def baseEnd_389104 : Nat := 199797376587150862510549

theorem tailTrace_389104 : CollatzResearch.WordTrace tailWord_389104 prefixEnd_389104 199797376587150862510549 := by
  unfold tailWord_389104
  simp only [CollatzResearch.WordTrace]
  refine ⟨7095894391175068258831183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9461192521566757678441577 7095894391175068258831183)
  ·
    refine ⟨10643841586762602388246775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7095894391175068258831183 10643841586762602388246775)
    ·
      refine ⟨15965762380143903582370163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10643841586762602388246775 15965762380143903582370163)
      ·
        refine ⟨23948643570215855373555245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15965762380143903582370163 23948643570215855373555245)
        ·
          refine ⟨8980741338830945765083217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23948643570215855373555245 8980741338830945765083217)
          ·
            refine ⟨6735556004123209323812413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8980741338830945765083217 6735556004123209323812413)
            ·
              refine ⟨2525833501546203496429655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6735556004123209323812413 2525833501546203496429655)
              ·
                refine ⟨3788750252319305244644483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525833501546203496429655 3788750252319305244644483)
                ·
                  refine ⟨5683125378478957866966725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3788750252319305244644483 5683125378478957866966725)
                  ·
                    refine ⟨1065586008464804600056261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683125378478957866966725 1065586008464804600056261)
                    ·
                      refine ⟨199797376587150862510549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1065586008464804600056261 199797376587150862510549)
                      ·
                        rfl

theorem cell23_389104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_389104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389104 prefixEnd_389104 := by exact prefixLift 389104
  have htrace : WordTrace (prefixWord ++ tailWord_389104) baseStart_389104 baseEnd_389104 := by
    simpa [prefixWord, tailWord_389104, baseEnd_389104] using wordTrace_append hprefix tailTrace_389104
  have hstable : (prefixWord ++ tailWord_389104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389104).length < 2 ^ (prefixWord ++ tailWord_389104).sum := by decide
  have hdescent : baseEnd_389104 < baseStart_389104 := by decide
  rcases family_descends (prefixWord ++ tailWord_389104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389148 : List Nat := [2, 2, 3, 1, 3, 1, 2, 4, 5]
def baseStart_389148 : Nat := 118140960795 + 389148 * 2 ^ 59
def prefixEnd_389148 : Nat := 4983230072969 + 3 ^ 40 * 389148 * 2
def baseEnd_389148 : Nat := 22202218859549854484483

theorem tailTrace_389148 : CollatzResearch.WordTrace tailWord_389148 prefixEnd_389148 22202218859549854484483 := by
  unfold tailWord_389148
  simp only [CollatzResearch.WordTrace]
  refine ⟨7096696797095366016132049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9462262396127154688176065 7096696797095366016132049)
  ·
    refine ⟨5322522597821524512099037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7096696797095366016132049 5322522597821524512099037)
    ·
      refine ⟨1995945974183071692037139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5322522597821524512099037 1995945974183071692037139)
      ·
        refine ⟨2993918961274607538055709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995945974183071692037139 2993918961274607538055709)
        ·
          refine ⟨1122719610477977826770891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2993918961274607538055709 1122719610477977826770891)
          ·
            refine ⟨1684079415716966740156337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122719610477977826770891 1684079415716966740156337)
            ·
              refine ⟨1263059561787725055117253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1684079415716966740156337 1263059561787725055117253)
              ·
                refine ⟨236823667835198447834485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1263059561787725055117253 236823667835198447834485)
                ·
                  refine ⟨22202218859549854484483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 236823667835198447834485 22202218859549854484483)
                  ·
                    rfl

theorem cell23_389148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 5].length) (baseStart_389148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389148 prefixEnd_389148 := by exact prefixLift 389148
  have htrace : WordTrace (prefixWord ++ tailWord_389148) baseStart_389148 baseEnd_389148 := by
    simpa [prefixWord, tailWord_389148, baseEnd_389148] using wordTrace_append hprefix tailTrace_389148
  have hstable : (prefixWord ++ tailWord_389148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389148).length < 2 ^ (prefixWord ++ tailWord_389148).sum := by decide
  have hdescent : baseEnd_389148 < baseStart_389148 := by decide
  rcases family_descends (prefixWord ++ tailWord_389148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389159 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_389159 : Nat := 118140960795 + 389159 * 2 ^ 59
def prefixEnd_389159 : Nat := 4983230072969 + 3 ^ 40 * 389159 * 2
def baseEnd_389159 : Nat := 199825618023148147322797

theorem tailTrace_389159 : CollatzResearch.WordTrace tailWord_389159 prefixEnd_389159 199825618023148147322797 := by
  unfold tailWord_389159
  simp only [CollatzResearch.WordTrace]
  refine ⟨14193794797150880910914531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9462529864767253940609687 14193794797150880910914531)
  ·
    refine ⟨21290692195726321366371797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14193794797150880910914531 21290692195726321366371797)
    ·
      refine ⟨499000598337335657024339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 21290692195726321366371797 499000598337335657024339)
      ·
        refine ⟨748500897506003485536509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499000598337335657024339 748500897506003485536509)
        ·
          refine ⟨280687836564751307076191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 748500897506003485536509 280687836564751307076191)
          ·
            refine ⟨421031754847126960614287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280687836564751307076191 421031754847126960614287)
            ·
              refine ⟨631547632270690440921431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421031754847126960614287 631547632270690440921431)
              ·
                refine ⟨947321448406035661382147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631547632270690440921431 947321448406035661382147)
                ·
                  refine ⟨1420982172609053492073221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947321448406035661382147 1420982172609053492073221)
                  ·
                    refine ⟨266434157364197529763729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1420982172609053492073221 266434157364197529763729)
                    ·
                      refine ⟨199825618023148147322797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266434157364197529763729 199825618023148147322797)
                      ·
                        rfl

theorem cell23_389159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_389159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389159 prefixEnd_389159 := by exact prefixLift 389159
  have htrace : WordTrace (prefixWord ++ tailWord_389159) baseStart_389159 baseEnd_389159 := by
    simpa [prefixWord, tailWord_389159, baseEnd_389159] using wordTrace_append hprefix tailTrace_389159
  have hstable : (prefixWord ++ tailWord_389159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389159).length < 2 ^ (prefixWord ++ tailWord_389159).sum := by decide
  have hdescent : baseEnd_389159 < baseStart_389159 := by decide
  rcases family_descends (prefixWord ++ tailWord_389159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389181 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_389181 : Nat := 118140960795 + 389181 * 2 ^ 59
def prefixEnd_389181 : Nat := 4983230072969 + 3 ^ 40 * 389181 * 2
def baseEnd_389181 : Nat := 199836914597547061247695

theorem tailTrace_389181 : CollatzResearch.WordTrace tailWord_389181 prefixEnd_389181 199836914597547061247695 := by
  unfold tailWord_389181
  simp only [CollatzResearch.WordTrace]
  refine ⟨14194597203071178668215397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9463064802047452445476931 14194597203071178668215397)
  ·
    refine ⟨2661486975575846000290387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14194597203071178668215397 2661486975575846000290387)
    ·
      refine ⟨3992230463363769000435581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2661486975575846000290387 3992230463363769000435581)
      ·
        refine ⟨1497086423761413375163343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3992230463363769000435581 1497086423761413375163343)
        ·
          refine ⟨2245629635642120062745015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1497086423761413375163343 2245629635642120062745015)
          ·
            refine ⟨3368444453463180094117523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2245629635642120062745015 3368444453463180094117523)
            ·
              refine ⟨5052666680194770141176285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3368444453463180094117523 5052666680194770141176285)
              ·
                refine ⟨1894750005073038802941107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5052666680194770141176285 1894750005073038802941107)
                ·
                  refine ⟨2842125007609558204411661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1894750005073038802941107 2842125007609558204411661)
                  ·
                    refine ⟨1065796877853584326654373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2842125007609558204411661 1065796877853584326654373)
                    ·
                      refine ⟨199836914597547061247695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1065796877853584326654373 199836914597547061247695)
                      ·
                        rfl

theorem cell23_389181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_389181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389181 prefixEnd_389181 := by exact prefixLift 389181
  have htrace : WordTrace (prefixWord ++ tailWord_389181) baseStart_389181 baseEnd_389181 := by
    simpa [prefixWord, tailWord_389181, baseEnd_389181] using wordTrace_append hprefix tailTrace_389181
  have hstable : (prefixWord ++ tailWord_389181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389181).length < 2 ^ (prefixWord ++ tailWord_389181).sum := by decide
  have hdescent : baseEnd_389181 < baseStart_389181 := by decide
  rcases family_descends (prefixWord ++ tailWord_389181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389182 : List Nat := [4, 2, 1, 3, 2, 2, 1, 3, 5]
def baseStart_389182 : Nat := 118140960795 + 389182 * 2 ^ 59
def prefixEnd_389182 : Nat := 4983230072969 + 3 ^ 40 * 389182 * 2
def baseEnd_389182 : Nat := 22204158675355728592799

theorem tailTrace_389182 : CollatzResearch.WordTrace tailWord_389182 prefixEnd_389182 22204158675355728592799 := by
  unfold tailWord_389182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1774329209508444479875225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9463089117378370559334533 1774329209508444479875225)
  ·
    refine ⟨1330746907131333359906419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1774329209508444479875225 1330746907131333359906419)
    ·
      refine ⟨1996120360697000039859629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330746907131333359906419 1996120360697000039859629)
      ·
        refine ⟨748545135261375014947361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1996120360697000039859629 748545135261375014947361)
        ·
          refine ⟨561408851446031261210521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748545135261375014947361 561408851446031261210521)
          ·
            refine ⟨421056638584523445907891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 561408851446031261210521 421056638584523445907891)
            ·
              refine ⟨631584957876785168861837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421056638584523445907891 631584957876785168861837)
              ·
                refine ⟨236844359203794438323189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 631584957876785168861837 236844359203794438323189)
                ·
                  refine ⟨22204158675355728592799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 236844359203794438323189 22204158675355728592799)
                  ·
                    rfl

theorem cell23_389182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_389182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389182 prefixEnd_389182 := by exact prefixLift 389182
  have htrace : WordTrace (prefixWord ++ tailWord_389182) baseStart_389182 baseEnd_389182 := by
    simpa [prefixWord, tailWord_389182, baseEnd_389182] using wordTrace_append hprefix tailTrace_389182
  have hstable : (prefixWord ++ tailWord_389182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389182).length < 2 ^ (prefixWord ++ tailWord_389182).sum := by decide
  have hdescent : baseEnd_389182 < baseStart_389182 := by decide
  rcases family_descends (prefixWord ++ tailWord_389182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389198 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_389198 : Nat := 118140960795 + 389198 * 2 ^ 59
def prefixEnd_389198 : Nat := 4983230072969 + 3 ^ 40 * 389198 * 2
def baseEnd_389198 : Nat := 199845643768673494735117

theorem tailTrace_389198 : CollatzResearch.WordTrace tailWord_389198 prefixEnd_389198 199845643768673494735117 := by
  unfold tailWord_389198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1774402155501198821448031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9463478162673060381056165 1774402155501198821448031)
  ·
    refine ⟨2661603233251798232172047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1774402155501198821448031 2661603233251798232172047)
    ·
      refine ⟨3992404849877697348258071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2661603233251798232172047 3992404849877697348258071)
      ·
        refine ⟨5988607274816546022387107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3992404849877697348258071 5988607274816546022387107)
        ·
          refine ⟨8982910912224819033580661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5988607274816546022387107 8982910912224819033580661)
          ·
            refine ⟨842147898021076784398187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8982910912224819033580661 842147898021076784398187)
            ·
              refine ⟨1263221847031615176597281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842147898021076784398187 1263221847031615176597281)
              ·
                refine ⟨947416385273711382447961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263221847031615176597281 947416385273711382447961)
                ·
                  refine ⟨710562288955283536835971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 947416385273711382447961 710562288955283536835971)
                  ·
                    refine ⟨1065843433432925305253957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 710562288955283536835971 1065843433432925305253957)
                    ·
                      refine ⟨199845643768673494735117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1065843433432925305253957 199845643768673494735117)
                      ·
                        rfl

theorem cell23_389198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_389198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389198 prefixEnd_389198 := by exact prefixLift 389198
  have htrace : WordTrace (prefixWord ++ tailWord_389198) baseStart_389198 baseEnd_389198 := by
    simpa [prefixWord, tailWord_389198, baseEnd_389198] using wordTrace_append hprefix tailTrace_389198
  have hstable : (prefixWord ++ tailWord_389198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389198).length < 2 ^ (prefixWord ++ tailWord_389198).sum := by decide
  have hdescent : baseEnd_389198 < baseStart_389198 := by decide
  rcases family_descends (prefixWord ++ tailWord_389198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389208 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 3, 4]
def baseStart_389208 : Nat := 118140960795 + 389208 * 2 ^ 59
def prefixEnd_389208 : Nat := 4983230072969 + 3 ^ 40 * 389208 * 2
def baseEnd_389208 : Nat := 66616926191739485203357

theorem tailTrace_389208 : CollatzResearch.WordTrace tailWord_389208 prefixEnd_389208 66616926191739485203357 := by
  unfold tailWord_389208
  simp only [CollatzResearch.WordTrace]
  refine ⟨7097790986986681139724139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9463721315982241519632185 7097790986986681139724139)
  ·
    refine ⟨10646686480480021709586209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7097790986986681139724139 10646686480480021709586209)
    ·
      refine ⟨7985014860360016282189657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10646686480480021709586209 7985014860360016282189657)
      ·
        refine ⟨5988761145270012211642243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7985014860360016282189657 5988761145270012211642243)
        ·
          refine ⟨8983141717905018317463365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5988761145270012211642243 8983141717905018317463365)
          ·
            refine ⟨1684339072107190934524381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8983141717905018317463365 1684339072107190934524381)
            ·
              refine ⟨631627152040196600446643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1684339072107190934524381 631627152040196600446643)
              ·
                refine ⟨947440728060294900669965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631627152040196600446643 947440728060294900669965)
                ·
                  refine ⟨355290273022610587751237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947440728060294900669965 355290273022610587751237)
                  ·
                    refine ⟨66616926191739485203357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 355290273022610587751237 66616926191739485203357)
                    ·
                      rfl

theorem cell23_389208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_389208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389208 prefixEnd_389208 := by exact prefixLift 389208
  have htrace : WordTrace (prefixWord ++ tailWord_389208) baseStart_389208 baseEnd_389208 := by
    simpa [prefixWord, tailWord_389208, baseEnd_389208] using wordTrace_append hprefix tailTrace_389208
  have hstable : (prefixWord ++ tailWord_389208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389208).length < 2 ^ (prefixWord ++ tailWord_389208).sum := by decide
  have hdescent : baseEnd_389208 < baseStart_389208 := by decide
  rcases family_descends (prefixWord ++ tailWord_389208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389282 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_389282 : Nat := 118140960795 + 389282 * 2 ^ 59
def prefixEnd_389282 : Nat := 4983230072969 + 3 ^ 40 * 389282 * 2
def baseEnd_389282 : Nat := 199888776143651166084731

theorem tailTrace_389282 : CollatzResearch.WordTrace tailWord_389282 prefixEnd_389282 199888776143651166084731 := by
  unfold tailWord_389282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3549570243926318229410525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9465520650470181945094733 3549570243926318229410525)
  ·
    refine ⟨1331088841472369336028947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3549570243926318229410525 1331088841472369336028947)
    ·
      refine ⟨1996633262208554004043421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1331088841472369336028947 1996633262208554004043421)
      ·
        refine ⟨748737473328207751516283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1996633262208554004043421 748737473328207751516283)
        ·
          refine ⟨1123106209992311627274425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748737473328207751516283 1123106209992311627274425)
          ·
            refine ⟨842329657494233720455819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1123106209992311627274425 842329657494233720455819)
            ·
              refine ⟨1263494486241350580683729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842329657494233720455819 1263494486241350580683729)
              ·
                refine ⟨947620864681012935512797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263494486241350580683729 947620864681012935512797)
                ·
                  refine ⟨355357824255379850817299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947620864681012935512797 355357824255379850817299)
                  ·
                    refine ⟨533036736383069776225949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 355357824255379850817299 533036736383069776225949)
                    ·
                      refine ⟨199888776143651166084731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 533036736383069776225949 199888776143651166084731)
                      ·
                        rfl

theorem cell23_389282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_389282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389282 prefixEnd_389282 := by exact prefixLift 389282
  have htrace : WordTrace (prefixWord ++ tailWord_389282) baseStart_389282 baseEnd_389282 := by
    simpa [prefixWord, tailWord_389282, baseEnd_389282] using wordTrace_append hprefix tailTrace_389282
  have hstable : (prefixWord ++ tailWord_389282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389282).length < 2 ^ (prefixWord ++ tailWord_389282).sum := by decide
  have hdescent : baseEnd_389282 < baseStart_389282 := by decide
  rcases family_descends (prefixWord ++ tailWord_389282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389298 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_389298 : Nat := 118140960795 + 389298 * 2 ^ 59
def prefixEnd_389298 : Nat := 4983230072969 + 3 ^ 40 * 389298 * 2
def baseEnd_389298 : Nat := 66632330611374367828219

theorem tailTrace_389298 : CollatzResearch.WordTrace tailWord_389298 prefixEnd_389298 66632330611374367828219 := by
  unfold tailWord_389298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3549716135911826912556137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9465909695764871766816365 3549716135911826912556137)
  ·
    refine ⟨2662287101933870184417103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3549716135911826912556137 2662287101933870184417103)
    ·
      refine ⟨3993430652900805276625655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2662287101933870184417103 3993430652900805276625655)
      ·
        refine ⟨5990145979351207914938483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3993430652900805276625655 5990145979351207914938483)
        ·
          refine ⟨8985218969026811872407725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5990145979351207914938483 8985218969026811872407725)
          ·
            refine ⟨3369457113385054452152897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8985218969026811872407725 3369457113385054452152897)
            ·
              refine ⟨2527092835038790839114673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3369457113385054452152897 2527092835038790839114673)
              ·
                refine ⟨1895319626279093129336005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2527092835038790839114673 1895319626279093129336005)
                ·
                  refine ⟨355372429927329961750501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1895319626279093129336005 355372429927329961750501)
                  ·
                    refine ⟨66632330611374367828219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 355372429927329961750501 66632330611374367828219)
                    ·
                      rfl

theorem cell23_389298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_389298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389298 prefixEnd_389298 := by exact prefixLift 389298
  have htrace : WordTrace (prefixWord ++ tailWord_389298) baseStart_389298 baseEnd_389298 := by
    simpa [prefixWord, tailWord_389298, baseEnd_389298] using wordTrace_append hprefix tailTrace_389298
  have hstable : (prefixWord ++ tailWord_389298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389298).length < 2 ^ (prefixWord ++ tailWord_389298).sum := by decide
  have hdescent : baseEnd_389298 < baseStart_389298 := by decide
  rcases family_descends (prefixWord ++ tailWord_389298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389305 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 5, 2, 2]
def baseStart_389305 : Nat := 118140960795 + 389305 * 2 ^ 59
def prefixEnd_389305 : Nat := 4983230072969 + 3 ^ 40 * 389305 * 2
def baseEnd_389305 : Nat := 199900586198704576097125

theorem tailTrace_389305 : CollatzResearch.WordTrace tailWord_389305 prefixEnd_389305 199900586198704576097125 := by
  unfold tailWord_389305
  simp only [CollatzResearch.WordTrace]
  refine ⟨14199119854621947845729369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9466079903081298563819579 14199119854621947845729369)
  ·
    refine ⟨10649339890966460884297027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14199119854621947845729369 10649339890966460884297027)
    ·
      refine ⟨15974009836449691326445541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10649339890966460884297027 15974009836449691326445541)
      ·
        refine ⟨2995126844334317123708539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15974009836449691326445541 2995126844334317123708539)
        ·
          refine ⟨4492690266501475685562809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2995126844334317123708539 4492690266501475685562809)
          ·
            refine ⟨3369517699876106764172107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4492690266501475685562809 3369517699876106764172107)
            ·
              refine ⟨5054276549814160146258161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3369517699876106764172107 5054276549814160146258161)
              ·
                refine ⟨3790707412360620109693621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5054276549814160146258161 3790707412360620109693621)
                ·
                  refine ⟨355378819908808135283777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3790707412360620109693621 355378819908808135283777)
                  ·
                    refine ⟨266534114931606101462833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 355378819908808135283777 266534114931606101462833)
                    ·
                      refine ⟨199900586198704576097125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266534114931606101462833 199900586198704576097125)
                      ·
                        rfl

theorem cell23_389305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_389305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389305 prefixEnd_389305 := by exact prefixLift 389305
  have htrace : WordTrace (prefixWord ++ tailWord_389305) baseStart_389305 baseEnd_389305 := by
    simpa [prefixWord, tailWord_389305, baseEnd_389305] using wordTrace_append hprefix tailTrace_389305
  have hstable : (prefixWord ++ tailWord_389305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389305).length < 2 ^ (prefixWord ++ tailWord_389305).sum := by decide
  have hdescent : baseEnd_389305 < baseStart_389305 := by decide
  rcases family_descends (prefixWord ++ tailWord_389305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389322 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 3, 2, 2]
def baseStart_389322 : Nat := 118140960795 + 389322 * 2 ^ 59
def prefixEnd_389322 : Nat := 4983230072969 + 3 ^ 40 * 389322 * 2
def baseEnd_389322 : Nat := 199909315369831009584547

theorem tailTrace_389322 : CollatzResearch.WordTrace tailWord_389322 prefixEnd_389322 199909315369831009584547 := by
  unfold tailWord_389322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3549934973890089937274555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9466493263706906499398813 3549934973890089937274555)
  ·
    refine ⟨5324902460835134905911833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3549934973890089937274555 5324902460835134905911833)
    ·
      refine ⟨3993676845626351179433875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5324902460835134905911833 3993676845626351179433875)
      ·
        refine ⟨5990515268439526769150813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3993676845626351179433875 5990515268439526769150813)
        ·
          refine ⟨2246443225664822538431555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5990515268439526769150813 2246443225664822538431555)
          ·
            refine ⟨3369664838497233807647333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2246443225664822538431555 3369664838497233807647333)
            ·
              refine ⟨631812157218231338933875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3369664838497233807647333 631812157218231338933875)
              ·
                refine ⟨947718235827347008400813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631812157218231338933875 947718235827347008400813)
                ·
                  refine ⟨355394338435255128150305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947718235827347008400813 355394338435255128150305)
                  ·
                    refine ⟨266545753826441346112729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 355394338435255128150305 266545753826441346112729)
                    ·
                      refine ⟨199909315369831009584547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266545753826441346112729 199909315369831009584547)
                      ·
                        rfl

theorem cell23_389322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_389322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389322 prefixEnd_389322 := by exact prefixLift 389322
  have htrace : WordTrace (prefixWord ++ tailWord_389322) baseStart_389322 baseEnd_389322 := by
    simpa [prefixWord, tailWord_389322, baseEnd_389322] using wordTrace_append hprefix tailTrace_389322
  have hstable : (prefixWord ++ tailWord_389322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389322).length < 2 ^ (prefixWord ++ tailWord_389322).sum := by decide
  have hdescent : baseEnd_389322 < baseStart_389322 := by decide
  rcases family_descends (prefixWord ++ tailWord_389322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389391 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 6]
def baseStart_389391 : Nat := 118140960795 + 389391 * 2 ^ 59
def prefixEnd_389391 : Nat := 4983230072969 + 3 ^ 40 * 389391 * 2
def baseEnd_389391 : Nat := 199944745534991239621729

theorem tailTrace_389391 : CollatzResearch.WordTrace tailWord_389391 prefixEnd_389391 199944745534991239621729 := by
  unfold tailWord_389391
  simp only [CollatzResearch.WordTrace]
  refine ⟨14202256532310384533360027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9468171021540256355573351 14202256532310384533360027)
  ·
    refine ⟨21303384798465576800040041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14202256532310384533360027 21303384798465576800040041)
    ·
      refine ⟨15977538598849182600030031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21303384798465576800040041 15977538598849182600030031)
      ·
        refine ⟨23966307898273773900045047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15977538598849182600030031 23966307898273773900045047)
        ·
          refine ⟨35949461847410660850067571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23966307898273773900045047 35949461847410660850067571)
          ·
            refine ⟨53924192771115991275101357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35949461847410660850067571 53924192771115991275101357)
            ·
              refine ⟨20221572289168496728163009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53924192771115991275101357 20221572289168496728163009)
              ·
                refine ⟨15166179216876372546122257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20221572289168496728163009 15166179216876372546122257)
                ·
                  refine ⟨11374634412657279409591693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15166179216876372546122257 11374634412657279409591693)
                  ·
                    refine ⟨4265487904746479778596885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11374634412657279409591693 4265487904746479778596885)
                    ·
                      refine ⟨199944745534991239621729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4265487904746479778596885 199944745534991239621729)
                      ·
                        rfl

theorem cell23_389391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_389391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389391 prefixEnd_389391 := by exact prefixLift 389391
  have htrace : WordTrace (prefixWord ++ tailWord_389391) baseStart_389391 baseEnd_389391 := by
    simpa [prefixWord, tailWord_389391, baseEnd_389391] using wordTrace_append hprefix tailTrace_389391
  have hstable : (prefixWord ++ tailWord_389391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389391).length < 2 ^ (prefixWord ++ tailWord_389391).sum := by decide
  have hdescent : baseEnd_389391 < baseStart_389391 := by decide
  rcases family_descends (prefixWord ++ tailWord_389391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389399 : List Nat := [1, 1, 3, 4, 1, 4, 1, 2, 1, 3, 2]
def baseStart_389399 : Nat := 118140960795 + 389399 * 2 ^ 59
def prefixEnd_389399 : Nat := 4983230072969 + 3 ^ 40 * 389399 * 2
def baseEnd_389399 : Nat := 199948853380227208321693

theorem tailTrace_389399 : CollatzResearch.WordTrace tailWord_389399 prefixEnd_389399 199948853380227208321693 := by
  unfold tailWord_389399
  simp only [CollatzResearch.WordTrace]
  refine ⟨14202548316281401899651251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9468365544187601266434167 14202548316281401899651251)
  ·
    refine ⟨21303822474422102849476877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14202548316281401899651251 21303822474422102849476877)
    ·
      refine ⟨7988933427908288568553829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21303822474422102849476877 7988933427908288568553829)
      ·
        refine ⟨1497925017732804106603843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7988933427908288568553829 1497925017732804106603843)
        ·
          refine ⟨2246887526599206159905765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1497925017732804106603843 2246887526599206159905765)
          ·
            refine ⟨421291411237351154982331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2246887526599206159905765 421291411237351154982331)
            ·
              refine ⟨631937116856026732473497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421291411237351154982331 631937116856026732473497)
              ·
                refine ⟨473952837642020049355123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631937116856026732473497 473952837642020049355123)
                ·
                  refine ⟨710929256463030074032685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473952837642020049355123 710929256463030074032685)
                  ·
                    refine ⟨266598471173636277762257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 710929256463030074032685 266598471173636277762257)
                    ·
                      refine ⟨199948853380227208321693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266598471173636277762257 199948853380227208321693)
                      ·
                        rfl

theorem cell23_389399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_389399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389399 prefixEnd_389399 := by exact prefixLift 389399
  have htrace : WordTrace (prefixWord ++ tailWord_389399) baseStart_389399 baseEnd_389399 := by
    simpa [prefixWord, tailWord_389399, baseEnd_389399] using wordTrace_append hprefix tailTrace_389399
  have hstable : (prefixWord ++ tailWord_389399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389399).length < 2 ^ (prefixWord ++ tailWord_389399).sum := by decide
  have hdescent : baseEnd_389399 < baseStart_389399 := by decide
  rcases family_descends (prefixWord ++ tailWord_389399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389412 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 1, 4, 2]
def baseStart_389412 : Nat := 118140960795 + 389412 * 2 ^ 59
def prefixEnd_389412 : Nat := 4983230072969 + 3 ^ 40 * 389412 * 2
def baseEnd_389412 : Nat := 199955528628735657459133

theorem tailTrace_389412 : CollatzResearch.WordTrace tailWord_389412 prefixEnd_389412 199955528628735657459133 := by
  unfold tailWord_389412
  simp only [CollatzResearch.WordTrace]
  refine ⟨7101511232617152559937245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9468681643489536746582993 7101511232617152559937245)
  ·
    refine ⟨2663066712231432209976467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7101511232617152559937245 2663066712231432209976467)
    ·
      refine ⟨3994600068347148314964701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2663066712231432209976467 3994600068347148314964701)
      ·
        refine ⟨1497975025630180618111763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3994600068347148314964701 1497975025630180618111763)
        ·
          refine ⟨2246962538445270927167645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1497975025630180618111763 2246962538445270927167645)
          ·
            refine ⟨842610951916976597687867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2246962538445270927167645 842610951916976597687867)
            ·
              refine ⟨1263916427875464896531801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842610951916976597687867 1263916427875464896531801)
              ·
                refine ⟨947937320906598672398851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263916427875464896531801 947937320906598672398851)
                ·
                  refine ⟨1421905981359898008598277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947937320906598672398851 1421905981359898008598277)
                  ·
                    refine ⟨266607371504980876612177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1421905981359898008598277 266607371504980876612177)
                    ·
                      refine ⟨199955528628735657459133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266607371504980876612177 199955528628735657459133)
                      ·
                        rfl

theorem cell23_389412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_389412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389412 prefixEnd_389412 := by exact prefixLift 389412
  have htrace : WordTrace (prefixWord ++ tailWord_389412) baseStart_389412 baseEnd_389412 := by
    simpa [prefixWord, tailWord_389412, baseEnd_389412] using wordTrace_append hprefix tailTrace_389412
  have hstable : (prefixWord ++ tailWord_389412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389412).length < 2 ^ (prefixWord ++ tailWord_389412).sum := by decide
  have hdescent : baseEnd_389412 < baseStart_389412 := by decide
  rcases family_descends (prefixWord ++ tailWord_389412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389416 : List Nat := [2, 1, 5, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_389416 : Nat := 118140960795 + 389416 * 2 ^ 59
def prefixEnd_389416 : Nat := 4983230072969 + 3 ^ 40 * 389416 * 2
def baseEnd_389416 : Nat := 199957582551353641809115

theorem tailTrace_389416 : CollatzResearch.WordTrace tailWord_389416 prefixEnd_389416 199957582551353641809115 := by
  unfold tailWord_389416
  simp only [CollatzResearch.WordTrace]
  refine ⟨7101584178609906901510051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9468778904813209202013401 7101584178609906901510051)
  ·
    refine ⟨10652376267914860352265077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7101584178609906901510051 10652376267914860352265077)
    ·
      refine ⟨998660275117018158024851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10652376267914860352265077 998660275117018158024851)
      ·
        refine ⟨1497990412675527237037277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998660275117018158024851 1497990412675527237037277)
        ·
          refine ⟨561746404753322713888979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1497990412675527237037277 561746404753322713888979)
          ·
            refine ⟨842619607129984070833469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561746404753322713888979 842619607129984070833469)
            ·
              refine ⟨315982352673744026562551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 842619607129984070833469 315982352673744026562551)
              ·
                refine ⟨473973529010616039843827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315982352673744026562551 473973529010616039843827)
                ·
                  refine ⟨710960293515924059765741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473973529010616039843827 710960293515924059765741)
                  ·
                    refine ⟨266610110068471522412153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 710960293515924059765741 266610110068471522412153)
                    ·
                      refine ⟨199957582551353641809115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266610110068471522412153 199957582551353641809115)
                      ·
                        rfl

theorem cell23_389416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_389416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389416 prefixEnd_389416 := by exact prefixLift 389416
  have htrace : WordTrace (prefixWord ++ tailWord_389416) baseStart_389416 baseEnd_389416 := by
    simpa [prefixWord, tailWord_389416, baseEnd_389416] using wordTrace_append hprefix tailTrace_389416
  have hstable : (prefixWord ++ tailWord_389416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389416).length < 2 ^ (prefixWord ++ tailWord_389416).sum := by decide
  have hdescent : baseEnd_389416 < baseStart_389416 := by decide
  rcases family_descends (prefixWord ++ tailWord_389416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389429 : List Nat := [1, 3, 3, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_389429 : Nat := 118140960795 + 389429 * 2 ^ 59
def prefixEnd_389429 : Nat := 4983230072969 + 3 ^ 40 * 389429 * 2
def baseEnd_389429 : Nat := 199964257799862090946555

theorem tailTrace_389429 : CollatzResearch.WordTrace tailWord_389429 prefixEnd_389429 199964257799862090946555 := by
  unfold tailWord_389429
  simp only [CollatzResearch.WordTrace]
  refine ⟨14203642506172717023243341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9469095004115144682162227 14203642506172717023243341)
  ·
    refine ⟨5326365939814768883716253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14203642506172717023243341 5326365939814768883716253)
    ·
      refine ⟨1997387227430538331393595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5326365939814768883716253 1997387227430538331393595)
      ·
        refine ⟨2996080841145807497090393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997387227430538331393595 2996080841145807497090393)
        ·
          refine ⟨2247060630859355622817795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2996080841145807497090393 2247060630859355622817795)
          ·
            refine ⟨3370590946289033434226693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247060630859355622817795 3370590946289033434226693)
            ·
              refine ⟨631985802429193768917505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3370590946289033434226693 631985802429193768917505)
              ·
                refine ⟨473989351821895326688129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631985802429193768917505 473989351821895326688129)
                ·
                  refine ⟨355492013866421495016097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473989351821895326688129 355492013866421495016097)
                  ·
                    refine ⟨266619010399816121262073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 355492013866421495016097 266619010399816121262073)
                    ·
                      refine ⟨199964257799862090946555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266619010399816121262073 199964257799862090946555)
                      ·
                        rfl

theorem cell23_389429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_389429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389429 prefixEnd_389429 := by exact prefixLift 389429
  have htrace : WordTrace (prefixWord ++ tailWord_389429) baseStart_389429 baseEnd_389429 := by
    simpa [prefixWord, tailWord_389429, baseEnd_389429] using wordTrace_append hprefix tailTrace_389429
  have hstable : (prefixWord ++ tailWord_389429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389429).length < 2 ^ (prefixWord ++ tailWord_389429).sum := by decide
  have hdescent : baseEnd_389429 < baseStart_389429 := by decide
  rcases family_descends (prefixWord ++ tailWord_389429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389448 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 4, 5]
def baseStart_389448 : Nat := 118140960795 + 389448 * 2 ^ 59
def prefixEnd_389448 : Nat := 4983230072969 + 3 ^ 40 * 389448 * 2
def baseEnd_389448 : Nat := 66658004644099172202989

theorem tailTrace_389448 : CollatzResearch.WordTrace tailWord_389448 prefixEnd_389448 66658004644099172202989 := by
  unfold tailWord_389448
  simp only [CollatzResearch.WordTrace]
  refine ⟨7102167746551941634092499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9469556995402588845456665 7102167746551941634092499)
  ·
    refine ⟨10653251619827912451138749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7102167746551941634092499 10653251619827912451138749)
    ·
      refine ⟨3994969357435467169177031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10653251619827912451138749 3994969357435467169177031)
      ·
        refine ⟨5992454036153200753765547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3994969357435467169177031 5992454036153200753765547)
        ·
          refine ⟨8988681054229801130648321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5992454036153200753765547 8988681054229801130648321)
          ·
            refine ⟨6741510790672350847986241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8988681054229801130648321 6741510790672350847986241)
            ·
              refine ⟨5056133093004263135989681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6741510790672350847986241 5056133093004263135989681)
              ·
                refine ⟨3792099819753197351992261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5056133093004263135989681 3792099819753197351992261)
                ·
                  refine ⟨711018716203724503498549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3792099819753197351992261 711018716203724503498549)
                  ·
                    refine ⟨66658004644099172202989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 711018716203724503498549 66658004644099172202989)
                    ·
                      rfl

theorem cell23_389448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_389448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389448 prefixEnd_389448 := by exact prefixLift 389448
  have htrace : WordTrace (prefixWord ++ tailWord_389448) baseStart_389448 baseEnd_389448 := by
    simpa [prefixWord, tailWord_389448, baseEnd_389448] using wordTrace_append hprefix tailTrace_389448
  have hstable : (prefixWord ++ tailWord_389448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389448).length < 2 ^ (prefixWord ++ tailWord_389448).sum := by decide
  have hdescent : baseEnd_389448 < baseStart_389448 := by decide
  rcases family_descends (prefixWord ++ tailWord_389448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389458 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_389458 : Nat := 118140960795 + 389458 * 2 ^ 59
def prefixEnd_389458 : Nat := 4983230072969 + 3 ^ 40 * 389458 * 2
def baseEnd_389458 : Nat := 199979148738842477483921

theorem tailTrace_389458 : CollatzResearch.WordTrace tailWord_389458 prefixEnd_389458 199979148738842477483921 := by
  unfold tailWord_389458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3551175055766913744012257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9469800148711769984032685 3551175055766913744012257)
  ·
    refine ⟨2663381291825185308009193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3551175055766913744012257 2663381291825185308009193)
    ·
      refine ⟨1997535968868888981006895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2663381291825185308009193 1997535968868888981006895)
      ·
        refine ⟨2996303953303333471510343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997535968868888981006895 2996303953303333471510343)
        ·
          refine ⟨4494455929955000207265515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996303953303333471510343 4494455929955000207265515)
          ·
            refine ⟨6741683894932500310898273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4494455929955000207265515 6741683894932500310898273)
            ·
              refine ⟨5056262921199375233173705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6741683894932500310898273 5056262921199375233173705)
              ·
                refine ⟨3792197190899531424880279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5056262921199375233173705 3792197190899531424880279)
                ·
                  refine ⟨5688295786349297137320419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792197190899531424880279 5688295786349297137320419)
                  ·
                    refine ⟨8532443679523945705980629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5688295786349297137320419 8532443679523945705980629)
                    ·
                      refine ⟨199979148738842477483921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8532443679523945705980629 199979148738842477483921)
                      ·
                        rfl

theorem cell23_389458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_389458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389458 prefixEnd_389458 := by exact prefixLift 389458
  have htrace : WordTrace (prefixWord ++ tailWord_389458) baseStart_389458 baseEnd_389458 := by
    simpa [prefixWord, tailWord_389458, baseEnd_389458] using wordTrace_append hprefix tailTrace_389458
  have hstable : (prefixWord ++ tailWord_389458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389458).length < 2 ^ (prefixWord ++ tailWord_389458).sum := by decide
  have hdescent : baseEnd_389458 < baseStart_389458 := by decide
  rcases family_descends (prefixWord ++ tailWord_389458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389485 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_389485 : Nat := 118140960795 + 389485 * 2 ^ 59
def prefixEnd_389485 : Nat := 4983230072969 + 3 ^ 40 * 389485 * 2
def baseEnd_389485 : Nat := 199993012716513871846297

theorem tailTrace_389485 : CollatzResearch.WordTrace tailWord_389485 prefixEnd_389485 199993012716513871846297 := by
  unfold tailWord_389485
  simp only [CollatzResearch.WordTrace]
  refine ⟨14205684993969838587281909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9470456662646559058187939 14205684993969838587281909)
  ·
    refine ⟨1331782968184672367557679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14205684993969838587281909 1331782968184672367557679)
    ·
      refine ⟨1997674452277008551336519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1331782968184672367557679 1997674452277008551336519)
      ·
        refine ⟨2996511678415512827004779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997674452277008551336519 2996511678415512827004779)
        ·
          refine ⟨4494767517623269240507169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996511678415512827004779 4494767517623269240507169)
          ·
            refine ⟨3371075638217451930380377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4494767517623269240507169 3371075638217451930380377)
            ·
              refine ⟨2528306728663088947785283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3371075638217451930380377 2528306728663088947785283)
              ·
                refine ⟨3792460092994633421677925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2528306728663088947785283 3792460092994633421677925)
                ·
                  refine ⟨711086267436493766564611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3792460092994633421677925 711086267436493766564611)
                  ·
                    refine ⟨1066629401154740649846917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 711086267436493766564611 1066629401154740649846917)
                    ·
                      refine ⟨199993012716513871846297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1066629401154740649846917 199993012716513871846297)
                      ·
                        rfl

theorem cell23_389485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_389485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389485 prefixEnd_389485 := by exact prefixLift 389485
  have htrace : WordTrace (prefixWord ++ tailWord_389485) baseStart_389485 baseEnd_389485 := by
    simpa [prefixWord, tailWord_389485, baseEnd_389485] using wordTrace_append hprefix tailTrace_389485
  have hstable : (prefixWord ++ tailWord_389485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389485).length < 2 ^ (prefixWord ++ tailWord_389485).sum := by decide
  have hdescent : baseEnd_389485 < baseStart_389485 := by decide
  rcases family_descends (prefixWord ++ tailWord_389485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389498 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_389498 : Nat := 118140960795 + 389498 * 2 ^ 59
def prefixEnd_389498 : Nat := 4983230072969 + 3 ^ 40 * 389498 * 2
def baseEnd_389498 : Nat := 199999687965022320983737

theorem tailTrace_389498 : CollatzResearch.WordTrace tailWord_389498 prefixEnd_389498 199999687965022320983737 := by
  unfold tailWord_389498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3551539785730685451876287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9470772761948494538336765 3551539785730685451876287)
  ·
    refine ⟨5327309678596028177814431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3551539785730685451876287 5327309678596028177814431)
    ·
      refine ⟨7990964517894042266721647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5327309678596028177814431 7990964517894042266721647)
      ·
        refine ⟨11986446776841063400082471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7990964517894042266721647 11986446776841063400082471)
        ·
          refine ⟨17979670165261595100123707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11986446776841063400082471 17979670165261595100123707)
          ·
            refine ⟨26969505247892392650185561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17979670165261595100123707 26969505247892392650185561)
            ·
              refine ⟨20227128935919294487639171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26969505247892392650185561 20227128935919294487639171)
              ·
                refine ⟨30340693403878941731458757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20227128935919294487639171 30340693403878941731458757)
                ·
                  refine ⟨5688880013227301574648517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30340693403878941731458757 5688880013227301574648517)
                  ·
                    refine ⟨1066665002480119045246597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5688880013227301574648517 1066665002480119045246597)
                    ·
                      refine ⟨199999687965022320983737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1066665002480119045246597 199999687965022320983737)
                      ·
                        rfl

theorem cell23_389498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_389498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389498 prefixEnd_389498 := by exact prefixLift 389498
  have htrace : WordTrace (prefixWord ++ tailWord_389498) baseStart_389498 baseEnd_389498 := by
    simpa [prefixWord, tailWord_389498, baseEnd_389498] using wordTrace_append hprefix tailTrace_389498
  have hstable : (prefixWord ++ tailWord_389498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389498).length < 2 ^ (prefixWord ++ tailWord_389498).sum := by decide
  have hdescent : baseEnd_389498 < baseStart_389498 := by decide
  rcases family_descends (prefixWord ++ tailWord_389498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389548 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_389548 : Nat := 118140960795 + 389548 * 2 ^ 59
def prefixEnd_389548 : Nat := 4983230072969 + 3 ^ 40 * 389548 * 2
def baseEnd_389548 : Nat := 200025361997747125358507

theorem tailTrace_389548 : CollatzResearch.WordTrace tailWord_389548 prefixEnd_389548 200025361997747125358507 := by
  unfold tailWord_389548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7103991396370800173412649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9471988528494400231216865 7103991396370800173412649)
  ·
    refine ⟨5327993547278100130059487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7103991396370800173412649 5327993547278100130059487)
    ·
      refine ⟨7991990320917150195089231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5327993547278100130059487 7991990320917150195089231)
      ·
        refine ⟨11987985481375725292633847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7991990320917150195089231 11987985481375725292633847)
        ·
          refine ⟨17981978222063587938950771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11987985481375725292633847 17981978222063587938950771)
          ·
            refine ⟨26972967333095381908426157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17981978222063587938950771 26972967333095381908426157)
            ·
              refine ⟨10114862749910768215659809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26972967333095381908426157 10114862749910768215659809)
              ·
                refine ⟨7586147062433076161744857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10114862749910768215659809 7586147062433076161744857)
                ·
                  refine ⟨5689610296824807121308643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7586147062433076161744857 5689610296824807121308643)
                  ·
                    refine ⟨8534415445237210681962965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5689610296824807121308643 8534415445237210681962965)
                    ·
                      refine ⟨200025361997747125358507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8534415445237210681962965 200025361997747125358507)
                      ·
                        rfl

theorem cell23_389548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_389548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389548 prefixEnd_389548 := by exact prefixLift 389548
  have htrace : WordTrace (prefixWord ++ tailWord_389548) baseStart_389548 baseEnd_389548 := by
    simpa [prefixWord, tailWord_389548, baseEnd_389548] using wordTrace_append hprefix tailTrace_389548
  have hstable : (prefixWord ++ tailWord_389548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389548).length < 2 ^ (prefixWord ++ tailWord_389548).sum := by decide
  have hdescent : baseEnd_389548 < baseStart_389548 := by decide
  rcases family_descends (prefixWord ++ tailWord_389548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389585 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 6, 4]
def baseStart_389585 : Nat := 118140960795 + 389585 * 2 ^ 59
def prefixEnd_389585 : Nat := 4983230072969 + 3 ^ 40 * 389585 * 2
def baseEnd_389585 : Nat := 66681453593987826865279

theorem tailTrace_389585 : CollatzResearch.WordTrace tailWord_389585 prefixEnd_389585 66681453593987826865279 := by
  unfold tailWord_389585
  simp only [CollatzResearch.WordTrace]
  refine ⟨14209332293607555665922209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9472888195738370443948139 14209332293607555665922209)
  ·
    refine ⟨10656999220205666749441657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14209332293607555665922209 10656999220205666749441657)
    ·
      refine ⟨7992749415154250062081243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10656999220205666749441657 7992749415154250062081243)
      ·
        refine ⟨11989124122731375093121865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7992749415154250062081243 11989124122731375093121865)
        ·
          refine ⟨8991843092048531319841399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11989124122731375093121865 8991843092048531319841399)
          ·
            refine ⟨13487764638072796979762099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8991843092048531319841399 13487764638072796979762099)
            ·
              refine ⟨20231646957109195469643149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13487764638072796979762099 20231646957109195469643149)
              ·
                refine ⟨7586867608915948301116181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20231646957109195469643149 7586867608915948301116181)
                ·
                  refine ⟨355634419167935076614821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7586867608915948301116181 355634419167935076614821)
                  ·
                    refine ⟨66681453593987826865279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 355634419167935076614821 66681453593987826865279)
                    ·
                      rfl

theorem cell23_389585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_389585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389585 prefixEnd_389585 := by exact prefixLift 389585
  have htrace : WordTrace (prefixWord ++ tailWord_389585) baseStart_389585 baseEnd_389585 := by
    simpa [prefixWord, tailWord_389585, baseEnd_389585] using wordTrace_append hprefix tailTrace_389585
  have hstable : (prefixWord ++ tailWord_389585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389585).length < 2 ^ (prefixWord ++ tailWord_389585).sum := by decide
  have hdescent : baseEnd_389585 < baseStart_389585 := by decide
  rcases family_descends (prefixWord ++ tailWord_389585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389589 : List Nat := [1, 3, 2, 3, 1, 3, 3, 1, 1, 5]
def baseStart_389589 : Nat := 118140960795 + 389589 * 2 ^ 59
def prefixEnd_389589 : Nat := 4983230072969 + 3 ^ 40 * 389589 * 2
def baseEnd_389589 : Nat := 66682138234860488315273

theorem tailTrace_389589 : CollatzResearch.WordTrace tailWord_389589 prefixEnd_389589 66682138234860488315273 := by
  unfold tailWord_389589
  simp only [CollatzResearch.WordTrace]
  refine ⟨14209478185593064349067821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9472985457062042899378547 14209478185593064349067821)
  ·
    refine ⟨5328554319597399130900433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14209478185593064349067821 5328554319597399130900433)
    ·
      refine ⟨3996415739698049348175325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5328554319597399130900433 3996415739698049348175325)
      ·
        refine ⟨1498655902386768505565747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3996415739698049348175325 1498655902386768505565747)
        ·
          refine ⟨2247983853580152758348621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498655902386768505565747 2247983853580152758348621)
          ·
            refine ⟨842993945092557284380733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2247983853580152758348621 842993945092557284380733)
            ·
              refine ⟨316122729409708981642775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 842993945092557284380733 316122729409708981642775)
              ·
                refine ⟨474184094114563472464163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316122729409708981642775 474184094114563472464163)
                ·
                  refine ⟨711276141171845208696245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474184094114563472464163 711276141171845208696245)
                  ·
                    refine ⟨66682138234860488315273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 711276141171845208696245 66682138234860488315273)
                    ·
                      rfl

theorem cell23_389589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_389589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389589 prefixEnd_389589 := by exact prefixLift 389589
  have htrace : WordTrace (prefixWord ++ tailWord_389589) baseStart_389589 baseEnd_389589 := by
    simpa [prefixWord, tailWord_389589, baseEnd_389589] using wordTrace_append hprefix tailTrace_389589
  have hstable : (prefixWord ++ tailWord_389589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389589).length < 2 ^ (prefixWord ++ tailWord_389589).sum := by decide
  have hdescent : baseEnd_389589 < baseStart_389589 := by decide
  rcases family_descends (prefixWord ++ tailWord_389589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389642 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_389642 : Nat := 118140960795 + 389642 * 2 ^ 59
def prefixEnd_389642 : Nat := 4983230072969 + 3 ^ 40 * 389642 * 2
def baseEnd_389642 : Nat := 200073629179269757583075

theorem tailTrace_389642 : CollatzResearch.WordTrace tailWord_389642 prefixEnd_389642 200073629179269757583075 := by
  unfold tailWord_389642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552852813600263600186795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9474274169600702933831453 3552852813600263600186795)
  ·
    refine ⟨5329279220400395400280193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3552852813600263600186795 5329279220400395400280193)
    ·
      refine ⟨3996959415300296550210145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5329279220400395400280193 3996959415300296550210145)
      ·
        refine ⟨2997719561475222412657609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3996959415300296550210145 2997719561475222412657609)
        ·
          refine ⟨2248289671106416809493207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2997719561475222412657609 2248289671106416809493207)
          ·
            refine ⟨3372434506659625214239811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248289671106416809493207 3372434506659625214239811)
            ·
              refine ⟨5058651759989437821359717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3372434506659625214239811 5058651759989437821359717)
              ·
                refine ⟨948497204998019591504947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5058651759989437821359717 948497204998019591504947)
                ·
                  refine ⟨1422745807497029387257421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948497204998019591504947 1422745807497029387257421)
                  ·
                    refine ⟨533529677811386020221533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1422745807497029387257421 533529677811386020221533)
                    ·
                      refine ⟨200073629179269757583075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 533529677811386020221533 200073629179269757583075)
                      ·
                        rfl

theorem cell23_389642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_389642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389642 prefixEnd_389642 := by exact prefixLift 389642
  have htrace : WordTrace (prefixWord ++ tailWord_389642) baseStart_389642 baseEnd_389642 := by
    simpa [prefixWord, tailWord_389642, baseEnd_389642] using wordTrace_append hprefix tailTrace_389642
  have hstable : (prefixWord ++ tailWord_389642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389642).length < 2 ^ (prefixWord ++ tailWord_389642).sum := by decide
  have hdescent : baseEnd_389642 < baseStart_389642 := by decide
  rcases family_descends (prefixWord ++ tailWord_389642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389643 : List Nat := [1, 1, 1, 1, 7, 2, 2, 3, 1, 2, 2]
def baseStart_389643 : Nat := 118140960795 + 389643 * 2 ^ 59
def prefixEnd_389643 : Nat := 4983230072969 + 3 ^ 40 * 389643 * 2
def baseEnd_389643 : Nat := 200074142659924253670571

theorem tailTrace_389643 : CollatzResearch.WordTrace tailWord_389643 prefixEnd_389643 200074142659924253670571 := by
  unfold tailWord_389643
  simp only [CollatzResearch.WordTrace]
  refine ⟨14211447727397431571533583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9474298484931621047689055 14211447727397431571533583)
  ·
    refine ⟨21317171591096147357300375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14211447727397431571533583 21317171591096147357300375)
    ·
      refine ⟨31975757386644221035950563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21317171591096147357300375 31975757386644221035950563)
      ·
        refine ⟨47963636079966331553925845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31975757386644221035950563 47963636079966331553925845)
        ·
          refine ⟨1124147720624210895795137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 47963636079966331553925845 1124147720624210895795137)
          ·
            refine ⟨843110790468158171846353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1124147720624210895795137 843110790468158171846353)
            ·
              refine ⟨632333092851118628884765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843110790468158171846353 632333092851118628884765)
              ·
                refine ⟨237124909819169485831787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 632333092851118628884765 237124909819169485831787)
                ·
                  refine ⟨355687364728754228747681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237124909819169485831787 355687364728754228747681)
                  ·
                    refine ⟨266765523546565671560761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 355687364728754228747681 266765523546565671560761)
                    ·
                      refine ⟨200074142659924253670571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266765523546565671560761 200074142659924253670571)
                      ·
                        rfl

theorem cell23_389643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 1, 2, 2].length) (baseStart_389643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389643 prefixEnd_389643 := by exact prefixLift 389643
  have htrace : WordTrace (prefixWord ++ tailWord_389643) baseStart_389643 baseEnd_389643 := by
    simpa [prefixWord, tailWord_389643, baseEnd_389643] using wordTrace_append hprefix tailTrace_389643
  have hstable : (prefixWord ++ tailWord_389643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389643).length < 2 ^ (prefixWord ++ tailWord_389643).sum := by decide
  have hdescent : baseEnd_389643 < baseStart_389643 := by decide
  rcases family_descends (prefixWord ++ tailWord_389643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389646 : List Nat := [4, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3]
def baseStart_389646 : Nat := 118140960795 + 389646 * 2 ^ 59
def prefixEnd_389646 : Nat := 4983230072969 + 3 ^ 40 * 389646 * 2
def baseEnd_389646 : Nat := 200075683101887741933057

theorem tailTrace_389646 : CollatzResearch.WordTrace tailWord_389646 prefixEnd_389646 200075683101887741933057 := by
  unfold tailWord_389646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1776444643298320385486599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9474371430924375389261861 1776444643298320385486599)
  ·
    refine ⟨2664666964947480578229899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1776444643298320385486599 2664666964947480578229899)
    ·
      refine ⟨3997000447421220867344849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2664666964947480578229899 3997000447421220867344849)
      ·
        refine ⟨2997750335565915650508637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3997000447421220867344849 2997750335565915650508637)
        ·
          refine ⟨1124156375837218368940739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2997750335565915650508637 1124156375837218368940739)
          ·
            refine ⟨1686234563755827553411109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124156375837218368940739 1686234563755827553411109)
            ·
              refine ⟨316168980704217666264583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1686234563755827553411109 316168980704217666264583)
              ·
                refine ⟨474253471056326499396875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316168980704217666264583 474253471056326499396875)
                ·
                  refine ⟨711380206584489749095313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474253471056326499396875 711380206584489749095313)
                  ·
                    refine ⟨533535154938367311821485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 711380206584489749095313 533535154938367311821485)
                    ·
                      refine ⟨200075683101887741933057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 533535154938367311821485 200075683101887741933057)
                      ·
                        rfl

theorem cell23_389646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_389646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389646 prefixEnd_389646 := by exact prefixLift 389646
  have htrace : WordTrace (prefixWord ++ tailWord_389646) baseStart_389646 baseEnd_389646 := by
    simpa [prefixWord, tailWord_389646, baseEnd_389646] using wordTrace_append hprefix tailTrace_389646
  have hstable : (prefixWord ++ tailWord_389646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389646).length < 2 ^ (prefixWord ++ tailWord_389646).sum := by decide
  have hdescent : baseEnd_389646 < baseStart_389646 := by decide
  rcases family_descends (prefixWord ++ tailWord_389646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389694 : List Nat := [4, 2, 1, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_389694 : Nat := 118140960795 + 389694 * 2 ^ 59
def prefixEnd_389694 : Nat := 4983230072969 + 3 ^ 40 * 389694 * 2
def baseEnd_389694 : Nat := 200100330173303554132837

theorem tailTrace_389694 : CollatzResearch.WordTrace tailWord_389694 prefixEnd_389694 200100330173303554132837 := by
  unfold tailWord_389694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1776663481276583410205017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9475538566808444854426757 1776663481276583410205017)
  ·
    refine ⟨1332497610957437557653763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1776663481276583410205017 1332497610957437557653763)
    ·
      refine ⟨1998746416436156336480645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1332497610957437557653763 1998746416436156336480645)
      ·
        refine ⟨374764953081779313090121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1998746416436156336480645 374764953081779313090121)
        ·
          refine ⟨281073714811334484817591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374764953081779313090121 281073714811334484817591)
          ·
            refine ⟨421610572217001727226387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281073714811334484817591 421610572217001727226387)
            ·
              refine ⟨632415858325502590839581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421610572217001727226387 632415858325502590839581)
              ·
                refine ⟨237155946872063471564843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 632415858325502590839581 237155946872063471564843)
                ·
                  refine ⟨355733920308095207347265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237155946872063471564843 355733920308095207347265)
                  ·
                    refine ⟨266800440231071405510449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 355733920308095207347265 266800440231071405510449)
                    ·
                      refine ⟨200100330173303554132837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266800440231071405510449 200100330173303554132837)
                      ·
                        rfl

theorem cell23_389694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_389694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389694 prefixEnd_389694 := by exact prefixLift 389694
  have htrace : WordTrace (prefixWord ++ tailWord_389694) baseStart_389694 baseEnd_389694 := by
    simpa [prefixWord, tailWord_389694, baseEnd_389694] using wordTrace_append hprefix tailTrace_389694
  have hstable : (prefixWord ++ tailWord_389694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389694).length < 2 ^ (prefixWord ++ tailWord_389694).sum := by decide
  have hdescent : baseEnd_389694 < baseStart_389694 := by decide
  rcases family_descends (prefixWord ++ tailWord_389694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389716 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_389716 : Nat := 118140960795 + 389716 * 2 ^ 59
def prefixEnd_389716 : Nat := 4983230072969 + 3 ^ 40 * 389716 * 2
def baseEnd_389716 : Nat := 200111626747702468057735

theorem tailTrace_389716 : CollatzResearch.WordTrace tailWord_389716 prefixEnd_389716 200111626747702468057735 := by
  unfold tailWord_389716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7107055128066482519470501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9476073504088643359294001 7107055128066482519470501)
  ·
    refine ⟨1332572836512465472400719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7107055128066482519470501 1332572836512465472400719)
    ·
      refine ⟨1998859254768698208601079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1332572836512465472400719 1998859254768698208601079)
      ·
        refine ⟨2998288882153047312901619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1998859254768698208601079 2998288882153047312901619)
        ·
          refine ⟨4497433323229570969352429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2998288882153047312901619 4497433323229570969352429)
          ·
            refine ⟨1686537496211089113507161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4497433323229570969352429 1686537496211089113507161)
            ·
              refine ⟨1264903122158316835130371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1686537496211089113507161 1264903122158316835130371)
              ·
                refine ⟨1897354683237475252695557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264903122158316835130371 1897354683237475252695557)
                ·
                  refine ⟨355754003107026609880417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1897354683237475252695557 355754003107026609880417)
                  ·
                    refine ⟨266815502330269957410313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 355754003107026609880417 266815502330269957410313)
                    ·
                      refine ⟨200111626747702468057735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266815502330269957410313 200111626747702468057735)
                      ·
                        rfl

theorem cell23_389716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_389716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389716 prefixEnd_389716 := by exact prefixLift 389716
  have htrace : WordTrace (prefixWord ++ tailWord_389716) baseStart_389716 baseEnd_389716 := by
    simpa [prefixWord, tailWord_389716, baseEnd_389716] using wordTrace_append hprefix tailTrace_389716
  have hstable : (prefixWord ++ tailWord_389716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389716).length < 2 ^ (prefixWord ++ tailWord_389716).sum := by decide
  have hdescent : baseEnd_389716 < baseStart_389716 := by decide
  rcases family_descends (prefixWord ++ tailWord_389716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389732 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_389732 : Nat := 118140960795 + 389732 * 2 ^ 59
def prefixEnd_389732 : Nat := 4983230072969 + 3 ^ 40 * 389732 * 2
def baseEnd_389732 : Nat := 200119842438174405457661

theorem tailTrace_389732 : CollatzResearch.WordTrace tailWord_389732 prefixEnd_389732 200119842438174405457661 := by
  unfold tailWord_389732
  simp only [CollatzResearch.WordTrace]
  refine ⟨7107346912037499885761725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9476462549383333181015633 7107346912037499885761725)
  ·
    refine ⟨2665255092014062457160647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7107346912037499885761725 2665255092014062457160647)
    ·
      refine ⟨3997882638021093685740971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2665255092014062457160647 3997882638021093685740971)
      ·
        refine ⟨5996823957031640528611457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3997882638021093685740971 5996823957031640528611457)
        ·
          refine ⟨4497617967773730396458593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5996823957031640528611457 4497617967773730396458593)
          ·
            refine ⟨3373213475830297797343945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4497617967773730396458593 3373213475830297797343945)
            ·
              refine ⟨2529910106872723348007959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3373213475830297797343945 2529910106872723348007959)
              ·
                refine ⟨3794865160309085022011939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529910106872723348007959 3794865160309085022011939)
                ·
                  refine ⟨5692297740463627533017909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794865160309085022011939 5692297740463627533017909)
                  ·
                    refine ⟨533652913168465081220429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5692297740463627533017909 533652913168465081220429)
                    ·
                      refine ⟨200119842438174405457661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 533652913168465081220429 200119842438174405457661)
                      ·
                        rfl

theorem cell23_389732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_389732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389732 prefixEnd_389732 := by exact prefixLift 389732
  have htrace : WordTrace (prefixWord ++ tailWord_389732) baseStart_389732 baseEnd_389732 := by
    simpa [prefixWord, tailWord_389732, baseEnd_389732] using wordTrace_append hprefix tailTrace_389732
  have hstable : (prefixWord ++ tailWord_389732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389732).length < 2 ^ (prefixWord ++ tailWord_389732).sum := by decide
  have hdescent : baseEnd_389732 < baseStart_389732 := by decide
  rcases family_descends (prefixWord ++ tailWord_389732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389733 : List Nat := [1, 3, 1, 3, 4, 1, 1, 3, 2, 2, 2]
def baseStart_389733 : Nat := 118140960795 + 389733 * 2 ^ 59
def prefixEnd_389733 : Nat := 4983230072969 + 3 ^ 40 * 389733 * 2
def baseEnd_389733 : Nat := 200120355918828901545157

theorem tailTrace_389733 : CollatzResearch.WordTrace tailWord_389733 prefixEnd_389733 200120355918828901545157 := by
  unfold tailWord_389733
  simp only [CollatzResearch.WordTrace]
  refine ⟨14214730297071376942309853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9476486864714251294873235 14214730297071376942309853)
  ·
    refine ⟨5330523861401766353366195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14214730297071376942309853 5330523861401766353366195)
    ·
      refine ⟨7995785792102649530049293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5330523861401766353366195 7995785792102649530049293)
      ·
        refine ⟨2998419672038493573768485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7995785792102649530049293 2998419672038493573768485)
        ·
          refine ⟨562203688507217545081591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2998419672038493573768485 562203688507217545081591)
          ·
            refine ⟨843305532760826317622387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562203688507217545081591 843305532760826317622387)
            ·
              refine ⟨1264958299141239476433581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 843305532760826317622387 1264958299141239476433581)
              ·
                refine ⟨474359362177964803662593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1264958299141239476433581 474359362177964803662593)
                ·
                  refine ⟨355769521633473602746945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474359362177964803662593 355769521633473602746945)
                  ·
                    refine ⟨266827141225105202060209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 355769521633473602746945 266827141225105202060209)
                    ·
                      refine ⟨200120355918828901545157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266827141225105202060209 200120355918828901545157)
                      ·
                        rfl

theorem cell23_389733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_389733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389733 prefixEnd_389733 := by exact prefixLift 389733
  have htrace : WordTrace (prefixWord ++ tailWord_389733) baseStart_389733 baseEnd_389733 := by
    simpa [prefixWord, tailWord_389733, baseEnd_389733] using wordTrace_append hprefix tailTrace_389733
  have hstable : (prefixWord ++ tailWord_389733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389733).length < 2 ^ (prefixWord ++ tailWord_389733).sum := by decide
  have hdescent : baseEnd_389733 < baseStart_389733 := by decide
  rcases family_descends (prefixWord ++ tailWord_389733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389772 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_389772 : Nat := 118140960795 + 389772 * 2 ^ 59
def prefixEnd_389772 : Nat := 4983230072969 + 3 ^ 40 * 389772 * 2
def baseEnd_389772 : Nat := 200140381664354248957477

theorem tailTrace_389772 : CollatzResearch.WordTrace tailWord_389772 prefixEnd_389772 200140381664354248957477 := by
  unfold tailWord_389772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7108076371965043301489785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9477435162620057735319713 7108076371965043301489785)
  ·
    refine ⟨5331057278973782476117339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7108076371965043301489785 5331057278973782476117339)
    ·
      refine ⟨7996585918460673714176009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5331057278973782476117339 7996585918460673714176009)
      ·
        refine ⟨5997439438845505285632007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7996585918460673714176009 5997439438845505285632007)
        ·
          refine ⟨8996159158268257928448011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5997439438845505285632007 8996159158268257928448011)
          ·
            refine ⟨13494238737402386892672017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8996159158268257928448011 13494238737402386892672017)
            ·
              refine ⟨10120679053051790169504013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13494238737402386892672017 10120679053051790169504013)
              ·
                refine ⟨3795254644894421313564005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10120679053051790169504013 3795254644894421313564005)
                ·
                  refine ⟨711610245917703996293251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3795254644894421313564005 711610245917703996293251)
                  ·
                    refine ⟨1067415368876555994439877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 711610245917703996293251 1067415368876555994439877)
                    ·
                      refine ⟨200140381664354248957477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1067415368876555994439877 200140381664354248957477)
                      ·
                        rfl

theorem cell23_389772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_389772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389772 prefixEnd_389772 := by exact prefixLift 389772
  have htrace : WordTrace (prefixWord ++ tailWord_389772) baseStart_389772 baseEnd_389772 := by
    simpa [prefixWord, tailWord_389772, baseEnd_389772] using wordTrace_append hprefix tailTrace_389772
  have hstable : (prefixWord ++ tailWord_389772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389772).length < 2 ^ (prefixWord ++ tailWord_389772).sum := by decide
  have hdescent : baseEnd_389772 < baseStart_389772 := by decide
  rcases family_descends (prefixWord ++ tailWord_389772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389789 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_389789 : Nat := 118140960795 + 389789 * 2 ^ 59
def prefixEnd_389789 : Nat := 4983230072969 + 3 ^ 40 * 389789 * 2
def baseEnd_389789 : Nat := 200149110835480682444899

theorem tailTrace_389789 : CollatzResearch.WordTrace tailWord_389789 prefixEnd_389789 200149110835480682444899 := by
  unfold tailWord_389789
  simp only [CollatzResearch.WordTrace]
  refine ⟨14216772784868498506348421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9477848523245665670898947 14216772784868498506348421)
  ·
    refine ⟨2665644897162843469940329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14216772784868498506348421 2665644897162843469940329)
    ·
      refine ⟨1999233672872132602455247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2665644897162843469940329 1999233672872132602455247)
      ·
        refine ⟨2998850509308198903682871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1999233672872132602455247 2998850509308198903682871)
        ·
          refine ⟨4498275763962298355524307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2998850509308198903682871 4498275763962298355524307)
          ·
            refine ⟨6747413645943447533286461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4498275763962298355524307 6747413645943447533286461)
            ·
              refine ⟨2530280117228792824982423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6747413645943447533286461 2530280117228792824982423)
              ·
                refine ⟨3795420175843189237473635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2530280117228792824982423 3795420175843189237473635)
                ·
                  refine ⟨5693130263764783856210453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795420175843189237473635 5693130263764783856210453)
                  ·
                    refine ⟨266865481113974243259865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5693130263764783856210453 266865481113974243259865)
                    ·
                      refine ⟨200149110835480682444899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266865481113974243259865 200149110835480682444899)
                      ·
                        rfl

theorem cell23_389789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_389789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389789 prefixEnd_389789 := by exact prefixLift 389789
  have htrace : WordTrace (prefixWord ++ tailWord_389789) baseStart_389789 baseEnd_389789 := by
    simpa [prefixWord, tailWord_389789, baseEnd_389789] using wordTrace_append hprefix tailTrace_389789
  have hstable : (prefixWord ++ tailWord_389789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389789).length < 2 ^ (prefixWord ++ tailWord_389789).sum := by decide
  have hdescent : baseEnd_389789 < baseStart_389789 := by decide
  rcases family_descends (prefixWord ++ tailWord_389789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389806 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_389806 : Nat := 118140960795 + 389806 * 2 ^ 59
def prefixEnd_389806 : Nat := 4983230072969 + 3 ^ 40 * 389806 * 2
def baseEnd_389806 : Nat := 200157840006607115932321

theorem tailTrace_389806 : CollatzResearch.WordTrace tailWord_389806 prefixEnd_389806 200157840006607115932321 := by
  unfold tailWord_389806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1777174103225863801214659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9478261883871273606478181 1777174103225863801214659)
  ·
    refine ⟨2665761154838795701821989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1777174103225863801214659 2665761154838795701821989)
    ·
      refine ⟨499830216532274194091623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2665761154838795701821989 499830216532274194091623)
      ·
        refine ⟨749745324798411291137435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499830216532274194091623 749745324798411291137435)
        ·
          refine ⟨1124617987197616936706153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749745324798411291137435 1124617987197616936706153)
          ·
            refine ⟨843463490398212702529615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1124617987197616936706153 843463490398212702529615)
            ·
              refine ⟨1265195235597319053794423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 843463490398212702529615 1265195235597319053794423)
              ·
                refine ⟨1897792853395978580691635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265195235597319053794423 1897792853395978580691635)
                ·
                  refine ⟨2846689280093967871037453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897792853395978580691635 2846689280093967871037453)
                  ·
                    refine ⟨1067508480035237951639045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2846689280093967871037453 1067508480035237951639045)
                    ·
                      refine ⟨200157840006607115932321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1067508480035237951639045 200157840006607115932321)
                      ·
                        rfl

theorem cell23_389806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_389806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389806 prefixEnd_389806 := by exact prefixLift 389806
  have htrace : WordTrace (prefixWord ++ tailWord_389806) baseStart_389806 baseEnd_389806 := by
    simpa [prefixWord, tailWord_389806, baseEnd_389806] using wordTrace_append hprefix tailTrace_389806
  have hstable : (prefixWord ++ tailWord_389806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389806).length < 2 ^ (prefixWord ++ tailWord_389806).sum := by decide
  have hdescent : baseEnd_389806 < baseStart_389806 := by decide
  rcases family_descends (prefixWord ++ tailWord_389806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389832 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_389832 : Nat := 118140960795 + 389832 * 2 ^ 59
def prefixEnd_389832 : Nat := 4983230072969 + 3 ^ 40 * 389832 * 2
def baseEnd_389832 : Nat := 200171190503624014207201

theorem tailTrace_389832 : CollatzResearch.WordTrace tailWord_389832 prefixEnd_389832 200171190503624014207201 := by
  unfold tailWord_389832
  simp only [CollatzResearch.WordTrace]
  refine ⟨7109170561856358425081875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9478894082475144566775833 7109170561856358425081875)
  ·
    refine ⟨10663755842784537637622813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7109170561856358425081875 10663755842784537637622813)
    ·
      refine ⟨3998908441044201614108555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10663755842784537637622813 3998908441044201614108555)
      ·
        refine ⟨5998362661566302421162833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3998908441044201614108555 5998362661566302421162833)
        ·
          refine ⟨4498771996174726815872125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5998362661566302421162833 4498771996174726815872125)
          ·
            refine ⟨1687039498565522555952047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4498771996174726815872125 1687039498565522555952047)
            ·
              refine ⟨2530559247848283833928071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1687039498565522555952047 2530559247848283833928071)
              ·
                refine ⟨3795838871772425750892107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2530559247848283833928071 3795838871772425750892107)
                ·
                  refine ⟨5693758307658638626338161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795838871772425750892107 5693758307658638626338161)
                  ·
                    refine ⟨4270318730743978969753621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5693758307658638626338161 4270318730743978969753621)
                    ·
                      refine ⟨200171190503624014207201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4270318730743978969753621 200171190503624014207201)
                      ·
                        rfl

theorem cell23_389832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_389832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389832 prefixEnd_389832 := by exact prefixLift 389832
  have htrace : WordTrace (prefixWord ++ tailWord_389832) baseStart_389832 baseEnd_389832 := by
    simpa [prefixWord, tailWord_389832, baseEnd_389832] using wordTrace_append hprefix tailTrace_389832
  have hstable : (prefixWord ++ tailWord_389832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389832).length < 2 ^ (prefixWord ++ tailWord_389832).sum := by decide
  have hdescent : baseEnd_389832 < baseStart_389832 := by decide
  rcases family_descends (prefixWord ++ tailWord_389832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389849 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 3, 5, 2]
def baseStart_389849 : Nat := 118140960795 + 389849 * 2 ^ 59
def prefixEnd_389849 : Nat := 4983230072969 + 3 ^ 40 * 389849 * 2
def baseEnd_389849 : Nat := 200179919674750447694623

theorem tailTrace_389849 : CollatzResearch.WordTrace tailWord_389849 prefixEnd_389849 200179919674750447694623 := by
  unfold tailWord_389849
  simp only [CollatzResearch.WordTrace]
  refine ⟨14218961164651128753532601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9479307443100752502355067 14218961164651128753532601)
  ·
    refine ⟨10664220873488346565149451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14218961164651128753532601 10664220873488346565149451)
    ·
      refine ⟨15996331310232519847724177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10664220873488346565149451 15996331310232519847724177)
      ·
        refine ⟨11997248482674389885793133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15996331310232519847724177 11997248482674389885793133)
        ·
          refine ⟨4498968181002896207172425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11997248482674389885793133 4498968181002896207172425)
          ·
            refine ⟨3374226135752172155379319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4498968181002896207172425 3374226135752172155379319)
            ·
              refine ⟨5061339203628258233068979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374226135752172155379319 5061339203628258233068979)
              ·
                refine ⟨7592008805442387349603469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5061339203628258233068979 7592008805442387349603469)
                ·
                  refine ⟨2847003302040895256101301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7592008805442387349603469 2847003302040895256101301)
                  ·
                    refine ⟨266906559566333930259497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2847003302040895256101301 266906559566333930259497)
                    ·
                      refine ⟨200179919674750447694623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266906559566333930259497 200179919674750447694623)
                      ·
                        rfl

theorem cell23_389849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 5, 2].length) (baseStart_389849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389849 prefixEnd_389849 := by exact prefixLift 389849
  have htrace : WordTrace (prefixWord ++ tailWord_389849) baseStart_389849 baseEnd_389849 := by
    simpa [prefixWord, tailWord_389849, baseEnd_389849] using wordTrace_append hprefix tailTrace_389849
  have hstable : (prefixWord ++ tailWord_389849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389849).length < 2 ^ (prefixWord ++ tailWord_389849).sum := by decide
  have hdescent : baseEnd_389849 < baseStart_389849 := by decide
  rcases family_descends (prefixWord ++ tailWord_389849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389866 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_389866 : Nat := 118140960795 + 389866 * 2 ^ 59
def prefixEnd_389866 : Nat := 4983230072969 + 3 ^ 40 * 389866 * 2
def baseEnd_389866 : Nat := 200188648845876881182045

theorem tailTrace_389866 : CollatzResearch.WordTrace tailWord_389866 prefixEnd_389866 200188648845876881182045 := by
  unfold tailWord_389866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3554895301397385164225363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9479720803726360437934301 3554895301397385164225363)
  ·
    refine ⟨5332342952096077746338045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3554895301397385164225363 5332342952096077746338045)
    ·
      refine ⟨1999628607036029154876767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5332342952096077746338045 1999628607036029154876767)
      ·
        refine ⟨2999442910554043732315151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1999628607036029154876767 2999442910554043732315151)
        ·
          refine ⟨4499164365831065598472727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999442910554043732315151 4499164365831065598472727)
          ·
            refine ⟨6748746548746598397709091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499164365831065598472727 6748746548746598397709091)
            ·
              refine ⟨10123119823119897596563637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6748746548746598397709091 10123119823119897596563637)
              ·
                refine ⟨949042483417490399677841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10123119823119897596563637 949042483417490399677841)
                ·
                  refine ⟨711781862563117799758381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 949042483417490399677841 711781862563117799758381)
                  ·
                    refine ⟨266918198461169174909393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 711781862563117799758381 266918198461169174909393)
                    ·
                      refine ⟨200188648845876881182045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266918198461169174909393 200188648845876881182045)
                      ·
                        rfl

theorem cell23_389866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_389866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389866 prefixEnd_389866 := by exact prefixLift 389866
  have htrace : WordTrace (prefixWord ++ tailWord_389866) baseStart_389866 baseEnd_389866 := by
    simpa [prefixWord, tailWord_389866, baseEnd_389866] using wordTrace_append hprefix tailTrace_389866
  have hstable : (prefixWord ++ tailWord_389866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389866).length < 2 ^ (prefixWord ++ tailWord_389866).sum := by decide
  have hdescent : baseEnd_389866 < baseStart_389866 := by decide
  rcases family_descends (prefixWord ++ tailWord_389866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389872 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 3, 6]
def baseStart_389872 : Nat := 118140960795 + 389872 * 2 ^ 59
def prefixEnd_389872 : Nat := 4983230072969 + 3 ^ 40 * 389872 * 2
def baseEnd_389872 : Nat := 66730576576601285902339

theorem tailTrace_389872 : CollatzResearch.WordTrace tailWord_389872 prefixEnd_389872 66730576576601285902339 := by
  unfold tailWord_389872
  simp only [CollatzResearch.WordTrace]
  refine ⟨7109900021783901840809935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9479866695711869121079913 7109900021783901840809935)
  ·
    refine ⟨10664850032675852761214903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7109900021783901840809935 10664850032675852761214903)
    ·
      refine ⟨15997275049013779141822355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10664850032675852761214903 15997275049013779141822355)
      ·
        refine ⟨23995912573520668712733533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15997275049013779141822355 23995912573520668712733533)
        ·
          refine ⟨8998467215070250767275075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23995912573520668712733533 8998467215070250767275075)
          ·
            refine ⟨13497700822605376150912613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8998467215070250767275075 13497700822605376150912613)
            ·
              refine ⟨2530818904238508028296115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13497700822605376150912613 2530818904238508028296115)
              ·
                refine ⟨3796228356357762042444173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2530818904238508028296115 3796228356357762042444173)
                ·
                  refine ⟨1423585633634160765916565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3796228356357762042444173 1423585633634160765916565)
                  ·
                    refine ⟨66730576576601285902339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1423585633634160765916565 66730576576601285902339)
                    ·
                      rfl

theorem cell23_389872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_389872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389872 prefixEnd_389872 := by exact prefixLift 389872
  have htrace : WordTrace (prefixWord ++ tailWord_389872) baseStart_389872 baseEnd_389872 := by
    simpa [prefixWord, tailWord_389872, baseEnd_389872] using wordTrace_append hprefix tailTrace_389872
  have hstable : (prefixWord ++ tailWord_389872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389872).length < 2 ^ (prefixWord ++ tailWord_389872).sum := by decide
  have hdescent : baseEnd_389872 < baseStart_389872 := by decide
  rcases family_descends (prefixWord ++ tailWord_389872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389890 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_389890 : Nat := 118140960795 + 389890 * 2 ^ 59
def prefixEnd_389890 : Nat := 4983230072969 + 3 ^ 40 * 389890 * 2
def baseEnd_389890 : Nat := 200200972381584787281935

theorem tailTrace_389890 : CollatzResearch.WordTrace tailWord_389890 prefixEnd_389890 200200972381584787281935 := by
  unfold tailWord_389890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3555114139375648188943781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9480304371668395170516749 3555114139375648188943781)
  ·
    refine ⟨666583901132934035426959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3555114139375648188943781 666583901132934035426959)
    ·
      refine ⟨999875851699401053140439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 666583901132934035426959 999875851699401053140439)
      ·
        refine ⟨1499813777549101579710659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999875851699401053140439 1499813777549101579710659)
        ·
          refine ⟨2249720666323652369565989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499813777549101579710659 2249720666323652369565989)
          ·
            refine ⟨421822624935684819293623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2249720666323652369565989 421822624935684819293623)
            ·
              refine ⟨632733937403527228940435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421822624935684819293623 632733937403527228940435)
              ·
                refine ⟨949100906105290843410653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632733937403527228940435 949100906105290843410653)
                ·
                  refine ⟨355912839789484066278995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949100906105290843410653 355912839789484066278995)
                  ·
                    refine ⟨533869259684226099418493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 355912839789484066278995 533869259684226099418493)
                    ·
                      refine ⟨200200972381584787281935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 533869259684226099418493 200200972381584787281935)
                      ·
                        rfl

theorem cell23_389890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_389890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389890 prefixEnd_389890 := by exact prefixLift 389890
  have htrace : WordTrace (prefixWord ++ tailWord_389890) baseStart_389890 baseEnd_389890 := by
    simpa [prefixWord, tailWord_389890, baseEnd_389890] using wordTrace_append hprefix tailTrace_389890
  have hstable : (prefixWord ++ tailWord_389890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389890).length < 2 ^ (prefixWord ++ tailWord_389890).sum := by decide
  have hdescent : baseEnd_389890 < baseStart_389890 := by decide
  rcases family_descends (prefixWord ++ tailWord_389890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389899 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 3]
def baseStart_389899 : Nat := 118140960795 + 389899 * 2 ^ 59
def prefixEnd_389899 : Nat := 4983230072969 + 3 ^ 40 * 389899 * 2
def baseEnd_389899 : Nat := 200205593707475252069393

theorem tailTrace_389899 : CollatzResearch.WordTrace tailWord_389899 prefixEnd_389899 200205593707475252069393 := by
  unfold tailWord_389899
  simp only [CollatzResearch.WordTrace]
  refine ⟨14220784814469987292852751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9480523209646658195235167 14220784814469987292852751)
  ·
    refine ⟨21331177221704980939279127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14220784814469987292852751 21331177221704980939279127)
    ·
      refine ⟨31996765832557471408918691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21331177221704980939279127 31996765832557471408918691)
      ·
        refine ⟨47995148748836207113378037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31996765832557471408918691 47995148748836207113378037)
        ·
          refine ⟨4499545195203394416879191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47995148748836207113378037 4499545195203394416879191)
          ·
            refine ⟨6749317792805091625318787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499545195203394416879191 6749317792805091625318787)
            ·
              refine ⟨10123976689207637437978181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6749317792805091625318787 10123976689207637437978181)
              ·
                refine ⟨1898245629226432019620909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10123976689207637437978181 1898245629226432019620909)
                ·
                  refine ⟨711842110959912007357841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1898245629226432019620909 711842110959912007357841)
                  ·
                    refine ⟨533881583219934005518381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 711842110959912007357841 533881583219934005518381)
                    ·
                      refine ⟨200205593707475252069393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 533881583219934005518381 200205593707475252069393)
                      ·
                        rfl

theorem cell23_389899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 3].length) (baseStart_389899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389899 prefixEnd_389899 := by exact prefixLift 389899
  have htrace : WordTrace (prefixWord ++ tailWord_389899) baseStart_389899 baseEnd_389899 := by
    simpa [prefixWord, tailWord_389899, baseEnd_389899] using wordTrace_append hprefix tailTrace_389899
  have hstable : (prefixWord ++ tailWord_389899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389899).length < 2 ^ (prefixWord ++ tailWord_389899).sum := by decide
  have hdescent : baseEnd_389899 < baseStart_389899 := by decide
  rcases family_descends (prefixWord ++ tailWord_389899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389909 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_389909 : Nat := 118140960795 + 389909 * 2 ^ 59
def prefixEnd_389909 : Nat := 4983230072969 + 3 ^ 40 * 389909 * 2
def baseEnd_389909 : Nat := 200210728514020212944347

theorem tailTrace_389909 : CollatzResearch.WordTrace tailWord_389909 prefixEnd_389909 200210728514020212944347 := by
  unfold tailWord_389909
  simp only [CollatzResearch.WordTrace]
  refine ⟨14221149544433759000716781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9480766362955839333811187 14221149544433759000716781)
  ·
    refine ⟨5332931079162659625268793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14221149544433759000716781 5332931079162659625268793)
    ·
      refine ⟨3999698309371994718951595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5332931079162659625268793 3999698309371994718951595)
      ·
        refine ⟨5999547464057992078427393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3999698309371994718951595 5999547464057992078427393)
        ·
          refine ⟨4499660598043494058820545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5999547464057992078427393 4499660598043494058820545)
          ·
            refine ⟨3374745448532620544115409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4499660598043494058820545 3374745448532620544115409)
            ·
              refine ⟨2531059086399465408086557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3374745448532620544115409 2531059086399465408086557)
              ·
                refine ⟨949147157399799528032459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2531059086399465408086557 949147157399799528032459)
                ·
                  refine ⟨1423720736099699292048689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949147157399799528032459 1423720736099699292048689)
                  ·
                    refine ⟨1067790552074774469036517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1423720736099699292048689 1067790552074774469036517)
                    ·
                      refine ⟨200210728514020212944347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1067790552074774469036517 200210728514020212944347)
                      ·
                        rfl

theorem cell23_389909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_389909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389909 prefixEnd_389909 := by exact prefixLift 389909
  have htrace : WordTrace (prefixWord ++ tailWord_389909) baseStart_389909 baseEnd_389909 := by
    simpa [prefixWord, tailWord_389909, baseEnd_389909] using wordTrace_append hprefix tailTrace_389909
  have hstable : (prefixWord ++ tailWord_389909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389909).length < 2 ^ (prefixWord ++ tailWord_389909).sum := by decide
  have hdescent : baseEnd_389909 < baseStart_389909 := by decide
  rcases family_descends (prefixWord ++ tailWord_389909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389916 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_389916 : Nat := 118140960795 + 389916 * 2 ^ 59
def prefixEnd_389916 : Nat := 4983230072969 + 3 ^ 40 * 389916 * 2
def baseEnd_389916 : Nat := 200214322878601685556815

theorem tailTrace_389916 : CollatzResearch.WordTrace tailWord_389916 prefixEnd_389916 200214322878601685556815 := by
  unfold tailWord_389916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7110702427704199598110801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9480936570272266130814401 7110702427704199598110801)
  ·
    refine ⟨5333026820778149698583101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7110702427704199598110801 5333026820778149698583101)
    ·
      refine ⟨1999885057791806136968663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5333026820778149698583101 1999885057791806136968663)
      ·
        refine ⟨2999827586687709205452995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1999885057791806136968663 2999827586687709205452995)
        ·
          refine ⟨4499741380031563808179493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999827586687709205452995 4499741380031563808179493)
          ·
            refine ⟨843701508755918214033655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4499741380031563808179493 843701508755918214033655)
            ·
              refine ⟨1265552263133877321050483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 843701508755918214033655 1265552263133877321050483)
              ·
                refine ⟨1898328394700815981575725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265552263133877321050483 1898328394700815981575725)
                ·
                  refine ⟨711873148012805993090897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1898328394700815981575725 711873148012805993090897)
                  ·
                    refine ⟨533904861009604494818173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 711873148012805993090897 533904861009604494818173)
                    ·
                      refine ⟨200214322878601685556815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 533904861009604494818173 200214322878601685556815)
                      ·
                        rfl

theorem cell23_389916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_389916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389916 prefixEnd_389916 := by exact prefixLift 389916
  have htrace : WordTrace (prefixWord ++ tailWord_389916) baseStart_389916 baseEnd_389916 := by
    simpa [prefixWord, tailWord_389916, baseEnd_389916] using wordTrace_append hprefix tailTrace_389916
  have hstable : (prefixWord ++ tailWord_389916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389916).length < 2 ^ (prefixWord ++ tailWord_389916).sum := by decide
  have hdescent : baseEnd_389916 < baseStart_389916 := by decide
  rcases family_descends (prefixWord ++ tailWord_389916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389929 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 1, 3, 3]
def baseStart_389929 : Nat := 118140960795 + 389929 * 2 ^ 59
def prefixEnd_389929 : Nat := 4983230072969 + 3 ^ 40 * 389929 * 2
def baseEnd_389929 : Nat := 200220998127110134694255

theorem tailTrace_389929 : CollatzResearch.WordTrace tailWord_389929 prefixEnd_389929 200220998127110134694255 := by
  unfold tailWord_389929
  simp only [CollatzResearch.WordTrace]
  refine ⟨14221879004361302416444841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9481252669574201610963227 14221879004361302416444841)
  ·
    refine ⟨10666409253270976812333631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14221879004361302416444841 10666409253270976812333631)
    ·
      refine ⟨15999613879906465218500447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10666409253270976812333631 15999613879906465218500447)
      ·
        refine ⟨23999420819859697827750671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15999613879906465218500447 23999420819859697827750671)
        ·
          refine ⟨35999131229789546741626007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23999420819859697827750671 35999131229789546741626007)
          ·
            refine ⟨53998696844684320112439011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35999131229789546741626007 53998696844684320112439011)
            ·
              refine ⟨80998045267026480168658517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53998696844684320112439011 80998045267026480168658517)
              ·
                refine ⟨949195842972966564476467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 80998045267026480168658517 949195842972966564476467)
                ·
                  refine ⟨1423793764459449846714701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949195842972966564476467 1423793764459449846714701)
                  ·
                    refine ⟨533922661672293692518013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1423793764459449846714701 533922661672293692518013)
                    ·
                      refine ⟨200220998127110134694255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 533922661672293692518013 200220998127110134694255)
                      ·
                        rfl

theorem cell23_389929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 3, 3].length) (baseStart_389929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389929 prefixEnd_389929 := by exact prefixLift 389929
  have htrace : WordTrace (prefixWord ++ tailWord_389929) baseStart_389929 baseEnd_389929 := by
    simpa [prefixWord, tailWord_389929, baseEnd_389929] using wordTrace_append hprefix tailTrace_389929
  have hstable : (prefixWord ++ tailWord_389929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389929).length < 2 ^ (prefixWord ++ tailWord_389929).sum := by decide
  have hdescent : baseEnd_389929 < baseStart_389929 := by decide
  rcases family_descends (prefixWord ++ tailWord_389929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389940 : List Nat := [2, 5, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_389940 : Nat := 118140960795 + 389940 * 2 ^ 59
def prefixEnd_389940 : Nat := 4983230072969 + 3 ^ 40 * 389940 * 2
def baseEnd_389940 : Nat := 66742215471436530552235

theorem tailTrace_389940 : CollatzResearch.WordTrace tailWord_389940 prefixEnd_389940 66742215471436530552235 := by
  unfold tailWord_389940
  simp only [CollatzResearch.WordTrace]
  refine ⟨7111140103660725647547637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9481520138214300863396849 7111140103660725647547637)
  ·
    refine ⟨666669384718193029457591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7111140103660725647547637 666669384718193029457591)
    ·
      refine ⟨1000004077077289544186387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 666669384718193029457591 1000004077077289544186387)
      ·
        refine ⟨1500006115615934316279581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1000004077077289544186387 1500006115615934316279581)
        ·
          refine ⟨562502293355975368604843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1500006115615934316279581 562502293355975368604843)
          ·
            refine ⟨843753440033963052907265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562502293355975368604843 843753440033963052907265)
            ·
              refine ⟨632815080025472289680449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843753440033963052907265 632815080025472289680449)
              ·
                refine ⟨474611310019104217260337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632815080025472289680449 474611310019104217260337)
                ·
                  refine ⟨355958482514328162945253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474611310019104217260337 355958482514328162945253)
                  ·
                    refine ⟨66742215471436530552235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 355958482514328162945253 66742215471436530552235)
                    ·
                      rfl

theorem cell23_389940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_389940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389940 prefixEnd_389940 := by exact prefixLift 389940
  have htrace : WordTrace (prefixWord ++ tailWord_389940) baseStart_389940 baseEnd_389940 := by
    simpa [prefixWord, tailWord_389940, baseEnd_389940] using wordTrace_append hprefix tailTrace_389940
  have hstable : (prefixWord ++ tailWord_389940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389940).length < 2 ^ (prefixWord ++ tailWord_389940).sum := by decide
  have hdescent : baseEnd_389940 < baseStart_389940 := by decide
  rcases family_descends (prefixWord ++ tailWord_389940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389953 : List Nat := [1, 2, 5, 3, 1, 2, 1, 8]
def baseStart_389953 : Nat := 118140960795 + 389953 * 2 ^ 59
def prefixEnd_389953 : Nat := 4983230072969 + 3 ^ 40 * 389953 * 2
def baseEnd_389953 : Nat := 7416048950474742251635

theorem tailTrace_389953 : CollatzResearch.WordTrace tailWord_389953 prefixEnd_389953 7416048950474742251635 := by
  unfold tailWord_389953
  simp only [CollatzResearch.WordTrace]
  refine ⟨14222754356274354515318513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9481836237516236343545675 14222754356274354515318513)
  ·
    refine ⟨10667065767205765886488885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14222754356274354515318513 10667065767205765886488885)
    ·
      refine ⟨1000037415675540551858333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10667065767205765886488885 1000037415675540551858333)
      ·
        refine ⟨375014030878327706946875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1000037415675540551858333 375014030878327706946875)
        ·
          refine ⟨562521046317491560420313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375014030878327706946875 562521046317491560420313)
          ·
            refine ⟨421890784738118670315235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562521046317491560420313 421890784738118670315235)
            ·
              refine ⟨632836177107178005472853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421890784738118670315235 632836177107178005472853)
              ·
                refine ⟨7416048950474742251635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 632836177107178005472853 7416048950474742251635)
                ·
                  rfl

theorem cell23_389953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 8].length) (baseStart_389953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389953 prefixEnd_389953 := by exact prefixLift 389953
  have htrace : WordTrace (prefixWord ++ tailWord_389953) baseStart_389953 baseEnd_389953 := by
    simpa [prefixWord, tailWord_389953, baseEnd_389953] using wordTrace_append hprefix tailTrace_389953
  have hstable : (prefixWord ++ tailWord_389953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389953).length < 2 ^ (prefixWord ++ tailWord_389953).sum := by decide
  have hdescent : baseEnd_389953 < baseStart_389953 := by decide
  rcases family_descends (prefixWord ++ tailWord_389953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389973 : List Nat := [1, 3, 2, 2, 2, 1, 2, 4, 1, 3, 2]
def baseStart_389973 : Nat := 118140960795 + 389973 * 2 ^ 59
def prefixEnd_389973 : Nat := 4983230072969 + 3 ^ 40 * 389973 * 2
def baseEnd_389973 : Nat := 200243591275907962544053

theorem tailTrace_389973 : CollatzResearch.WordTrace tailWord_389973 prefixEnd_389973 200243591275907962544053 := by
  unfold tailWord_389973
  simp only [CollatzResearch.WordTrace]
  refine ⟨14223483816201897931046573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9482322544134598620697715 14223483816201897931046573)
  ·
    refine ⟨5333806431075711724142465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14223483816201897931046573 5333806431075711724142465)
    ·
      refine ⟨4000354823306783793106849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5333806431075711724142465 4000354823306783793106849)
      ·
        refine ⟨3000266117480087844830137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4000354823306783793106849 3000266117480087844830137)
        ·
          refine ⟨2250199588110065883622603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3000266117480087844830137 2250199588110065883622603)
          ·
            refine ⟨3375299382165098825433905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250199588110065883622603 3375299382165098825433905)
            ·
              refine ⟨2531474536623824119075429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3375299382165098825433905 2531474536623824119075429)
              ·
                refine ⟨474651475616967022326643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2531474536623824119075429 474651475616967022326643)
                ·
                  refine ⟨711977213425450533489965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474651475616967022326643 711977213425450533489965)
                  ·
                    refine ⟨266991455034543950058737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 711977213425450533489965 266991455034543950058737)
                    ·
                      refine ⟨200243591275907962544053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 266991455034543950058737 200243591275907962544053)
                      ·
                        rfl

theorem cell23_389973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_389973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389973 prefixEnd_389973 := by exact prefixLift 389973
  have htrace : WordTrace (prefixWord ++ tailWord_389973) baseStart_389973 baseEnd_389973 := by
    simpa [prefixWord, tailWord_389973, baseEnd_389973] using wordTrace_append hprefix tailTrace_389973
  have hstable : (prefixWord ++ tailWord_389973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389973).length < 2 ^ (prefixWord ++ tailWord_389973).sum := by decide
  have hdescent : baseEnd_389973 < baseStart_389973 := by decide
  rcases family_descends (prefixWord ++ tailWord_389973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389989 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_389989 : Nat := 118140960795 + 389989 * 2 ^ 59
def prefixEnd_389989 : Nat := 4983230072969 + 3 ^ 40 * 389989 * 2
def baseEnd_389989 : Nat := 200251806966379899943979

theorem tailTrace_389989 : CollatzResearch.WordTrace tailWord_389989 prefixEnd_389989 200251806966379899943979 := by
  unfold tailWord_389989
  simp only [CollatzResearch.WordTrace]
  refine ⟨14224067384143932663629021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9482711589429288442419347 14224067384143932663629021)
  ·
    refine ⟨5334025269053974748860883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14224067384143932663629021 5334025269053974748860883)
    ·
      refine ⟨8001037903580962123291325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5334025269053974748860883 8001037903580962123291325)
      ·
        refine ⟨3000389213842860796234247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8001037903580962123291325 3000389213842860796234247)
        ·
          refine ⟨4500583820764291194351371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3000389213842860796234247 4500583820764291194351371)
          ·
            refine ⟨6750875731146436791527057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4500583820764291194351371 6750875731146436791527057)
            ·
              refine ⟨5063156798359827593645293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6750875731146436791527057 5063156798359827593645293)
              ·
                refine ⟨1898683799384935347616985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5063156798359827593645293 1898683799384935347616985)
                ·
                  refine ⟨1424012849538701510712739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1898683799384935347616985 1424012849538701510712739)
                  ·
                    refine ⟨2136019274308052266069109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1424012849538701510712739 2136019274308052266069109)
                    ·
                      refine ⟨200251806966379899943979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2136019274308052266069109 200251806966379899943979)
                      ·
                        rfl

theorem cell23_389989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_389989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_389989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_389989 prefixEnd_389989 := by exact prefixLift 389989
  have htrace : WordTrace (prefixWord ++ tailWord_389989) baseStart_389989 baseEnd_389989 := by
    simpa [prefixWord, tailWord_389989, baseEnd_389989] using wordTrace_append hprefix tailTrace_389989
  have hstable : (prefixWord ++ tailWord_389989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389989).length < 2 ^ (prefixWord ++ tailWord_389989).sum := by decide
  have hdescent : baseEnd_389989 < baseStart_389989 := by decide
  rcases family_descends (prefixWord ++ tailWord_389989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390009 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 7]
def baseStart_390009 : Nat := 118140960795 + 390009 * 2 ^ 59
def prefixEnd_390009 : Nat := 4983230072969 + 3 ^ 40 * 390009 * 2
def baseEnd_390009 : Nat := 22251341842163313521543

theorem tailTrace_390009 : CollatzResearch.WordTrace tailWord_390009 prefixEnd_390009 22251341842163313521543 := by
  unfold tailWord_390009
  simp only [CollatzResearch.WordTrace]
  refine ⟨14224796844071476079357081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9483197896047650719571387 14224796844071476079357081)
  ·
    refine ⟨10668597633053607059517811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14224796844071476079357081 10668597633053607059517811)
    ·
      refine ⟨16002896449580410589276717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10668597633053607059517811 16002896449580410589276717)
      ·
        refine ⟨6001086168592653970978769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16002896449580410589276717 6001086168592653970978769)
        ·
          refine ⟨4500814626444490478234077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6001086168592653970978769 4500814626444490478234077)
          ·
            refine ⟨1687805484916683929337779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4500814626444490478234077 1687805484916683929337779)
            ·
              refine ⟨2531708227375025894006669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1687805484916683929337779 2531708227375025894006669)
              ·
                refine ⟨949390585265634710252501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2531708227375025894006669 949390585265634710252501)
                ·
                  refine ⟨22251341842163313521543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 949390585265634710252501 22251341842163313521543)
                  ·
                    rfl

theorem cell23_390009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 7].length) (baseStart_390009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390009 prefixEnd_390009 := by exact prefixLift 390009
  have htrace : WordTrace (prefixWord ++ tailWord_390009) baseStart_390009 baseEnd_390009 := by
    simpa [prefixWord, tailWord_390009, baseEnd_390009] using wordTrace_append hprefix tailTrace_390009
  have hstable : (prefixWord ++ tailWord_390009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390009).length < 2 ^ (prefixWord ++ tailWord_390009).sum := by decide
  have hdescent : baseEnd_390009 < baseStart_390009 := by decide
  rcases family_descends (prefixWord ++ tailWord_390009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390014 : List Nat := [4, 2, 3, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_390014 : Nat := 118140960795 + 390014 * 2 ^ 59
def prefixEnd_390014 : Nat := 4983230072969 + 3 ^ 40 * 390014 * 2
def baseEnd_390014 : Nat := 200264643982742302131365

theorem tailTrace_390014 : CollatzResearch.WordTrace tailWord_390014 prefixEnd_390014 200264643982742302131365 := by
  unfold tailWord_390014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1778122401131670241661137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9483319472702241288859397 1778122401131670241661137)
  ·
    refine ⟨1333591800848752681245853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1778122401131670241661137 1333591800848752681245853)
    ·
      refine ⟨500096925318282255467195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1333591800848752681245853 500096925318282255467195)
      ·
        refine ⟨750145387977423383200793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500096925318282255467195 750145387977423383200793)
        ·
          refine ⟨562609040983067537400595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 750145387977423383200793 562609040983067537400595)
          ·
            refine ⟨843913561474601306100893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562609040983067537400595 843913561474601306100893)
            ·
              refine ⟨316467585552975489787835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 843913561474601306100893 316467585552975489787835)
              ·
                refine ⟨474701378329463234681753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316467585552975489787835 474701378329463234681753)
                ·
                  refine ⟨356026033747097426011315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474701378329463234681753 356026033747097426011315)
                  ·
                    refine ⟨534039050620646139016973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 356026033747097426011315 534039050620646139016973)
                    ·
                      refine ⟨200264643982742302131365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 534039050620646139016973 200264643982742302131365)
                      ·
                        rfl

theorem cell23_390014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_390014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390014 prefixEnd_390014 := by exact prefixLift 390014
  have htrace : WordTrace (prefixWord ++ tailWord_390014) baseStart_390014 baseEnd_390014 := by
    simpa [prefixWord, tailWord_390014, baseEnd_390014] using wordTrace_append hprefix tailTrace_390014
  have hstable : (prefixWord ++ tailWord_390014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390014).length < 2 ^ (prefixWord ++ tailWord_390014).sum := by decide
  have hdescent : baseEnd_390014 < baseStart_390014 := by decide
  rcases family_descends (prefixWord ++ tailWord_390014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390026 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 7]
def baseStart_390026 : Nat := 118140960795 + 390026 * 2 ^ 59
def prefixEnd_390026 : Nat := 4983230072969 + 3 ^ 40 * 390026 * 2
def baseEnd_390026 : Nat := 22252311750066250575701

theorem tailTrace_390026 : CollatzResearch.WordTrace tailWord_390026 prefixEnd_390026 22252311750066250575701 := by
  unfold tailWord_390026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3556354221252471995681483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9483611256673258655150621 3556354221252471995681483)
  ·
    refine ⟨5334531331878707993522225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3556354221252471995681483 5334531331878707993522225)
    ·
      refine ⟨4000898498909030995141669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5334531331878707993522225 4000898498909030995141669)
      ·
        refine ⟨750168468545443311589063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4000898498909030995141669 750168468545443311589063)
        ·
          refine ⟨1125252702818164967383595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750168468545443311589063 1125252702818164967383595)
          ·
            refine ⟨1687879054227247451075393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125252702818164967383595 1687879054227247451075393)
            ·
              refine ⟨1265909290670435588306545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1687879054227247451075393 1265909290670435588306545)
              ·
                refine ⟨949431968002826691229909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265909290670435588306545 949431968002826691229909)
                ·
                  refine ⟨22252311750066250575701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 949431968002826691229909 22252311750066250575701)
                  ·
                    rfl

theorem cell23_390026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_390026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390026 prefixEnd_390026 := by exact prefixLift 390026
  have htrace : WordTrace (prefixWord ++ tailWord_390026) baseStart_390026 baseEnd_390026 := by
    simpa [prefixWord, tailWord_390026, baseEnd_390026] using wordTrace_append hprefix tailTrace_390026
  have hstable : (prefixWord ++ tailWord_390026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390026).length < 2 ^ (prefixWord ++ tailWord_390026).sum := by decide
  have hdescent : baseEnd_390026 < baseStart_390026 := by decide
  rcases family_descends (prefixWord ++ tailWord_390026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390039 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 1, 7]
def baseStart_390039 : Nat := 118140960795 + 390039 * 2 ^ 59
def prefixEnd_390039 : Nat := 4983230072969 + 3 ^ 40 * 390039 * 2
def baseEnd_390039 : Nat := 66759160333034901439583

theorem tailTrace_390039 : CollatzResearch.WordTrace tailWord_390039 prefixEnd_390039 66759160333034901439583 := by
  unfold tailWord_390039
  simp only [CollatzResearch.WordTrace]
  refine ⟨14225891033962791202949171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9483927355975194135299447 14225891033962791202949171)
  ·
    refine ⟨21338836550944186804423757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14225891033962791202949171 21338836550944186804423757)
    ·
      refine ⟨8002063706604070051658909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21338836550944186804423757 8002063706604070051658909)
      ·
        refine ⟨3000773889976526269372091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8002063706604070051658909 3000773889976526269372091)
        ·
          refine ⟨4501160834964789404058137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3000773889976526269372091 4501160834964789404058137)
          ·
            refine ⟨3375870626223592053043603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4501160834964789404058137 3375870626223592053043603)
            ·
              refine ⟨5063805939335388079565405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375870626223592053043603 5063805939335388079565405)
              ·
                refine ⟨1898927227250770529837027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5063805939335388079565405 1898927227250770529837027)
                ·
                  refine ⟨2848390840876155794755541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898927227250770529837027 2848390840876155794755541)
                  ·
                    refine ⟨66759160333034901439583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2848390840876155794755541 66759160333034901439583)
                    ·
                      rfl

theorem cell23_390039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_390039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390039 prefixEnd_390039 := by exact prefixLift 390039
  have htrace : WordTrace (prefixWord ++ tailWord_390039) baseStart_390039 baseEnd_390039 := by
    simpa [prefixWord, tailWord_390039, baseEnd_390039] using wordTrace_append hprefix tailTrace_390039
  have hstable : (prefixWord ++ tailWord_390039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390039).length < 2 ^ (prefixWord ++ tailWord_390039).sum := by decide
  have hdescent : baseEnd_390039 < baseStart_390039 := by decide
  rcases family_descends (prefixWord ++ tailWord_390039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390139 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 7]
def baseStart_390139 : Nat := 118140960795 + 390139 * 2 ^ 59
def prefixEnd_390139 : Nat := 4983230072969 + 3 ^ 40 * 390139 * 2
def baseEnd_390139 : Nat := 200328829064554313068289

theorem tailTrace_390139 : CollatzResearch.WordTrace tailWord_390139 prefixEnd_390139 200328829064554313068289 := by
  unfold tailWord_390139
  simp only [CollatzResearch.WordTrace]
  refine ⟨14229538333600508281589471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9486358889067005521059647 14229538333600508281589471)
  ·
    refine ⟨21344307500400762422384207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14229538333600508281589471 21344307500400762422384207)
    ·
      refine ⟨32016461250601143633576311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21344307500400762422384207 32016461250601143633576311)
      ·
        refine ⟨48024691875901715450364467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32016461250601143633576311 48024691875901715450364467)
        ·
          refine ⟨72037037813852573175546701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48024691875901715450364467 72037037813852573175546701)
          ·
            refine ⟨27013889180194714940830013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72037037813852573175546701 27013889180194714940830013)
            ·
              refine ⟨10130208442573018102811255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27013889180194714940830013 10130208442573018102811255)
              ·
                refine ⟨15195312663859527154216883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10130208442573018102811255 15195312663859527154216883)
                ·
                  refine ⟨22792968995789290731325325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15195312663859527154216883 22792968995789290731325325)
                  ·
                    refine ⟨8547363373420984024246997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22792968995789290731325325 8547363373420984024246997)
                    ·
                      refine ⟨200328829064554313068289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8547363373420984024246997 200328829064554313068289)
                      ·
                        rfl

theorem cell23_390139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_390139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390139 prefixEnd_390139 := by exact prefixLift 390139
  have htrace : WordTrace (prefixWord ++ tailWord_390139) baseStart_390139 baseEnd_390139 := by
    simpa [prefixWord, tailWord_390139, baseEnd_390139] using wordTrace_append hprefix tailTrace_390139
  have hstable : (prefixWord ++ tailWord_390139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390139).length < 2 ^ (prefixWord ++ tailWord_390139).sum := by decide
  have hdescent : baseEnd_390139 < baseStart_390139 := by decide
  rcases family_descends (prefixWord ++ tailWord_390139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390177 : List Nat := [1, 2, 3, 2, 3, 1, 2, 4, 1, 1, 3]
def baseStart_390177 : Nat := 118140960795 + 390177 * 2 ^ 59
def prefixEnd_390177 : Nat := 4983230072969 + 3 ^ 40 * 390177 * 2
def baseEnd_390177 : Nat := 200348341329425164393115

theorem tailTrace_390177 : CollatzResearch.WordTrace tailWord_390177 prefixEnd_390177 200348341329425164393115 := by
  unfold tailWord_390177
  simp only [CollatzResearch.WordTrace]
  refine ⟨14230924307462840771472785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9487282871641893847648523 14230924307462840771472785)
  ·
    refine ⟨10673193230597130578604589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14230924307462840771472785 10673193230597130578604589)
    ·
      refine ⟨4002447461473923966976721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10673193230597130578604589 4002447461473923966976721)
      ·
        refine ⟨3001835596105442975232541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4002447461473923966976721 3001835596105442975232541)
        ·
          refine ⟨1125688348539541115712203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3001835596105442975232541 1125688348539541115712203)
          ·
            refine ⟨1688532522809311673568305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125688348539541115712203 1688532522809311673568305)
            ·
              refine ⟨1266399392106983755176229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1688532522809311673568305 1266399392106983755176229)
              ·
                refine ⟨237449886020059454095543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1266399392106983755176229 237449886020059454095543)
                ·
                  refine ⟨356174829030089181143315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237449886020059454095543 356174829030089181143315)
                  ·
                    refine ⟨534262243545133771714973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 356174829030089181143315 534262243545133771714973)
                    ·
                      refine ⟨200348341329425164393115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 534262243545133771714973 200348341329425164393115)
                      ·
                        rfl

theorem cell23_390177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_390177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390177 prefixEnd_390177 := by exact prefixLift 390177
  have htrace : WordTrace (prefixWord ++ tailWord_390177) baseStart_390177 baseEnd_390177 := by
    simpa [prefixWord, tailWord_390177, baseEnd_390177] using wordTrace_append hprefix tailTrace_390177
  have hstable : (prefixWord ++ tailWord_390177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390177).length < 2 ^ (prefixWord ++ tailWord_390177).sum := by decide
  have hdescent : baseEnd_390177 < baseStart_390177 := by decide
  rcases family_descends (prefixWord ++ tailWord_390177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390200 : List Nat := [2, 1, 2, 1, 5, 2, 2, 2, 1, 1, 4]
def baseStart_390200 : Nat := 118140960795 + 390200 * 2 ^ 59
def prefixEnd_390200 : Nat := 4983230072969 + 3 ^ 40 * 390200 * 2
def baseEnd_390200 : Nat := 200360151384478574405509

theorem tailTrace_390200 : CollatzResearch.WordTrace tailWord_390200 prefixEnd_390200 200360151384478574405509 := by
  unfold tailWord_390200
  simp only [CollatzResearch.WordTrace]
  refine ⟨7115881593189757849780027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9487842124253010466373369 7115881593189757849780027)
  ·
    refine ⟨10673822389784636774670041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7115881593189757849780027 10673822389784636774670041)
    ·
      refine ⟨8005366792338477581002531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10673822389784636774670041 8005366792338477581002531)
      ·
        refine ⟨12008050188507716371503797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8005366792338477581002531 12008050188507716371503797)
        ·
          refine ⟨1125754705172598409828481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12008050188507716371503797 1125754705172598409828481)
          ·
            refine ⟨844316028879448807371361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1125754705172598409828481 844316028879448807371361)
            ·
              refine ⟨633237021659586605528521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844316028879448807371361 633237021659586605528521)
              ·
                refine ⟨474927766244689954146391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633237021659586605528521 474927766244689954146391)
                ·
                  refine ⟨712391649367034931219587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474927766244689954146391 712391649367034931219587)
                  ·
                    refine ⟨1068587474050552396829381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 712391649367034931219587 1068587474050552396829381)
                    ·
                      refine ⟨200360151384478574405509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1068587474050552396829381 200360151384478574405509)
                      ·
                        rfl

theorem cell23_390200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_390200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390200 prefixEnd_390200 := by exact prefixLift 390200
  have htrace : WordTrace (prefixWord ++ tailWord_390200) baseStart_390200 baseEnd_390200 := by
    simpa [prefixWord, tailWord_390200, baseEnd_390200] using wordTrace_append hprefix tailTrace_390200
  have hstable : (prefixWord ++ tailWord_390200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390200).length < 2 ^ (prefixWord ++ tailWord_390200).sum := by decide
  have hdescent : baseEnd_390200 < baseStart_390200 := by decide
  rcases family_descends (prefixWord ++ tailWord_390200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390217 : List Nat := [1, 2, 1, 1, 2, 2, 2, 7, 1, 2, 2]
def baseStart_390217 : Nat := 118140960795 + 390217 * 2 ^ 59
def prefixEnd_390217 : Nat := 4983230072969 + 3 ^ 40 * 390217 * 2
def baseEnd_390217 : Nat := 200368880555605007892931

theorem tailTrace_390217 : CollatzResearch.WordTrace tailWord_390217 prefixEnd_390217 200368880555605007892931 := by
  unfold tailWord_390217
  simp only [CollatzResearch.WordTrace]
  refine ⟨14232383227317927602928905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9488255484878618401952603 14232383227317927602928905)
  ·
    refine ⟨10674287420488445702196679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14232383227317927602928905 10674287420488445702196679)
    ·
      refine ⟨16011431130732668553295019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10674287420488445702196679 16011431130732668553295019)
      ·
        refine ⟨24017146696099002829942529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16011431130732668553295019 24017146696099002829942529)
        ·
          refine ⟨18012860022074252122456897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24017146696099002829942529 18012860022074252122456897)
          ·
            refine ⟨13509645016555689091842673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18012860022074252122456897 13509645016555689091842673)
            ·
              refine ⟨10132233762416766818882005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13509645016555689091842673 10132233762416766818882005)
              ·
                refine ⟨237474228806642972317547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10132233762416766818882005 237474228806642972317547)
                ·
                  refine ⟨356211343209964458476321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237474228806642972317547 356211343209964458476321)
                  ·
                    refine ⟨267158507407473343857241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 356211343209964458476321 267158507407473343857241)
                    ·
                      refine ⟨200368880555605007892931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 267158507407473343857241 200368880555605007892931)
                      ·
                        rfl

theorem cell23_390217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 1, 2, 2].length) (baseStart_390217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390217 prefixEnd_390217 := by exact prefixLift 390217
  have htrace : WordTrace (prefixWord ++ tailWord_390217) baseStart_390217 baseEnd_390217 := by
    simpa [prefixWord, tailWord_390217, baseEnd_390217] using wordTrace_append hprefix tailTrace_390217
  have hstable : (prefixWord ++ tailWord_390217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390217).length < 2 ^ (prefixWord ++ tailWord_390217).sum := by decide
  have hdescent : baseEnd_390217 < baseStart_390217 := by decide
  rcases family_descends (prefixWord ++ tailWord_390217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390243 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 2, 7, 2]
def baseStart_390243 : Nat := 118140960795 + 390243 * 2 ^ 59
def prefixEnd_390243 : Nat := 4983230072969 + 3 ^ 40 * 390243 * 2
def baseEnd_390243 : Nat := 200382231052621906167811

theorem tailTrace_390243 : CollatzResearch.WordTrace tailWord_390243 prefixEnd_390243 200382231052621906167811 := by
  unfold tailWord_390243
  simp only [CollatzResearch.WordTrace]
  refine ⟨14233331525223734043375383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9488887683482489362250255 14233331525223734043375383)
  ·
    refine ⟨21349997287835601065063075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14233331525223734043375383 21349997287835601065063075)
    ·
      refine ⟨32024995931753401597594613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21349997287835601065063075 32024995931753401597594613)
      ·
        refine ⟨3002343368601881399774495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32024995931753401597594613 3002343368601881399774495)
        ·
          refine ⟨4503515052902822099661743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3002343368601881399774495 4503515052902822099661743)
          ·
            refine ⟨6755272579354233149492615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4503515052902822099661743 6755272579354233149492615)
            ·
              refine ⟨10132908869031349724238923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6755272579354233149492615 10132908869031349724238923)
              ·
                refine ⟨15199363303547024586358385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10132908869031349724238923 15199363303547024586358385)
                ·
                  refine ⟨11399522477660268439768789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15199363303547024586358385 11399522477660268439768789)
                  ·
                    refine ⟨267176308070162541557081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11399522477660268439768789 267176308070162541557081)
                    ·
                      refine ⟨200382231052621906167811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 267176308070162541557081 200382231052621906167811)
                      ·
                        rfl

theorem cell23_390243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_390243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390243 prefixEnd_390243 := by exact prefixLift 390243
  have htrace : WordTrace (prefixWord ++ tailWord_390243) baseStart_390243 baseEnd_390243 := by
    simpa [prefixWord, tailWord_390243, baseEnd_390243] using wordTrace_append hprefix tailTrace_390243
  have hstable : (prefixWord ++ tailWord_390243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390243).length < 2 ^ (prefixWord ++ tailWord_390243).sum := by decide
  have hdescent : baseEnd_390243 < baseStart_390243 := by decide
  rcases family_descends (prefixWord ++ tailWord_390243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390343 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 2, 5]
def baseStart_390343 : Nat := 118140960795 + 390343 * 2 ^ 59
def prefixEnd_390343 : Nat := 4983230072969 + 3 ^ 40 * 390343 * 2
def baseEnd_390343 : Nat := 66811193039357171639117

theorem tailTrace_390343 : CollatzResearch.WordTrace tailWord_390343 prefixEnd_390343 66811193039357171639117 := by
  unfold tailWord_390343
  simp only [CollatzResearch.WordTrace]
  refine ⟨14236978824861451122015683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9491319216574300748010455 14236978824861451122015683)
  ·
    refine ⟨21355468237292176683023525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14236978824861451122015683 21355468237292176683023525)
    ·
      refine ⟨4004150294492283128066911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21355468237292176683023525 4004150294492283128066911)
      ·
        refine ⟨6006225441738424692100367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4004150294492283128066911 6006225441738424692100367)
        ·
          refine ⟨9009338162607637038150551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6006225441738424692100367 9009338162607637038150551)
          ·
            refine ⟨13514007243911455557225827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9009338162607637038150551 13514007243911455557225827)
            ·
              refine ⟨20271010865867183335838741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13514007243911455557225827 20271010865867183335838741)
              ·
                refine ⟨950203634337524218867441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20271010865867183335838741 950203634337524218867441)
                ·
                  refine ⟨712652725753143164150581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 950203634337524218867441 712652725753143164150581)
                  ·
                    refine ⟨66811193039357171639117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 712652725753143164150581 66811193039357171639117)
                    ·
                      rfl

theorem cell23_390343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_390343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390343 prefixEnd_390343 := by exact prefixLift 390343
  have htrace : WordTrace (prefixWord ++ tailWord_390343) baseStart_390343 baseEnd_390343 := by
    simpa [prefixWord, tailWord_390343, baseEnd_390343] using wordTrace_append hprefix tailTrace_390343
  have hstable : (prefixWord ++ tailWord_390343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390343).length < 2 ^ (prefixWord ++ tailWord_390343).sum := by decide
  have hdescent : baseEnd_390343 < baseStart_390343 := by decide
  rcases family_descends (prefixWord ++ tailWord_390343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390358 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_390358 : Nat := 118140960795 + 390358 * 2 ^ 59
def prefixEnd_390358 : Nat := 4983230072969 + 3 ^ 40 * 390358 * 2
def baseEnd_390358 : Nat := 200441281327888956229783

theorem tailTrace_390358 : CollatzResearch.WordTrace tailWord_390358 prefixEnd_390358 200441281327888956229783 := by
  unfold tailWord_390358
  simp only [CollatzResearch.WordTrace]
  refine ⟨889845369987944292738233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9491683946538072455874485 889845369987944292738233)
  ·
    refine ⟨667384027490958219553675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 889845369987944292738233 667384027490958219553675)
    ·
      refine ⟨1001076041236437329330513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 667384027490958219553675 1001076041236437329330513)
      ·
        refine ⟨750807030927327996997885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1001076041236437329330513 750807030927327996997885)
        ·
          refine ⟨281552636597747998874207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 750807030927327996997885 281552636597747998874207)
          ·
            refine ⟨422328954896621998311311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281552636597747998874207 422328954896621998311311)
            ·
              refine ⟨633493432344932997466967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422328954896621998311311 633493432344932997466967)
              ·
                refine ⟨950240148517399496200451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633493432344932997466967 950240148517399496200451)
                ·
                  refine ⟨1425360222776099244300677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950240148517399496200451 1425360222776099244300677)
                  ·
                    refine ⟨267255041770518608306377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1425360222776099244300677 267255041770518608306377)
                    ·
                      refine ⟨200441281327888956229783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 267255041770518608306377 200441281327888956229783)
                      ·
                        rfl

theorem cell23_390358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_390358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390358 prefixEnd_390358 := by exact prefixLift 390358
  have htrace : WordTrace (prefixWord ++ tailWord_390358) baseStart_390358 baseEnd_390358 := by
    simpa [prefixWord, tailWord_390358, baseEnd_390358] using wordTrace_append hprefix tailTrace_390358
  have hstable : (prefixWord ++ tailWord_390358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390358).length < 2 ^ (prefixWord ++ tailWord_390358).sum := by decide
  have hdescent : baseEnd_390358 < baseStart_390358 := by decide
  rcases family_descends (prefixWord ++ tailWord_390358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390403 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 8]
def baseStart_390403 : Nat := 118140960795 + 390403 * 2 ^ 59
def prefixEnd_390403 : Nat := 4983230072969 + 3 ^ 40 * 390403 * 2
def baseEnd_390403 : Nat := 22273820884149031129675

theorem tailTrace_390403 : CollatzResearch.WordTrace tailWord_390403 prefixEnd_390403 22273820884149031129675 := by
  unfold tailWord_390403
  simp only [CollatzResearch.WordTrace]
  refine ⟨14239167204644081369199863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9492778136429387579466575 14239167204644081369199863)
  ·
    refine ⟨21358750806966122053799795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14239167204644081369199863 21358750806966122053799795)
    ·
      refine ⟨32038126210449183080699693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21358750806966122053799795 32038126210449183080699693)
      ·
        refine ⟨12014297328918443655262385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32038126210449183080699693 12014297328918443655262385)
        ·
          refine ⟨9010722996688832741446789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12014297328918443655262385 9010722996688832741446789)
          ·
            refine ⟨1689510561879156139021273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9010722996688832741446789 1689510561879156139021273)
            ·
              refine ⟨1267132921409367104265955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1689510561879156139021273 1267132921409367104265955)
              ·
                refine ⟨1900699382114050656398933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1267132921409367104265955 1900699382114050656398933)
                ·
                  refine ⟨22273820884149031129675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1900699382114050656398933 22273820884149031129675)
                  ·
                    rfl

theorem cell23_390403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 8].length) (baseStart_390403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390403 prefixEnd_390403 := by exact prefixLift 390403
  have htrace : WordTrace (prefixWord ++ tailWord_390403) baseStart_390403 baseEnd_390403 := by
    simpa [prefixWord, tailWord_390403, baseEnd_390403] using wordTrace_append hprefix tailTrace_390403
  have hstable : (prefixWord ++ tailWord_390403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390403).length < 2 ^ (prefixWord ++ tailWord_390403).sum := by decide
  have hdescent : baseEnd_390403 < baseStart_390403 := by decide
  rcases family_descends (prefixWord ++ tailWord_390403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390434 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_390434 : Nat := 118140960795 + 390434 * 2 ^ 59
def prefixEnd_390434 : Nat := 4983230072969 + 3 ^ 40 * 390434 * 2
def baseEnd_390434 : Nat := 200480305857630658879433

theorem tailTrace_390434 : CollatzResearch.WordTrace tailWord_390434 prefixEnd_390434 200480305857630658879433 := by
  unfold tailWord_390434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3560074466882943415894589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9493531911687849109052237 3560074466882943415894589)
  ·
    refine ⟨1335027925081103780960471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3560074466882943415894589 1335027925081103780960471)
    ·
      refine ⟨2002541887621655671440707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1335027925081103780960471 2002541887621655671440707)
      ·
        refine ⟨3003812831432483507161061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2002541887621655671440707 3003812831432483507161061)
        ·
          refine ⟨563214905893590657592699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3003812831432483507161061 563214905893590657592699)
          ·
            refine ⟨844822358840385986389049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563214905893590657592699 844822358840385986389049)
            ·
              refine ⟨633616769130289489791787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844822358840385986389049 633616769130289489791787)
              ·
                refine ⟨950425153695434234687681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633616769130289489791787 950425153695434234687681)
                ·
                  refine ⟨712818865271575676015761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 950425153695434234687681 712818865271575676015761)
                  ·
                    refine ⟨534614148953681757011821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 712818865271575676015761 534614148953681757011821)
                    ·
                      refine ⟨200480305857630658879433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 534614148953681757011821 200480305857630658879433)
                      ·
                        rfl

theorem cell23_390434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_390434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390434 prefixEnd_390434 := by exact prefixLift 390434
  have htrace : WordTrace (prefixWord ++ tailWord_390434) baseStart_390434 baseEnd_390434 := by
    simpa [prefixWord, tailWord_390434, baseEnd_390434] using wordTrace_append hprefix tailTrace_390434
  have hstable : (prefixWord ++ tailWord_390434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390434).length < 2 ^ (prefixWord ++ tailWord_390434).sum := by decide
  have hdescent : baseEnd_390434 < baseStart_390434 := by decide
  rcases family_descends (prefixWord ++ tailWord_390434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390464 : List Nat := [2, 1, 1, 2, 2, 1, 5, 4, 1, 1, 3]
def baseStart_390464 : Nat := 118140960795 + 390464 * 2 ^ 59
def prefixEnd_390464 : Nat := 4983230072969 + 3 ^ 40 * 390464 * 2
def baseEnd_390464 : Nat := 200495710277265541504295

theorem tailTrace_390464 : CollatzResearch.WordTrace tailWord_390464 prefixEnd_390464 200495710277265541504295 := by
  unfold tailWord_390464
  simp only [CollatzResearch.WordTrace]
  refine ⟨7120696028711544393585223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9494261371615392524780297 7120696028711544393585223)
  ·
    refine ⟨10681044043067316590377835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7120696028711544393585223 10681044043067316590377835)
    ·
      refine ⟨16021566064600974885566753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10681044043067316590377835 16021566064600974885566753)
      ·
        refine ⟨12016174548450731164175065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16021566064600974885566753 12016174548450731164175065)
        ·
          refine ⟨9012130911338048373131299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12016174548450731164175065 9012130911338048373131299)
          ·
            refine ⟨13518196367007072559696949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9012130911338048373131299 13518196367007072559696949)
            ·
              refine ⟨1267330909406913052471589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13518196367007072559696949 1267330909406913052471589)
              ·
                refine ⟨237624545513796197338423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1267330909406913052471589 237624545513796197338423)
                ·
                  refine ⟨356436818270694296007635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237624545513796197338423 356436818270694296007635)
                  ·
                    refine ⟨534655227406041444011453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 356436818270694296007635 534655227406041444011453)
                    ·
                      refine ⟨200495710277265541504295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 534655227406041444011453 200495710277265541504295)
                      ·
                        rfl

theorem cell23_390464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 1, 1, 3].length) (baseStart_390464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390464 prefixEnd_390464 := by exact prefixLift 390464
  have htrace : WordTrace (prefixWord ++ tailWord_390464) baseStart_390464 baseEnd_390464 := by
    simpa [prefixWord, tailWord_390464, baseEnd_390464] using wordTrace_append hprefix tailTrace_390464
  have hstable : (prefixWord ++ tailWord_390464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390464).length < 2 ^ (prefixWord ++ tailWord_390464).sum := by decide
  have hdescent : baseEnd_390464 < baseStart_390464 := by decide
  rcases family_descends (prefixWord ++ tailWord_390464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390480 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 1, 6]
def baseStart_390480 : Nat := 118140960795 + 390480 * 2 ^ 59
def prefixEnd_390480 : Nat := 4983230072969 + 3 ^ 40 * 390480 * 2
def baseEnd_390480 : Nat := 66834641989245826301407

theorem tailTrace_390480 : CollatzResearch.WordTrace tailWord_390480 prefixEnd_390480 66834641989245826301407 := by
  unfold tailWord_390480
  simp only [CollatzResearch.WordTrace]
  refine ⟨7120987812682561759876447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9494650416910082346501929 7120987812682561759876447)
  ·
    refine ⟨10681481719023842639814671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7120987812682561759876447 10681481719023842639814671)
    ·
      refine ⟨16022222578535763959722007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10681481719023842639814671 16022222578535763959722007)
      ·
        refine ⟨24033333867803645939583011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16022222578535763959722007 24033333867803645939583011)
        ·
          refine ⟨36050000801705468909374517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24033333867803645939583011 36050000801705468909374517)
          ·
            refine ⟨3379687575159887710253861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36050000801705468909374517 3379687575159887710253861)
            ·
              refine ⟨633691420342478945672599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3379687575159887710253861 633691420342478945672599)
              ·
                refine ⟨950537130513718418508899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633691420342478945672599 950537130513718418508899)
                ·
                  refine ⟨1425805695770577627763349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950537130513718418508899 1425805695770577627763349)
                  ·
                    refine ⟨66834641989245826301407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1425805695770577627763349 66834641989245826301407)
                    ·
                      rfl

theorem cell23_390480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 6].length) (baseStart_390480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390480 prefixEnd_390480 := by exact prefixLift 390480
  have htrace : WordTrace (prefixWord ++ tailWord_390480) baseStart_390480 baseEnd_390480 := by
    simpa [prefixWord, tailWord_390480, baseEnd_390480] using wordTrace_append hprefix tailTrace_390480
  have hstable : (prefixWord ++ tailWord_390480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390480).length < 2 ^ (prefixWord ++ tailWord_390480).sum := by decide
  have hdescent : baseEnd_390480 < baseStart_390480 := by decide
  rcases family_descends (prefixWord ++ tailWord_390480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390504 : List Nat := [2, 1, 4, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_390504 : Nat := 118140960795 + 390504 * 2 ^ 59
def prefixEnd_390504 : Nat := 4983230072969 + 3 ^ 40 * 390504 * 2
def baseEnd_390504 : Nat := 200516249503445385004111

theorem tailTrace_390504 : CollatzResearch.WordTrace tailWord_390504 prefixEnd_390504 200516249503445385004111 := by
  unfold tailWord_390504
  simp only [CollatzResearch.WordTrace]
  refine ⟨7121425488639087809313283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9495233984852117079084377 7121425488639087809313283)
  ·
    refine ⟨10682138232958631713969925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7121425488639087809313283 10682138232958631713969925)
    ·
      refine ⟨2002900918679743446369361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10682138232958631713969925 2002900918679743446369361)
      ·
        refine ⟨1502175689009807584777021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2002900918679743446369361 1502175689009807584777021)
        ·
          refine ⟨563315883378677844291383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1502175689009807584777021 563315883378677844291383)
          ·
            refine ⟨844973825068016766437075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563315883378677844291383 844973825068016766437075)
            ·
              refine ⟨1267460737602025149655613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844973825068016766437075 1267460737602025149655613)
              ·
                refine ⟨475297776600759431120855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1267460737602025149655613 475297776600759431120855)
                ·
                  refine ⟨712946664901139146681283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475297776600759431120855 712946664901139146681283)
                  ·
                    refine ⟨1069419997351708720021925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 712946664901139146681283 1069419997351708720021925)
                    ·
                      refine ⟨200516249503445385004111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1069419997351708720021925 200516249503445385004111)
                      ·
                        rfl

theorem cell23_390504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_390504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390504 prefixEnd_390504 := by exact prefixLift 390504
  have htrace : WordTrace (prefixWord ++ tailWord_390504) baseStart_390504 baseEnd_390504 := by
    simpa [prefixWord, tailWord_390504, baseEnd_390504] using wordTrace_append hprefix tailTrace_390504
  have hstable : (prefixWord ++ tailWord_390504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390504).length < 2 ^ (prefixWord ++ tailWord_390504).sum := by decide
  have hdescent : baseEnd_390504 < baseStart_390504 := by decide
  rcases family_descends (prefixWord ++ tailWord_390504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390521 : List Nat := [1, 2, 1, 3, 2, 1, 4, 4, 1, 2, 2]
def baseStart_390521 : Nat := 118140960795 + 390521 * 2 ^ 59
def prefixEnd_390521 : Nat := 4983230072969 + 3 ^ 40 * 390521 * 2
def baseEnd_390521 : Nat := 200524978674571818491533

theorem tailTrace_390521 : CollatzResearch.WordTrace tailWord_390521 prefixEnd_390521 200524978674571818491533 := by
  unfold tailWord_390521
  simp only [CollatzResearch.WordTrace]
  refine ⟨14243471018216587521995417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9495647345477725014663611 14243471018216587521995417)
  ·
    refine ⟨10682603263662440641496563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14243471018216587521995417 10682603263662440641496563)
    ·
      refine ⟨16023904895493660962244845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10682603263662440641496563 16023904895493660962244845)
      ·
        refine ⟨6008964335810122860841817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16023904895493660962244845 6008964335810122860841817)
        ·
          refine ⟨4506723251857592145631363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6008964335810122860841817 4506723251857592145631363)
          ·
            refine ⟨6760084877786388218447045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4506723251857592145631363 6760084877786388218447045)
            ·
              refine ⟨1267515914584947790958821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6760084877786388218447045 1267515914584947790958821)
              ·
                refine ⟨237659233984677710804779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1267515914584947790958821 237659233984677710804779)
                ·
                  refine ⟨356488850977016566207169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237659233984677710804779 356488850977016566207169)
                  ·
                    refine ⟨267366638232762424655377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 356488850977016566207169 267366638232762424655377)
                    ·
                      refine ⟨200524978674571818491533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 267366638232762424655377 200524978674571818491533)
                      ·
                        rfl

theorem cell23_390521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_390521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390521 prefixEnd_390521 := by exact prefixLift 390521
  have htrace : WordTrace (prefixWord ++ tailWord_390521) baseStart_390521 baseEnd_390521 := by
    simpa [prefixWord, tailWord_390521, baseEnd_390521] using wordTrace_append hprefix tailTrace_390521
  have hstable : (prefixWord ++ tailWord_390521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390521).length < 2 ^ (prefixWord ++ tailWord_390521).sum := by decide
  have hdescent : baseEnd_390521 < baseStart_390521 := by decide
  rcases family_descends (prefixWord ++ tailWord_390521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390600 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 9]
def baseStart_390600 : Nat := 118140960795 + 390600 * 2 ^ 59
def prefixEnd_390600 : Nat := 4983230072969 + 3 ^ 40 * 390600 * 2
def baseEnd_390600 : Nat := 22285060405141889933741

theorem tailTrace_390600 : CollatzResearch.WordTrace tailWord_390600 prefixEnd_390600 22285060405141889933741 := by
  unfold tailWord_390600
  simp only [CollatzResearch.WordTrace]
  refine ⟨7123176192465192007060627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9497568256620256009414169 7123176192465192007060627)
  ·
    refine ⟨10684764288697788010590941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7123176192465192007060627 10684764288697788010590941)
    ·
      refine ⟨4006786608261670503971603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10684764288697788010590941 4006786608261670503971603)
      ·
        refine ⟨6010179912392505755957405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4006786608261670503971603 6010179912392505755957405)
        ·
          refine ⟨2253817467147189658484027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6010179912392505755957405 2253817467147189658484027)
          ·
            refine ⟨3380726200720784487726041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253817467147189658484027 3380726200720784487726041)
            ·
              refine ⟨2535544650540588365794531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3380726200720784487726041 2535544650540588365794531)
              ·
                refine ⟨3803316975810882548691797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535544650540588365794531 3803316975810882548691797)
                ·
                  refine ⟨22285060405141889933741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3803316975810882548691797 22285060405141889933741)
                  ·
                    rfl

theorem cell23_390600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 9].length) (baseStart_390600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390600 prefixEnd_390600 := by exact prefixLift 390600
  have htrace : WordTrace (prefixWord ++ tailWord_390600) baseStart_390600 baseEnd_390600 := by
    simpa [prefixWord, tailWord_390600, baseEnd_390600] using wordTrace_append hprefix tailTrace_390600
  have hstable : (prefixWord ++ tailWord_390600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390600).length < 2 ^ (prefixWord ++ tailWord_390600).sum := by decide
  have hdescent : baseEnd_390600 < baseStart_390600 := by decide
  rcases family_descends (prefixWord ++ tailWord_390600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390614 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_390614 : Nat := 118140960795 + 390614 * 2 ^ 59
def prefixEnd_390614 : Nat := 4983230072969 + 3 ^ 40 * 390614 * 2
def baseEnd_390614 : Nat := 200572732375439954628605

theorem tailTrace_390614 : CollatzResearch.WordTrace tailWord_390614 prefixEnd_390614 200572732375439954628605 := by
  unfold tailWord_390614
  simp only [CollatzResearch.WordTrace]
  refine ⟨890428937929979025320681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9497908671253109603420597 890428937929979025320681)
  ·
    refine ⟨667821703447484268990511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 890428937929979025320681 667821703447484268990511)
    ·
      refine ⟨1001732555171226403485767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 667821703447484268990511 1001732555171226403485767)
      ·
        refine ⟨1502598832756839605228651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1001732555171226403485767 1502598832756839605228651)
        ·
          refine ⟨2253898249135259407842977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1502598832756839605228651 2253898249135259407842977)
          ·
            refine ⟨1690423686851444555882233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2253898249135259407842977 1690423686851444555882233)
            ·
              refine ⟨1267817765138583416911675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1690423686851444555882233 1267817765138583416911675)
              ·
                refine ⟨1901726647707875125367513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1267817765138583416911675 1901726647707875125367513)
                ·
                  refine ⟨1426294985780906344025635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1901726647707875125367513 1426294985780906344025635)
                  ·
                    refine ⟨2139442478671359516038453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1426294985780906344025635 2139442478671359516038453)
                    ·
                      refine ⟨200572732375439954628605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2139442478671359516038453 200572732375439954628605)
                      ·
                        rfl

theorem cell23_390614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_390614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390614 prefixEnd_390614 := by exact prefixLift 390614
  have htrace : WordTrace (prefixWord ++ tailWord_390614) baseStart_390614 baseEnd_390614 := by
    simpa [prefixWord, tailWord_390614, baseEnd_390614] using wordTrace_append hprefix tailTrace_390614
  have hstable : (prefixWord ++ tailWord_390614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390614).length < 2 ^ (prefixWord ++ tailWord_390614).sum := by decide
  have hdescent : baseEnd_390614 < baseStart_390614 := by decide
  rcases family_descends (prefixWord ++ tailWord_390614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390684 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_390684 : Nat := 118140960795 + 390684 * 2 ^ 59
def prefixEnd_390684 : Nat := 4983230072969 + 3 ^ 40 * 390684 * 2
def baseEnd_390684 : Nat := 200608676021254680753283

theorem tailTrace_390684 : CollatzResearch.WordTrace tailWord_390684 prefixEnd_390684 200608676021254680753283 := by
  unfold tailWord_390684
  simp only [CollatzResearch.WordTrace]
  refine ⟨7124708058313033180089553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9499610744417377573452737 7124708058313033180089553)
  ·
    refine ⟨5343531043734774885067165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7124708058313033180089553 5343531043734774885067165)
    ·
      refine ⟨2003824141400540581900187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5343531043734774885067165 2003824141400540581900187)
      ·
        refine ⟨3005736212100810872850281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2003824141400540581900187 3005736212100810872850281)
        ·
          refine ⟨2254302159075608154637711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3005736212100810872850281 2254302159075608154637711)
          ·
            refine ⟨3381453238613412231956567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254302159075608154637711 3381453238613412231956567)
            ·
              refine ⟨5072179857920118347934851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3381453238613412231956567 5072179857920118347934851)
              ·
                refine ⟨7608269786880177521902277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5072179857920118347934851 7608269786880177521902277)
                ·
                  refine ⟨1426550585040033285356677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7608269786880177521902277 1426550585040033285356677)
                  ·
                    refine ⟨267478234695006241004377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1426550585040033285356677 267478234695006241004377)
                    ·
                      refine ⟨200608676021254680753283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 267478234695006241004377 200608676021254680753283)
                      ·
                        rfl

theorem cell23_390684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_390684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390684 prefixEnd_390684 := by exact prefixLift 390684
  have htrace : WordTrace (prefixWord ++ tailWord_390684) baseStart_390684 baseEnd_390684 := by
    simpa [prefixWord, tailWord_390684, baseEnd_390684] using wordTrace_append hprefix tailTrace_390684
  have hstable : (prefixWord ++ tailWord_390684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390684).length < 2 ^ (prefixWord ++ tailWord_390684).sum := by decide
  have hdescent : baseEnd_390684 < baseStart_390684 := by decide
  rcases family_descends (prefixWord ++ tailWord_390684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390767 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 1, 6]
def baseStart_390767 : Nat := 118140960795 + 390767 * 2 ^ 59
def prefixEnd_390767 : Nat := 4983230072969 + 3 ^ 40 * 390767 * 2
def baseEnd_390767 : Nat := 66883764971859285338467

theorem tailTrace_390767 : CollatzResearch.WordTrace tailWord_390767 prefixEnd_390767 66883764971859285338467 := by
  unfold tailWord_390767
  simp only [CollatzResearch.WordTrace]
  refine ⟨14252443375325371535450555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9501628916883581023633703 14252443375325371535450555)
  ·
    refine ⟨21378665062988057303175833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14252443375325371535450555 21378665062988057303175833)
    ·
      refine ⟨16033998797241042977381875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21378665062988057303175833 16033998797241042977381875)
      ·
        refine ⟨24050998195861564466072813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16033998797241042977381875 24050998195861564466072813)
        ·
          refine ⟨9019124323448086674777305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24050998195861564466072813 9019124323448086674777305)
          ·
            refine ⟨6764343242586065006082979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9019124323448086674777305 6764343242586065006082979)
            ·
              refine ⟨10146514863879097509124469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6764343242586065006082979 10146514863879097509124469)
              ·
                refine ⟨951235768488665391480419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10146514863879097509124469 951235768488665391480419)
                ·
                  refine ⟨1426853652732998087220629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951235768488665391480419 1426853652732998087220629)
                  ·
                    refine ⟨66883764971859285338467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1426853652732998087220629 66883764971859285338467)
                    ·
                      rfl

theorem cell23_390767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 6].length) (baseStart_390767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390767 prefixEnd_390767 := by exact prefixLift 390767
  have htrace : WordTrace (prefixWord ++ tailWord_390767) baseStart_390767 baseEnd_390767 := by
    simpa [prefixWord, tailWord_390767, baseEnd_390767] using wordTrace_append hprefix tailTrace_390767
  have hstable : (prefixWord ++ tailWord_390767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390767).length < 2 ^ (prefixWord ++ tailWord_390767).sum := by decide
  have hdescent : baseEnd_390767 < baseStart_390767 := by decide
  rcases family_descends (prefixWord ++ tailWord_390767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390788 : List Nat := [2, 3, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_390788 : Nat := 118140960795 + 390788 * 2 ^ 59
def prefixEnd_390788 : Nat := 4983230072969 + 3 ^ 40 * 390788 * 2
def baseEnd_390788 : Nat := 66887359336440757950935

theorem tailTrace_390788 : CollatzResearch.WordTrace tailWord_390788 prefixEnd_390788 66887359336440757950935 := by
  unfold tailWord_390788
  simp only [CollatzResearch.WordTrace]
  refine ⟨7126604654124646060982509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9502139538832861414643345 7126604654124646060982509)
  ·
    refine ⟨2672476745296742272868441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7126604654124646060982509 2672476745296742272868441)
    ·
      refine ⟨2004357558972556704651331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2672476745296742272868441 2004357558972556704651331)
      ·
        refine ⟨3006536338458835056976997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004357558972556704651331 3006536338458835056976997)
        ·
          refine ⟨563725563461031573183187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3006536338458835056976997 563725563461031573183187)
          ·
            refine ⟨845588345191547359774781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563725563461031573183187 845588345191547359774781)
            ·
              refine ⟨317095629446830259915543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 845588345191547359774781 317095629446830259915543)
              ·
                refine ⟨475643444170245389873315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317095629446830259915543 475643444170245389873315)
                ·
                  refine ⟨713465166255368084809973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475643444170245389873315 713465166255368084809973)
                  ·
                    refine ⟨66887359336440757950935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 713465166255368084809973 66887359336440757950935)
                    ·
                      rfl

theorem cell23_390788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_390788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390788 prefixEnd_390788 := by exact prefixLift 390788
  have htrace : WordTrace (prefixWord ++ tailWord_390788) baseStart_390788 baseEnd_390788 := by
    simpa [prefixWord, tailWord_390788, baseEnd_390788] using wordTrace_append hprefix tailTrace_390788
  have hstable : (prefixWord ++ tailWord_390788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390788).length < 2 ^ (prefixWord ++ tailWord_390788).sum := by decide
  have hdescent : baseEnd_390788 < baseStart_390788 := by decide
  rcases family_descends (prefixWord ++ tailWord_390788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390818 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_390818 : Nat := 118140960795 + 390818 * 2 ^ 59
def prefixEnd_390818 : Nat := 4983230072969 + 3 ^ 40 * 390818 * 2
def baseEnd_390818 : Nat := 66892494142985718825889

theorem tailTrace_390818 : CollatzResearch.WordTrace tailWord_390818 prefixEnd_390818 66892494142985718825889 := by
  unfold tailWord_390818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3563575874535151811389277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9502868998760404830371405 3563575874535151811389277)
  ·
    refine ⟨1336340952950681929270979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3563575874535151811389277 1336340952950681929270979)
    ·
      refine ⟨2004511429426022893906469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1336340952950681929270979 2004511429426022893906469)
      ·
        refine ⟨375845893017379292607463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2004511429426022893906469 375845893017379292607463)
        ·
          refine ⟨563768839526068938911195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375845893017379292607463 563768839526068938911195)
          ·
            refine ⟨845653259289103408366793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563768839526068938911195 845653259289103408366793)
            ·
              refine ⟨634239944466827556275095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 845653259289103408366793 634239944466827556275095)
              ·
                refine ⟨951359916700241334412643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634239944466827556275095 951359916700241334412643)
                ·
                  refine ⟨1427039875050362001618965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951359916700241334412643 1427039875050362001618965)
                  ·
                    refine ⟨66892494142985718825889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1427039875050362001618965 66892494142985718825889)
                    ·
                      rfl

theorem cell23_390818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_390818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390818 prefixEnd_390818 := by exact prefixLift 390818
  have htrace : WordTrace (prefixWord ++ tailWord_390818) baseStart_390818 baseEnd_390818 := by
    simpa [prefixWord, tailWord_390818, baseEnd_390818] using wordTrace_append hprefix tailTrace_390818
  have hstable : (prefixWord ++ tailWord_390818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390818).length < 2 ^ (prefixWord ++ tailWord_390818).sum := by decide
  have hdescent : baseEnd_390818 < baseStart_390818 := by decide
  rcases family_descends (prefixWord ++ tailWord_390818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390838 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_390838 : Nat := 118140960795 + 390838 * 2 ^ 59
def prefixEnd_390838 : Nat := 4983230072969 + 3 ^ 40 * 390838 * 2
def baseEnd_390838 : Nat := 200687752042047078227575

theorem tailTrace_390838 : CollatzResearch.WordTrace tailWord_390838 prefixEnd_390838 200687752042047078227575 := by
  unfold tailWord_390838
  simp only [CollatzResearch.WordTrace]
  refine ⟨890939559879259416330323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9503355305378767107523445 890939559879259416330323)
  ·
    refine ⟨1336409339818889124495485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 890939559879259416330323 1336409339818889124495485)
    ·
      refine ⟨501153502432083421685807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1336409339818889124495485 501153502432083421685807)
      ·
        refine ⟨751730253648125132528711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501153502432083421685807 751730253648125132528711)
        ·
          refine ⟨1127595380472187698793067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751730253648125132528711 1127595380472187698793067)
          ·
            refine ⟨1691393070708281548189601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127595380472187698793067 1691393070708281548189601)
            ·
              refine ⟨1268544803031211161142201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691393070708281548189601 1268544803031211161142201)
              ·
                refine ⟨951408602273408370856651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1268544803031211161142201 951408602273408370856651)
                ·
                  refine ⟨1427112903410112556284977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951408602273408370856651 1427112903410112556284977)
                  ·
                    refine ⟨1070334677557584417213733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1427112903410112556284977 1070334677557584417213733)
                    ·
                      refine ⟨200687752042047078227575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1070334677557584417213733 200687752042047078227575)
                      ·
                        rfl

theorem cell23_390838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_390838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390838 prefixEnd_390838 := by exact prefixLift 390838
  have htrace : WordTrace (prefixWord ++ tailWord_390838) baseStart_390838 baseEnd_390838 := by
    simpa [prefixWord, tailWord_390838, baseEnd_390838] using wordTrace_append hprefix tailTrace_390838
  have hstable : (prefixWord ++ tailWord_390838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390838).length < 2 ^ (prefixWord ++ tailWord_390838).sum := by decide
  have hdescent : baseEnd_390838 < baseStart_390838 := by decide
  rcases family_descends (prefixWord ++ tailWord_390838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390858 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_390858 : Nat := 118140960795 + 390858 * 2 ^ 59
def prefixEnd_390858 : Nat := 4983230072969 + 3 ^ 40 * 390858 * 2
def baseEnd_390858 : Nat := 200698021655136999977483

theorem tailTrace_390858 : CollatzResearch.WordTrace tailWord_390858 prefixEnd_390858 200698021655136999977483 := by
  unfold tailWord_390858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3563940604498923519253307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9503841611997129384675485 3563940604498923519253307)
  ·
    refine ⟨5345910906748385278879961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3563940604498923519253307 5345910906748385278879961)
    ·
      refine ⟨4009433180061288959159971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5345910906748385278879961 4009433180061288959159971)
      ·
        refine ⟨6014149770091933438739957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4009433180061288959159971 6014149770091933438739957)
        ·
          refine ⟨563826540946118759881871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6014149770091933438739957 563826540946118759881871)
          ·
            refine ⟨845739811419178139822807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563826540946118759881871 845739811419178139822807)
            ·
              refine ⟨1268609717128767209734211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845739811419178139822807 1268609717128767209734211)
              ·
                refine ⟨1902914575693150814601317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268609717128767209734211 1902914575693150814601317)
                ·
                  refine ⟨356796482942465777737747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1902914575693150814601317 356796482942465777737747)
                  ·
                    refine ⟨535194724413698666606621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 356796482942465777737747 535194724413698666606621)
                    ·
                      refine ⟨200698021655136999977483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 535194724413698666606621 200698021655136999977483)
                      ·
                        rfl

theorem cell23_390858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_390858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390858 prefixEnd_390858 := by exact prefixLift 390858
  have htrace : WordTrace (prefixWord ++ tailWord_390858) baseStart_390858 baseEnd_390858 := by
    simpa [prefixWord, tailWord_390858, baseEnd_390858] using wordTrace_append hprefix tailTrace_390858
  have hstable : (prefixWord ++ tailWord_390858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390858).length < 2 ^ (prefixWord ++ tailWord_390858).sum := by decide
  have hdescent : baseEnd_390858 < baseStart_390858 := by decide
  rcases family_descends (prefixWord ++ tailWord_390858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390874 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 2, 6]
def baseStart_390874 : Nat := 118140960795 + 390874 * 2 ^ 59
def prefixEnd_390874 : Nat := 4983230072969 + 3 ^ 40 * 390874 * 2
def baseEnd_390874 : Nat := 66902079115202979125803

theorem tailTrace_390874 : CollatzResearch.WordTrace tailWord_390874 prefixEnd_390874 66902079115202979125803 := by
  unfold tailWord_390874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3564086496484432202398919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9504230657291819206397117 3564086496484432202398919)
  ·
    refine ⟨5346129744726648303598379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3564086496484432202398919 5346129744726648303598379)
    ·
      refine ⟨8019194617089972455397569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5346129744726648303598379 8019194617089972455397569)
      ·
        refine ⟨6014395962817479341548177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8019194617089972455397569 6014395962817479341548177)
        ·
          refine ⟨4510796972113109506161133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6014395962817479341548177 4510796972113109506161133)
          ·
            refine ⟨1691548864542416064810425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4510796972113109506161133 1691548864542416064810425)
            ·
              refine ⟨1268661648406812048607819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691548864542416064810425 1268661648406812048607819)
              ·
                refine ⟨1902992472610218072911729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268661648406812048607819 1902992472610218072911729)
                ·
                  refine ⟨1427244354457663554683797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1902992472610218072911729 1427244354457663554683797)
                  ·
                    refine ⟨66902079115202979125803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1427244354457663554683797 66902079115202979125803)
                    ·
                      rfl

theorem cell23_390874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_390874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390874 prefixEnd_390874 := by exact prefixLift 390874
  have htrace : WordTrace (prefixWord ++ tailWord_390874) baseStart_390874 baseEnd_390874 := by
    simpa [prefixWord, tailWord_390874, baseEnd_390874] using wordTrace_append hprefix tailTrace_390874
  have hstable : (prefixWord ++ tailWord_390874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390874).length < 2 ^ (prefixWord ++ tailWord_390874).sum := by decide
  have hdescent : baseEnd_390874 < baseStart_390874 := by decide
  rcases family_descends (prefixWord ++ tailWord_390874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
